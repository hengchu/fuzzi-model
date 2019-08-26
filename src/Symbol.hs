module Symbol where

{- HLINT ignore "Use newtype instead of data" -}
{- HLINT ignore "Use camelCase" -}
{- HLINT ignore "Use mapM" -}

import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Bifunctor
import Data.Coerce
import Data.Foldable
import Data.Void
import Debug.Trace
import Type.Reflection
import Types
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S
import qualified Distribution as D
import qualified EDSL as EDSL
import qualified PrettyPrint as PP
import qualified Z3.Base as Z3

k_FLOAT_TOLERANCE :: Rational
k_FLOAT_TOLERANCE = 1e-4

data SymbolicExpr :: * where
  RealVar :: String -> SymbolicExpr

  Rat      :: Rational -> SymbolicExpr
  JustBool :: Bool     -> SymbolicExpr

  Add :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Sub :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Mul :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Div :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Lt  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Le  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Gt  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Ge  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Eq_ :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  And :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Or  :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr
  Not :: SymbolicExpr -> SymbolicExpr

  Ite :: SymbolicExpr -> SymbolicExpr -> SymbolicExpr -> SymbolicExpr

  Substitute :: SymbolicExpr -> [(SymbolicExpr, SymbolicExpr)] -> SymbolicExpr
  deriving (Show, Eq, Ord)

class Matchable a b => SEq a b where
  symEq :: a -> b -> BoolExpr

newtype RealExpr = RealExpr { getRealExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

newtype BoolExpr = BoolExpr { getBoolExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

type ConcreteSampleSymbol = RealExpr
type ConcreteCenterSymbol = RealExpr
type SymbolicSampleSymbol = RealExpr
type OpenSymbolTriple =
  (ConcreteSampleSymbol, ConcreteCenterSymbol, SymbolicSampleSymbol)

type NameMap  = M.Map String Int
type Bucket r = [(r, S.Seq (D.Trace Double))]
data SymbolicState r = SymbolicState {
  _ssNameMap               :: NameMap
  , _ssPathConstraints     :: S.Seq (BoolExpr, Bool)
  , _ssCouplingConstraints :: S.Seq BoolExpr
  , _ssCostSymbols         :: S.Seq RealExpr
  , _ssOpenSymbols         :: S.Seq OpenSymbolTriple
  , _ssBucket              :: Bucket r
  , _ssSourceCode          :: PP.SomeFuzzi
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''SymbolicState

data SymbolicConstraints = SymbolicConstraints {
  _scPathConstraints       :: S.Seq (BoolExpr, Bool)
  , _scCouplingConstraints :: S.Seq BoolExpr
  , _scCostSymbols         :: S.Seq RealExpr
  , _scOpenSymbols         :: S.Seq OpenSymbolTriple
  , _scSourceCode          :: [PP.SomeFuzzi]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''SymbolicConstraints

data SymExecError =
  UnbalancedLaplaceCalls
  | MismatchingNoiseMechanism
  | DifferentLaplaceWidth Double Double
  | ResultDefinitelyNotEqual
  | InternalError String
  deriving (Show, Eq, Ord, Typeable)

initialSymbolicState :: Bucket r -> PP.SomeFuzzi -> SymbolicState r
initialSymbolicState =
  SymbolicState M.empty S.empty S.empty S.empty S.empty

newtype SymbolicT r m a =
  SymbolicT { runSymbolicT_ :: StateT (SymbolicState r) (ExceptT SymExecError m) a }
  deriving (MonadState (SymbolicState r))
  via (StateT (SymbolicState r) (ExceptT SymExecError m))
  deriving (MonadError SymExecError)
  via (StateT (SymbolicState r) (ExceptT SymExecError m))
  deriving (Functor, Applicative, Monad)
  via (StateT (SymbolicState r) (ExceptT SymExecError m))

type Symbolic r a = SymbolicT r Identity a

instance MonadTrans (SymbolicT r) where
  lift = SymbolicT . lift . lift

z3Init :: (MonadIO m) => m (Z3.Context, Z3.Solver)
z3Init = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  solver <- liftIO (Z3.mkSolverForLogic ctx Z3.QF_NRA)
  return (ctx, solver)

double :: Double -> RealExpr
double = fromRational . toRational

bool :: Bool -> BoolExpr
bool = BoolExpr . JustBool

runSymbolic :: Symbolic Void a -> Either SymExecError a
runSymbolic = runExcept . (flip evalStateT initialSt) . runSymbolicT_
  where initialSt =
          SymbolicState
            M.empty
            S.empty
            S.empty
            S.empty
            S.empty
            []
            (PP.MkSomeFuzzi $ EDSL.PrettyPrintVariable @Int "nope")

type PathCondition     = BoolExpr
type CouplingCondition = BoolExpr
type EqualityCondition = BoolExpr
type TotalSymbolicCost = RealExpr
type Epsilon           = Double

fillConstraintTemplate :: (SEq concrete symbolic)
                       => Int
                       -> symbolic
                       -> SymbolicConstraints
                       -> concrete
                       -> S.Seq (D.Trace Double)
                       -> Either SymExecError ([PathCondition], [CouplingCondition], EqualityCondition)
fillConstraintTemplate idx sym sc cr traces = runSymbolic $ do
  subst <- go idx (toList $ sc ^. openSymbols) (toList traces)
  let pcs = (toList . fmap (simplify . (first $ flip substituteB subst))) (sc ^. pathConstraints)
  let cpls = (toList . fmap (flip substituteB subst)) (sc ^. couplingConstraints)
  let sc' = sc & pathConstraints     %~ (fmap (first $ flip substituteB subst))
               & couplingConstraints %~ (fmap (flip substituteB subst))
  let eqCond = substituteB (cr `symEq` sym) subst
  return (pcs, cpls, eqCond)
  where
    simplify (cond, True)  = cond
    simplify (cond, False) = neg cond

    go idx []                  []                             = return []
    go idx ((cs, cc, ss):syms) (D.TrLaplace cc' _ cs':traces) = do
      ss' <- freshSReal $ "run_" ++ show idx ++ "_lap"
      subst <- go idx syms traces
      return $ (cs,double cs'):(cc,double cc'):(ss,ss'):subst

buildFullConstraints :: (SEq concrete symbolic)
                     => symbolic
                     -> SymbolicConstraints
                     -> Bucket concrete
                     -> Either SymExecError [( [PathCondition]
                                             , [CouplingCondition]
                                             , EqualityCondition)
                                            ]
buildFullConstraints sym sc bucket =
  forM (zip bucket [0..]) $ \((cr, traces), idx) ->
    fillConstraintTemplate idx sym sc cr traces

solve_ :: [( [PathCondition]
           , [CouplingCondition]
           , EqualityCondition)
          ]
       -> TotalSymbolicCost
       -> Epsilon
       -> IO Z3.Result
solve_ conditions symCost eps = do
  (cxt, solver) <- z3Init
  let addToSolver = Z3.solverAssertCnstr cxt solver
      toZ3        = symbolicExprToZ3AST cxt . getBoolExpr
  forM_ conditions $ \(pcs, cpls, eqCond) -> do
    forM_ pcs $ \pc -> (toZ3 pc) >>= addToSolver
    forM_ cpls $ \cpl -> (toZ3 cpl) >>= addToSolver
  toZ3 (symCost %<= double eps) >>= addToSolver
  Z3.solverCheck cxt solver

solve :: (SEq concrete symbolic)
      => symbolic
      -> SymbolicConstraints
      -> Bucket concrete
      -> Epsilon
      -> IO (Either SymExecError Z3.Result)
solve sym sc bucket eps = do
  let totalCostExpr = foldr (+) (double 0) (sc ^. costSymbols)
  case buildFullConstraints sym sc bucket of
    Left err -> return (Left err)
    Right conds -> do
      r <- solve_ conds totalCostExpr eps
      return (Right r)

gatherConstraints :: ( Monad m
                     , Matchable r a
                     )
                  => Bucket r
                  -> PP.SomeFuzzi
                  -> SymbolicT r m a
                  -> m (Either SymExecError (a, SymbolicConstraints))
gatherConstraints bucket code computation = do
  errorOrA :: (Either SymExecError (a, SymbolicState r)) <- run computation
  case errorOrA of
    Left err -> return (Left err)
    Right (a, st) ->
      let pc    = st ^. pathConstraints
          cc    = st ^. couplingConstraints
          csyms = st ^. costSymbols
          osyms = st ^. openSymbols
          code' = st ^. sourceCode
      in
        if any (\r -> not $ match r a) (map fst bucket)
        then
          return (Left ResultDefinitelyNotEqual)
        else
          return (Right (a, SymbolicConstraints pc cc csyms osyms [code']))
  where run =
          runExceptT
          . flip runStateT (initialSymbolicState bucket code)
          . runSymbolicT_

symbolicExprToZ3AST :: (MonadIO m) => Z3.Context -> SymbolicExpr -> m Z3.AST
symbolicExprToZ3AST ctx (RealVar name) = do
  sym <- liftIO (Z3.mkStringSymbol ctx name)
  liftIO (Z3.mkRealVar ctx sym)
symbolicExprToZ3AST ctx (Rat v) =
  liftIO (Z3.mkRational ctx v)
symbolicExprToZ3AST ctx (JustBool v) =
  liftIO (Z3.mkBool ctx v)
symbolicExprToZ3AST ctx (Add a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkAdd ctx [a', b'])
symbolicExprToZ3AST ctx (Sub a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkSub ctx [a', b'])
symbolicExprToZ3AST ctx (Mul a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkMul ctx [a', b'])
symbolicExprToZ3AST ctx (Div a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkDiv ctx a' b')
symbolicExprToZ3AST ctx (Lt a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkLt ctx a' b')
symbolicExprToZ3AST ctx (Le a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkLe ctx a' b')
symbolicExprToZ3AST ctx (Gt a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkGt ctx a' b')
symbolicExprToZ3AST ctx (Ge a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkGe ctx a' b')
symbolicExprToZ3AST ctx (Eq_ a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkEq ctx a' b')
symbolicExprToZ3AST ctx (And a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkAnd ctx [a', b'])
symbolicExprToZ3AST ctx (Or a b) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  liftIO (Z3.mkOr ctx [a', b'])
symbolicExprToZ3AST ctx (Not a) = do
  a' <- symbolicExprToZ3AST ctx a
  liftIO (Z3.mkNot ctx a')
symbolicExprToZ3AST ctx (Ite a b c) = do
  a' <- symbolicExprToZ3AST ctx a
  b' <- symbolicExprToZ3AST ctx b
  c' <- symbolicExprToZ3AST ctx c
  liftIO (Z3.mkIte ctx a' b' c')
symbolicExprToZ3AST ctx (Substitute a fts) = do
  let f (from, to) = do
        from' <- symbolicExprToZ3AST ctx from
        to'   <- symbolicExprToZ3AST ctx to
        return (from', to')
  a'   <- symbolicExprToZ3AST ctx a
  fts' <- mapM f fts
  liftIO (Z3.substitute ctx a' fts')

sReal :: String -> RealExpr
sReal = RealExpr . RealVar

freshSReal :: (Monad m) => String -> SymbolicT r m RealExpr
freshSReal name = do
  maybeCounter <- gets (M.lookup name . (^. nameMap))
  case maybeCounter of
    Just c -> do
      modify (\st -> st & nameMap %~ M.insert name (c + 1))
      return (sReal $ name ++ show c)
    Nothing -> do
      modify (\st -> st & nameMap %~ M.insert name 1)
      return (sReal name)

data PopTraceItem r =
  PopTraceItem {
    popped :: D.Trace Double
    , rest :: (r, S.Seq (D.Trace Double))
  }

type PopTraceAcc r = Either SymExecError [PopTraceItem r]

bucketEntryToPopTraceAcc :: r -> S.Seq (D.Trace Double) -> PopTraceAcc r
bucketEntryToPopTraceAcc _ S.Empty      = Left UnbalancedLaplaceCalls
bucketEntryToPopTraceAcc r (x S.:<| xs) = Right [PopTraceItem x (r, xs)]

instance Monoid (PopTraceAcc r) where
  mempty = Right []
  mappend (Left e) _ = Left e
  mappend _ (Left e) = Left e
  mappend (Right xs) (Right ys) = Right (xs ++ ys)

popTraces :: (Monad m) => SymbolicT r m [D.Trace Double]
popTraces = do
  bkt <- gets (^. bucket)
  let remaining = foldMap (uncurry bucketEntryToPopTraceAcc) bkt
  case remaining of
    Left err -> throwError err
    Right remaining' -> do
      modify (\st -> st & bucket .~ rebuild remaining')
      return (map popped remaining')
  where rebuild = map rest

laplaceSymbolic :: (Monad m)
                => D.WithDistributionProvenance RealExpr
                -> Double
                -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
laplaceSymbolic centerWithProvenance w = do
  let c = D.value centerWithProvenance
  lapSym <- freshSReal "lap"
  matchedTraces <- popTraces
  -- Check the width of matching calls
  forM_ matchedTraces $
    \case
      D.TrLaplace _ width _ ->
        when (width /= w) $
          throwError (DifferentLaplaceWidth width w)
      D.TrGaussian{} ->
        throwError MismatchingNoiseMechanism

  concreteSampleSym <- freshSReal "concreteLap"
  concreteCenterSym <- freshSReal "concreteCenter"

  epsSym   <- freshSReal "eps"
  shiftSym <- freshSReal "shift"

  let shiftCond =
        abs (concreteSampleSym + shiftSym - lapSym)
        %<= fromRational k_FLOAT_TOLERANCE
  modify (\st -> st & couplingConstraints %~ (S.|> shiftCond))
  let costCond =
        epsSym %>= (abs (c - concreteCenterSym + shiftSym)
                    / (fromRational . toRational $ w))
  modify (\st -> st & couplingConstraints %~ (S.|> costCond))

  modify (\st -> st & costSymbols %~ (S.|> epsSym))
  modify (\st -> st & openSymbols %~ (S.|> (concreteSampleSym, concreteCenterSym, lapSym)))

  let provenance = D.Laplace (D.provenance centerWithProvenance) w
  return (D.WithDistributionProvenance lapSym provenance)

gaussianSymbolic :: (Monad m)
                 => D.WithDistributionProvenance RealExpr
                 -> Double
                 -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
gaussianSymbolic _ _ = error "not yet implemented"

substituteB :: BoolExpr -> [(RealExpr, RealExpr)] -> BoolExpr
substituteB (BoolExpr a) fts =
  let ftsAst = map (\(f, t) -> (getRealExpr f, getRealExpr t)) fts
  in BoolExpr $ Substitute a ftsAst

substituteR :: RealExpr -> [(RealExpr, RealExpr)] -> RealExpr
substituteR (RealExpr a) fts =
  let ftsAst = map (\(f, t) -> (getRealExpr f, getRealExpr t)) fts
  in RealExpr $ Substitute a ftsAst

newtype GSC a =
  GSC {
    getGSC :: Either SymExecError a
  } deriving (Show, Eq, Ord)
    deriving (Functor, Applicative, Monad, MonadError SymExecError)
    via (Either SymExecError)

instance Semigroup (GSC SymbolicConstraints) where
  (GSC (Left e)) <> _ = GSC (Left e)
  _ <> (GSC (Left e)) = GSC (Left e)
  (GSC (Right sc1)) <> (GSC (Right sc2)) = do
    let sc1CC = sc1 ^. couplingConstraints
    let sc2CC = sc2 ^. couplingConstraints
    when (sc1CC /= sc2CC) $
      throwError (InternalError $
                    "coupling constraints mismatch:\n"
                    ++ show sc1CC
                    ++ "\n"
                    ++ show sc2CC)
    let sc1CSyms = sc1 ^. costSymbols
    let sc2CSyms = sc2 ^. costSymbols
    when (sc1CSyms /= sc2CSyms) $
      throwError (InternalError $
                    "cost symbols mismatch:\n"
                    ++ show sc1CSyms
                    ++ "\n"
                    ++ show sc2CSyms)
    let sc1Syms = sc1 ^. openSymbols
    let sc2Syms = sc2 ^. openSymbols
    when (sc1Syms /= sc2Syms) $
      throwError (InternalError $
                    "open symbols mismatch:\n"
                    ++ show sc1Syms
                    ++ "\n"
                    ++ show sc2Syms)
    let sc1PCs = (M.fromList . toList) (sc1 ^. pathConstraints)
    let sc2PCs = (M.fromList . toList) (sc2 ^. pathConstraints)
    merged <- MM.mergeA whenMissing whenMissing whenMatched sc1PCs sc2PCs
    return (sc1 & pathConstraints .~ (S.fromList . M.toList) merged
                & sourceCode .~ (sc1 ^. sourceCode ++ sc2 ^. sourceCode))
    where whenMissing = MM.preserveMissing
          whenMatched = MM.zipWithMaybeMatched
            (\_ b1 b2 ->
               if b1 == b2
               then Just b1
               else Nothing)

generalize :: [SymbolicConstraints] -> Either SymExecError SymbolicConstraints
generalize []     = Left (InternalError "generalizing an empty list of constraints?")
generalize (x:xs) =
  getGSC (foldr merge (inject x) xs)
  where
    merge :: SymbolicConstraints -> GSC SymbolicConstraints -> GSC SymbolicConstraints
    merge a b = inject a <> b
    inject    = GSC . Right

instance Num RealExpr where
  (+) = coerce Add
  (-) = coerce Sub
  (*) = coerce Mul
  abs (RealExpr ast) =
    let geZero = ast `Ge` Rat 0
        negAst = Rat 0 `Sub` ast
    in RealExpr $ Ite geZero ast negAst
  signum (RealExpr ast) =
    let eqZero = ast `Eq_` Rat 0
        gtZero = ast `Gt` Rat 0
    in RealExpr $ Ite eqZero (Rat 0) (Ite gtZero (Rat 1) (Rat (-1)))
  fromInteger v = RealExpr $ Rat (fromInteger v)

instance Fractional RealExpr where
  (/) = coerce Div
  fromRational = RealExpr . Rat

instance Boolean BoolExpr where
  and = coerce And
  or  = coerce Or
  neg = coerce Not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr

  (%<)  = coerce Lt
  (%<=) = coerce Le
  (%>)  = coerce Gt
  (%>=) = coerce Ge
  (%==) = coerce Eq_
  a %/= b = neg (a %== b)

instance Numeric     RealExpr
instance FracNumeric RealExpr
instance FuzziType   RealExpr
instance FuzziType   BoolExpr

instance (Monad m, Typeable m, Typeable r)
  => MonadDist (SymbolicT r m) where
  type NumDomain (SymbolicT r m) = D.WithDistributionProvenance RealExpr
  laplace  = laplaceSymbolic
  gaussian = gaussianSymbolic

instance (Monad m, Typeable m, Typeable r)
  => MonadAssert (SymbolicT r m) where
  type BoolType (SymbolicT r m) = BoolExpr
  assertTrue  cond =
    modify (\st -> st & pathConstraints %~ (S.|> (cond, True)))
  assertFalse cond =
    modify (\st -> st & pathConstraints %~ (S.|> (cond, False)))

instance Matchable Double RealExpr where
  match _ _ = True

instance (Eq a, Matchable a a) => SEq a a where
  symEq a b = (BoolExpr . JustBool) (a == b)

instance SEq Double RealExpr where
  symEq a b =
    BoolExpr (Eq_ (getRealExpr . fromRational . toRational $ a) (getRealExpr b))

instance (SEq a b, SEq c d) => SEq (a, c) (b, d) where
  symEq (a, c) (b, d) =
    BoolExpr (And (getBoolExpr (a `symEq` b)) (getBoolExpr (c `symEq` d)))

instance SEq a b => SEq [a] [b] where
  symEq [] []         = BoolExpr (JustBool True)
  symEq (x:xs) (y:ys) =
    BoolExpr $
    And (getBoolExpr (x `symEq` y))
        (getBoolExpr (xs `symEq` ys))
  symEq _      _      = BoolExpr (JustBool False)
