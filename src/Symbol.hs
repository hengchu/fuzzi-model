module Symbol where

{- HLINT ignore "Use newtype instead of data" -}
{- HLINT ignore "Use camelCase" -}
{- HLINT ignore "Use mapM" -}

import Control.Lens
import Control.Monad.Except
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Coerce
import Data.Foldable
import Type.Reflection
import Types
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S
import qualified Distribution as D
import qualified Z3.Base as Z3

k_FLOAT_TOLERANCE :: Rational
k_FLOAT_TOLERANCE = 1e-4

data SymbolicExpr :: * where
  RealVar :: String -> SymbolicExpr

  Rat :: Rational     -> SymbolicExpr

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

newtype RealExpr = RealExpr { getRealExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

newtype BoolExpr = BoolExpr { getBoolExpr :: SymbolicExpr }
  deriving (Show, Eq, Ord)

type ConcreteSampleSymbol = RealExpr
type ConcreteCenterSymbol = RealExpr
type SymbolicSampleSymbol = RealExpr
type OpenSymbolTriple =
  (ConcreteSampleSymbol, ConcreteCenterSymbol, SymbolicSampleSymbol)

type NameMap = M.Map String Int
data SymbolicState r = SymbolicState {
  _ssNameMap               :: NameMap
  , _ssPathConstraints     :: S.Seq (BoolExpr, Bool)
  , _ssCouplingConstraints :: S.Seq BoolExpr
  , _ssCostSymbols         :: S.Seq RealExpr
  , _ssOpenSymbols         :: S.Seq OpenSymbolTriple
  , _ssBuckets             :: D.Buckets r
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''SymbolicState

data SymbolicConstraints = SymbolicConstraints {
  _scPathConstraints     :: S.Seq (BoolExpr, Bool)
  , _scCouplingConstraints :: S.Seq BoolExpr
  , _scCostSymbols         :: S.Seq RealExpr
  , _scOpenSymbols         :: S.Seq OpenSymbolTriple
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''SymbolicConstraints

data SymExecError =
  UnbalancedLaplaceCalls
  | MismatchingNoiseMechanism
  | DifferentLaplaceWidth Double Double
  | ResultDefinitelyNotEqual
  | InternalError String
  deriving (Show, Eq, Ord, Typeable)

initialSymbolicState :: D.Buckets r -> SymbolicState r
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

instance MonadTrans (SymbolicT r) where
  lift = SymbolicT . lift . lift

z3Init :: (MonadIO m) => m (Z3.Context, Z3.Solver)
z3Init = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  solver <- liftIO (Z3.mkSolverForLogic ctx Z3.QF_NRA)
  return (ctx, solver)

gatherConstraints :: (Monad m)
                  => D.Buckets r
                  -> SymbolicT r m a
                  -> m (Either SymExecError (a, SymbolicConstraints))
gatherConstraints buckets computation = do
  errorOrA :: (Either SymExecError (a, SymbolicState r)) <- run computation
  case errorOrA of
    Left err -> return (Left err)
    Right (a, st) ->
      let pc = st ^. pathConstraints
          cc = st ^. couplingConstraints
          csyms = st ^. costSymbols
          osyms = st ^. openSymbols
      in return (Right (a, SymbolicConstraints pc cc csyms osyms))
  where run =
          runExceptT
          . flip runStateT (initialSymbolicState buckets)
          . runSymbolicT_

symbolicExprToZ3AST :: (MonadIO m) => Z3.Context -> SymbolicExpr -> m Z3.AST
symbolicExprToZ3AST ctx (RealVar name) = do
  sym <- liftIO (Z3.mkStringSymbol ctx name)
  liftIO (Z3.mkRealVar ctx sym)
symbolicExprToZ3AST ctx (Rat v) =
  liftIO (Z3.mkRational ctx v)
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
      modify (\st -> st & nameMap %~ M.adjust (+1) name)
      return (sReal $ name ++ show c)
    Nothing -> do
      modify (\st -> st & nameMap %~ M.insert name 1)
      return (sReal name)

data PopTraceItem r =
  PopTraceItem {
    key      :: D.DistributionProvenance r
    , popped :: [D.Trace Double]
    , rest   :: [(r, S.Seq (D.Trace Double))]
    }

type PopTraceAcc r = Either SymExecError [PopTraceItem r]

bucketEntryToPopTraceAcc :: (Show r)
                         => D.DistributionProvenance r
                         -> [(r, S.Seq (D.Trace Double))]
                         -> PopTraceAcc r
bucketEntryToPopTraceAcc k [] =
  Left (InternalError $ "found provenance " ++ show k ++ " with no trace")
bucketEntryToPopTraceAcc k resultsAndTraces =
  let results     = map fst resultsAndTraces
      traces      = map snd resultsAndTraces
      headAndRest = sequence (map split traces)
      heads       = fmap (map fst) headAndRest
      rests       = fmap (zip results . map snd) headAndRest
  in (:[]) `fmap` (PopTraceItem <$> pure k <*> heads <*> rests)
  where split :: S.Seq (D.Trace Double)
              -> Either SymExecError (D.Trace Double, S.Seq (D.Trace Double))
        split xs =
          case xs of
            x S.:<| xs -> Right (x, xs)
            S.Empty    -> Left UnbalancedLaplaceCalls

instance Monoid (PopTraceAcc r) where
  mempty = Right []
  mappend (Left e) _ = Left e
  mappend _ (Left e) = Left e
  mappend (Right xs) (Right ys) = Right (xs ++ ys)

popTraces :: forall m r. (Monad m, Ord r, Show r) => SymbolicT r m [D.Trace Double]
popTraces = do
  bkts <- gets (^. buckets)
  let remaining = fold (M.mapWithKey bucketEntryToPopTraceAcc bkts)
  case remaining of
    Left err -> throwError err
    Right remaining' -> do
      modify (\st -> st & buckets .~ rebuild remaining')
      return (concatMap popped remaining')
  where rebuild :: [PopTraceItem r] -> D.Buckets r
        rebuild accs = M.fromList (map (\acc -> (key acc, rest acc)) accs)

laplaceSymbolic :: (Monad m, Ord r, Show r)
                => RealExpr -> Double -> SymbolicT r m RealExpr
laplaceSymbolic c w = do
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

  return lapSym

gaussianSymbolic :: (Monad m) => RealExpr -> Double -> SymbolicT r m RealExpr
gaussianSymbolic _ _ = freshSReal "gauss"

substituteB :: BoolExpr -> [(RealExpr, RealExpr)] -> BoolExpr
substituteB (BoolExpr a) fts =
  let ftsAst = map (\(f, t) -> (getRealExpr f, getRealExpr t)) fts
  in BoolExpr $ Substitute a ftsAst

substituteR :: RealExpr -> [(RealExpr, RealExpr)] -> RealExpr
substituteR (RealExpr a) fts =
  let ftsAst = map (\(f, t) -> (getRealExpr f, getRealExpr t)) fts
  in RealExpr $ Substitute a ftsAst

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

  (%<) = coerce Lt
  (%<=) = coerce Le
  (%>) = coerce Gt
  (%>=) = coerce Ge
  (%==) = coerce Eq_
  a %/= b = neg (a %== b)

instance Numeric     RealExpr
instance FracNumeric RealExpr

instance (Monad m, Typeable m, Typeable r, Ord r, Show r)
  => MonadDist (SymbolicT r m) where
  type NumDomain (SymbolicT r m) = RealExpr
  laplace  = laplaceSymbolic
  gaussian = gaussianSymbolic

instance (Monad m, Typeable m, Typeable r)
  => MonadAssert (SymbolicT r m) where
  type BoolType (SymbolicT r m) = BoolExpr
  assertTrue  cond =
    modify (\st -> st & pathConstraints %~ (S.|> (cond, True)))
  assertFalse cond =
    modify (\st -> st & pathConstraints %~ (S.|> (cond, False)))
