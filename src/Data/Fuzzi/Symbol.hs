module Data.Fuzzi.Symbol where

{- HLINT ignore "Use newtype instead of data" -}
{- HLINT ignore "Use camelCase" -}
{- HLINT ignore "Use mapM" -}

import Control.DeepSeq
import Control.Exception
import Control.Lens
import Control.Monad.Except
import Control.Monad.Logger
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Bifunctor
import Data.Coerce
import Data.Foldable
import Data.Fuzzi.Types
import Data.Text (pack)
import Data.Void
import Debug.Trace
import Type.Reflection
import qualified Data.Fuzzi.Distribution as D
import qualified Data.Fuzzi.EDSL as EDSL
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S
import qualified Text.PrettyPrint as TPP
import qualified Z3.Base as Z3

k_FLOAT_TOLERANCE :: Rational
k_FLOAT_TOLERANCE = 1e-4

type ConcreteSampleSymbol = String
type ConcreteCenterSymbol = String
type SymbolicSampleSymbol = String
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

data SymbolicConstraints = SymbolicConstraints {
  _scPathConstraints       :: S.Seq (BoolExpr, Bool)
  , _scCouplingConstraints :: S.Seq BoolExpr
  , _scCostSymbols         :: S.Seq RealExpr
  , _scOpenSymbols         :: S.Seq OpenSymbolTriple
  , _scSourceCode          :: [PP.SomeFuzzi]
  } deriving (Show, Eq, Ord)

data PathConstraintMergeResult = Keep Bool
                               | Drop
                               deriving (Show, Eq, Ord)

data MergingSymbolicConstraints = MergingSymbolicConstraints {
  _mscPathConstraints       :: S.Seq (BoolExpr, PathConstraintMergeResult)
  , _mscCouplingConstraints :: S.Seq BoolExpr
  , _mscCostSymbols         :: S.Seq RealExpr
  , _mscOpenSymbols         :: S.Seq OpenSymbolTriple
  , _mscSourceCode          :: [PP.SomeFuzzi]
  } deriving (Show, Eq, Ord)

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

  Substitute :: SymbolicExpr -> [(String, SymbolicExpr)] -> SymbolicExpr
  deriving (Eq, Ord)

instance Show SymbolicExpr where
  show = pretty

pretty :: SymbolicExpr -> String
pretty = TPP.render . prettySymbolic 0

parensIf :: Bool -> TPP.Doc -> TPP.Doc
parensIf True  = TPP.parens
parensIf False = id

commaSep :: TPP.Doc -> TPP.Doc -> TPP.Doc
commaSep a b = a TPP.<> TPP.comma TPP.<+> b

prettySymbolic :: Int -> SymbolicExpr -> TPP.Doc
prettySymbolic _ (RealVar x) = TPP.text x
prettySymbolic _ (Rat r) = TPP.double (fromRational r)
prettySymbolic _ (JustBool b) = TPP.text (show b)
prettySymbolic currPrec (Add x y) =
  let thisPrec = PP.precedence M.! "+" in
  let thisFixity = PP.fixity M.! "+" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "+"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Sub x y) =
  let thisPrec = PP.precedence M.! "-" in
  let thisFixity = PP.fixity M.! "-" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "-"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Mul x y) =
  let thisPrec = PP.precedence M.! "*" in
  let thisFixity = PP.fixity M.! "*" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "*"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Div x y) =
  let thisPrec = PP.precedence M.! "/" in
  let thisFixity = PP.fixity M.! "/" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "/"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Lt x y) =
  let thisPrec = PP.precedence M.! "<" in
  let thisFixity = PP.fixity M.! "<" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "<"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Le x y) =
  let thisPrec = PP.precedence M.! "<=" in
  let thisFixity = PP.fixity M.! "<=" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "<="
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Gt x y) =
  let thisPrec = PP.precedence M.! ">" in
  let thisFixity = PP.fixity M.! ">" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text ">"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Ge x y) =
  let thisPrec = PP.precedence M.! ">=" in
  let thisFixity = PP.fixity M.! ">=" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text ">="
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Eq_ x y) =
  let thisPrec = PP.precedence M.! "==" in
  let thisFixity = PP.fixity M.! "==" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "=="
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (And x y) =
  let thisPrec = PP.precedence M.! "&&" in
  let thisFixity = PP.fixity M.! "&&" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "&&"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic currPrec (Or x y) =
  let thisPrec = PP.precedence M.! "||" in
  let thisFixity = PP.fixity M.! "||" in
  parensIf (currPrec > thisPrec) $
    prettySymbolic thisPrec x
    TPP.<+> TPP.text "||"
    TPP.<+> prettySymbolic (thisPrec + thisFixity) y
prettySymbolic _ (Not x) =
  TPP.text "not" TPP.<> TPP.parens (prettySymbolic 0 x)
prettySymbolic _ (Ite cond x y) =
  TPP.text "ite" TPP.<> TPP.parens (prettyCond `commaSep`
                                    prettyX    `commaSep`
                                    prettyY)
  where prettyX    = prettySymbolic 0 x
        prettyY    = prettySymbolic 0 y
        prettyCond = prettySymbolic 0 cond
prettySymbolic _ (Substitute x substs) =
  TPP.text "subst" TPP.<> TPP.parens (prettyX `commaSep`
                                      prettySubsts3)
  where prettyX       = prettySymbolic 0 x
        prettySubsts1 = map (first TPP.text . second (prettySymbolic 0)) substs
        prettySubsts2 =
          foldr (\(f,t) acc -> TPP.parens (f `commaSep` t) `commaSep` acc)
                TPP.empty
                prettySubsts1
        prettySubsts3 = TPP.brackets prettySubsts2

class Matchable a b => SEq a b where
  symEq :: a -> b -> BoolExpr

newtype RealExpr = RealExpr { getRealExpr :: SymbolicExpr }
  deriving (Eq, Ord)

instance Show RealExpr where
  show a = show (getRealExpr a)

newtype BoolExpr = BoolExpr { getBoolExpr :: SymbolicExpr }
  deriving (Eq, Ord)

instance Show BoolExpr where
  show a = show (getBoolExpr a)

makeLensesWith abbreviatedFields ''SymbolicState
makeLensesWith abbreviatedFields ''SymbolicConstraints
makeLensesWith abbreviatedFields ''MergingSymbolicConstraints

data SolverResult = Ok      Epsilon --Z3.Model
                  | Failed  [String]
                  | Unknown  String

isOk :: SolverResult -> Bool
isOk (Ok _) = True
isOk _        = False

isFailed :: SolverResult -> Bool
isFailed (Failed _) = True
isFailed _          = False

instance Show SolverResult where
  show (Ok eps)       = "Ok " ++ show eps
  show (Failed cores)   = "Failed " ++ show cores
  show (Unknown reason) = "Unknown " ++ reason

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

z3Init :: (MonadIO m, MonadLogger m) => m (Z3.Context, Z3.Solver)
z3Init = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  liftIO (Z3.setASTPrintMode ctx Z3.Z3_PRINT_SMTLIB2_COMPLIANT)
  solver <- liftIO (Z3.mkSolverForLogic ctx Z3.QF_NRA)
  $(logInfo) "initialized Z3 solver and context"
  return (ctx, solver)

double :: Double -> RealExpr
double = fromRational . toRational

bool :: Bool -> BoolExpr
bool = BoolExpr . JustBool

runSymbolic :: Symbolic Void a -> Either SymExecError a
runSymbolic = runExcept . (`evalStateT` initialSt) . runSymbolicT_
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
  let pcs =
        (toList . fmap (simplify . first (`substituteB` subst)))
        (sc ^. pathConstraints)
  let cpls = (toList . fmap (reduceSubstB . flip substituteB subst)) (sc ^. couplingConstraints)
  let eqCond = reduceSubstB $ substituteB (cr `symEq` sym) subst
  return (pcs, cpls, eqCond)
  where
    simplify (cond, True)  = reduceSubstB cond
    simplify (cond, False) = reduceSubstB $ neg cond

    go _   []                  []                             = return []
    go idx ((cs, cc, ss):syms) (D.TrLaplace cc' _ cs':traces) = do
      ss' <- freshSReal $ "run_" ++ show idx ++ "_lap"
      subst <- go idx syms traces
      return $ (cs,double cs'):(cc,double cc'):(ss,sReal ss'):subst
    go idx ((cs, cc, ss):syms) (D.TrGaussian cc' _ cs':traces) =
      error "not implemented yet..."
    go _    _                  _                               =
      error "impossible: trace and symbol triples have different lengths..."

buildFullConstraints :: (SEq concrete symbolic)
                     => symbolic
                     -> SymbolicConstraints
                     -> Bucket concrete
                     -> Either SymExecError [([PathCondition], [CouplingCondition], EqualityCondition)]
buildFullConstraints sym sc bucket =
  forM (zip bucket [0..]) $ \((cr, traces), idx) ->
    fillConstraintTemplate idx sym sc cr traces

solve_ :: (MonadIO m, MonadLogger m)
       => [([PathCondition], [CouplingCondition], EqualityCondition)]
       -> TotalSymbolicCost
       -> Epsilon
       -> m SolverResult
solve_ conditions symCost eps = do
  (cxt, solver) <- z3Init
  let addToSolver (label, ast) = do
        trackedBoolVar <- liftIO $ Z3.mkFreshBoolVar cxt label
        liftIO (Z3.solverAssertAndTrack cxt solver ast trackedBoolVar)
        --liftIO $ Z3.solverAssertCnstr cxt solver ast
      toZ3 cond = do
        ast <- liftIO $ symbolicExprToZ3AST cxt (getBoolExpr cond)
        let prettyStr = pretty (getBoolExpr cond)
        return (prettyStr, ast)
  $(logInfo) "loading constraints..."
  forM_ conditions $ \(pcs, cpls, eqCond) -> do
    forM_ pcs $ toZ3 >=> addToSolver
    forM_ cpls $ toZ3 >=> addToSolver
    toZ3 eqCond >>= addToSolver
  toZ3 (symCost %<= double eps) >>= addToSolver
  $(logInfo) "checking constraints..."
  r <- liftIO $ Z3.solverCheck cxt solver
  case r of
    Z3.Sat -> do
      $(logInfo) "solver returned sat, retrieving total privacy cost..."
      model <- liftIO $ Z3.solverGetModel cxt solver
      let getCostValue sym = do
            ast <- liftIO $ symbolicExprToZ3AST cxt (getRealExpr sym)
            liftIO $ Z3.evalReal cxt model ast
      cost <- liftIO $ getCostValue symCost
      case cost of
        Just cost' -> do
          costForced <- liftIO $ evaluate (force cost')
          return (Ok (fromRational costForced) )--model)
        Nothing ->
          error "failed to retrieve total privacy cost..."
    Z3.Unsat -> do
      $(logInfo) "solver returned unsat, retrieving unsat core..."
      cores <- liftIO $ Z3.solverGetUnsatCore cxt solver
      strs <- liftIO $ mapM ((liftIO . evaluate . force) <=< (Z3.astToString cxt)) cores
      return (Failed strs)
    Z3.Undef -> do
      $(logInfo) "solver returned undef, retrieving reason..."
      reason <- liftIO $ Z3.solverGetReasonUnknown cxt solver
      return (Unknown reason)

solve :: (MonadIO m, MonadLogger m, SEq concrete symbolic)
      => symbolic
      -> SymbolicConstraints
      -> Bucket concrete
      -> Epsilon
      -> m (Either SymExecError SolverResult)
solve sym sc bucket eps = do
  let totalCostExpr = sum (sc ^. costSymbols)
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
        fromSym <- liftIO $ Z3.mkStringSymbol ctx from
        from' <- liftIO $ Z3.mkRealVar ctx fromSym
        to'   <- symbolicExprToZ3AST ctx to
        return (from', to')
  a'   <- symbolicExprToZ3AST ctx a
  fts' <- mapM f fts
  liftIO (Z3.substitute ctx a' fts')

sReal :: String -> RealExpr
sReal = RealExpr . RealVar

freshSReal :: (Monad m) => String -> SymbolicT r m String
freshSReal name = do
  maybeCounter <- gets (M.lookup name . (^. nameMap))
  case maybeCounter of
    Just c -> do
      modify (\st -> st & nameMap %~ M.insert name (c + 1))
      return (name ++ show c)
    Nothing -> do
      modify (\st -> st & nameMap %~ M.insert name 1)
      return name

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
        abs (sReal concreteSampleSym + sReal shiftSym - sReal lapSym)
        %<= fromRational k_FLOAT_TOLERANCE
  modify (\st -> st & couplingConstraints %~ (S.|> shiftCond))
  let costCond =
        sReal epsSym %>= (abs (c - sReal concreteCenterSym + sReal shiftSym)
                    / (fromRational . toRational $ w))
  modify (\st -> st & couplingConstraints %~ (S.|> costCond))

  modify (\st -> st & costSymbols %~ (S.|> sReal epsSym))
  modify (\st -> st & openSymbols %~ (S.|> (concreteSampleSym, concreteCenterSym, lapSym)))

  let provenance = D.Laplace (D.provenance centerWithProvenance) w
  return (D.WithDistributionProvenance (sReal lapSym) provenance)

gaussianSymbolic :: (Monad m)
                 => D.WithDistributionProvenance RealExpr
                 -> Double
                 -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
gaussianSymbolic _ _ = error "not yet implemented"

substituteB :: BoolExpr -> [(String, RealExpr)] -> BoolExpr
substituteB (BoolExpr a) fts =
  let ftsAst = map (second getRealExpr) fts
  in BoolExpr $ Substitute a ftsAst

substituteR :: RealExpr -> [(String, RealExpr)] -> RealExpr
substituteR (RealExpr a) fts =
  let ftsAst = map (second getRealExpr) fts
  in RealExpr $ Substitute a ftsAst

newtype GSC a =
  GSC {
    getGSC :: Either SymExecError a
  } deriving (Show, Eq, Ord)
    deriving (Functor, Applicative, Monad, MonadError SymExecError)
    via (Either SymExecError)

instance Semigroup (GSC MergingSymbolicConstraints) where
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
          whenMatched = MM.zipWithMatched
            (\_ r1 r2 ->
               case (r1, r2) of
                 (Keep b1, Keep b2) | b1 == b2  -> Keep b1
                                    | otherwise -> Drop
                 (Drop, _) -> Drop
                 (_, Drop) -> Drop)

generalize :: [SymbolicConstraints] -> Either SymExecError SymbolicConstraints
generalize []     = Left (InternalError "generalizing an empty list of constraints?")
generalize (x:xs) =
  fmap dropUselessPcs (getGSC (foldr merge (inject x) xs))
  where
    merge :: SymbolicConstraints
          -> GSC MergingSymbolicConstraints
          -> GSC MergingSymbolicConstraints
    merge a b = inject a <> b

    inject :: SymbolicConstraints -> GSC MergingSymbolicConstraints
    inject sc =
      let pcs = fmap (second Keep) (sc ^. pathConstraints) in
      GSC (Right (MergingSymbolicConstraints
                    pcs
                    (sc ^. couplingConstraints)
                    (sc ^. costSymbols)
                    (sc ^. openSymbols)
                    (sc ^. sourceCode)
                 )
          )

    dropUselessPcs :: MergingSymbolicConstraints -> SymbolicConstraints
    dropUselessPcs sc =
      let cc   = sc ^. couplingConstraints
          cs   = sc ^. costSymbols
          os   = sc ^. openSymbols
          code = sc ^. sourceCode
          pcs  = sc ^. pathConstraints
      in SymbolicConstraints (go pcs) cc cs os code

    go S.Empty                   = S.Empty
    go ((cond, Keep b) S.:<| xs) = (cond, b) S.:<| go xs
    go ((_,    Drop)   S.:<| xs) = go xs

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

reduceSubst :: SymbolicExpr -> SymbolicExpr
reduceSubst e = doSubst e []

reduceSubstB :: BoolExpr -> BoolExpr
reduceSubstB = coerce reduceSubst

doSubst :: SymbolicExpr -> [(String, SymbolicExpr)] -> SymbolicExpr
doSubst (RealVar x) substs =
  case find (\(f, _) -> f == x) substs of
    Nothing -> RealVar x
    Just (_, t) -> t
doSubst e@(Rat _) _ = e
doSubst e@(JustBool _) _ = e
doSubst (Add x y)      substs = Add (doSubst x substs) (doSubst y substs)
doSubst (Sub x y)      substs = Sub (doSubst x substs) (doSubst y substs)
doSubst (Mul x y)      substs = Mul (doSubst x substs) (doSubst y substs)
doSubst (Div x y)      substs = Div (doSubst x substs) (doSubst y substs)
doSubst (Lt x y)       substs = Lt  (doSubst x substs) (doSubst y substs)
doSubst (Le x y)       substs = Le  (doSubst x substs) (doSubst y substs)
doSubst (Gt x y)       substs = Gt  (doSubst x substs) (doSubst y substs)
doSubst (Ge x y)       substs = Ge  (doSubst x substs) (doSubst y substs)
doSubst (Eq_ x y)      substs = Eq_ (doSubst x substs) (doSubst y substs)
doSubst (And x y)      substs = And (doSubst x substs) (doSubst y substs)
doSubst (Or x y)       substs = Or  (doSubst x substs) (doSubst y substs)
doSubst (Not x)        substs = Not (doSubst x substs)
doSubst (Ite cond x y) substs = Ite (doSubst cond substs)
                                    (doSubst x substs)
                                    (doSubst y substs)
doSubst (Substitute x substs) substs' = doSubst x (substs ++ substs')