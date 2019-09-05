module Data.Fuzzi.Symbol where

{- HLINT ignore "Use newtype instead of data" -}
{- HLINT ignore "Use camelCase" -}
{- HLINT ignore "Use mapM" -}

import Control.DeepSeq
import Control.Exception
import Control.Lens
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.Logger
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Bifunctor
import Data.Coerce
import Data.Foldable
import Data.Fuzzi.Interp
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

{-
deriving instance Show (D.DropProvenance r) => Show (SymbolicState r)
deriving instance Eq   (D.DropProvenance r) => Eq   (SymbolicState r)
deriving instance Ord  (D.DropProvenance r) => Ord  (SymbolicState r)
-}

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

prettySymbolic :: Int -> SymbolicExpr -> TPP.Doc
prettySymbolic _ (RealVar x) = TPP.text x
prettySymbolic _ (Rat r) = TPP.text (show r) --TPP.double (fromRational r)
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
prettySymbolic _ (Ite (e1 `Ge` (Rat 0)) e2 (Rat 0 `Sub` e3)) -- an optimization for our encoding of absolute values
  | e1 == e2 && e2 == e3 =
    TPP.text "abs" TPP.<> TPP.parens (prettyExpr)
  where prettyExpr = prettySymbolic 0 e1
prettySymbolic _ (Ite cond x y) =
  TPP.text "ite" TPP.<> TPP.parens (prettyCond `PP.commaSep`
                                    prettyX    `PP.commaSep`
                                    prettyY)
  where prettyX    = prettySymbolic 0 x
        prettyY    = prettySymbolic 0 y
        prettyCond = prettySymbolic 0 cond
prettySymbolic _ (Substitute x substs) =
  TPP.text "subst" TPP.<> TPP.parens (prettyX `PP.commaSep`
                                      prettySubsts3)
  where prettyX       = prettySymbolic 0 x
        prettySubsts1 = map (first TPP.text . second (prettySymbolic 0)) substs
        prettySubsts2 =
          foldr (\(f,t) acc -> TPP.parens (f `PP.commaSep` t) `PP.commaSep` acc)
                TPP.empty
                prettySubsts1
        prettySubsts3 = TPP.brackets prettySubsts2

class Matchable a b => SEq a b where
  symEq :: a -> b -> BoolExpr

data RealExpr = RealExpr { getTolerance :: Rational
                         , getRealExpr :: SymbolicExpr
                         }
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

type Epsilon           = Double

data SolverResult = Ok           Epsilon
                  | FailedEps    Epsilon Epsilon -- ^expected epsilon and actual minimized epsilon
                  | FailedUnSat  [String]
                  | Unknown      String
                  deriving (Show, Eq, Ord)

data TestResult c s = TestResult {
  _trSolverResult     :: SolverResult
  , _trSymbolicValue  :: s
  , _trConcreteValues :: [c]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''TestResult

isOk :: HasSolverResult r SolverResult => r -> Bool
isOk (view solverResult -> Ok _) = True
isOk _                           = False

isFailed :: HasSolverResult r SolverResult => r -> Bool
isFailed (view solverResult -> FailedEps _ _) = True
isFailed (view solverResult -> FailedUnSat _) = True
isFailed _                                    = False

type PathConstraints = S.Seq (BoolExpr, Bool)

data SymExecError =
  UnbalancedLaplaceCalls
  | MismatchingNoiseMechanism
  | DifferentLaplaceWidth Double Double
  | ResultDefinitelyNotEqual
  | AssertImpossible BoolExpr Bool
  | ComputationAborted AbortException
  | AbsurdConstraints [String] -- ^ the unsat core
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

z3InitOpt :: (MonadIO m, MonadLogger m) => m (Z3.Context, Z3.Optimizer)
z3InitOpt = do
  cfg <- liftIO Z3.mkConfig
  ctx <- liftIO (Z3.mkContext cfg)
  liftIO (Z3.setASTPrintMode ctx Z3.Z3_PRINT_SMTLIB2_COMPLIANT)
  optimizer <- liftIO (Z3.mkOptimizer ctx)
  $(logInfo) "initialized Z3 optimizer and context"
  return (ctx, optimizer)

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

fillConstraintTemplate :: ( D.HasProvenance concrete
                          , D.HasProvenance symbolic
                          , Show concrete
                          , Show symbolic
                          , Show (D.DropProvenance concrete)
                          , Show (D.DropProvenance symbolic)
                          , SEq (D.DropProvenance concrete) (D.DropProvenance symbolic))
                       => Int
                       -> symbolic
                       -> SymbolicConstraints
                       -> concrete
                       -> S.Seq (D.Trace Double)
                       -> Either SymExecError ([PathCondition], [CouplingCondition], EqualityCondition)
fillConstraintTemplate idx sym sc cr traces = runSymbolic $ do
  unless (match (D.dropProvenance cr) (D.dropProvenance sym)) $
    error $ "impossible: trace and symbol results do not match...\n"
            ++ show (D.dropProvenance cr)
            ++ "\n===========\n"
            ++ show (D.dropProvenance sym)
  subst <- go sym cr idx (toList $ sc ^. openSymbols) (toList traces)
  let pcs =
        (toList . fmap (simplify . first (`substituteB` subst)))
        (sc ^. pathConstraints)
  let cpls = (toList . fmap (reduceSubstB . flip substituteB subst)) (sc ^. couplingConstraints)
  let eqCond = reduceSubstB $ substituteB (D.dropProvenance cr `symEq` D.dropProvenance sym) subst
  return (pcs, cpls, eqCond)
  where
    simplify (cond, True)  = reduceSubstB cond
    simplify (cond, False) = reduceSubstB $ neg cond

    go sr cr _   syms                traces | length syms /= length traces =
      error $ "impossible: trace and symbol triples have different lengths...\n"
            ++ show (D.dropProvenance cr)
            ++ "\n===========\n"
            ++ show (D.dropProvenance sr)
            ++ "\n===========\n"
            ++ show traces
            ++ "\n===========\n"
            ++ show syms
    go _  _  _   []                  []                             = return []
    go sr cr idx ((cs, cc, ss):syms) (D.TrLaplace cc' _ cs':traces) = do
      ss' <- freshSReal $ "run_" ++ show idx ++ "_lap"
      subst <- go sr cr idx syms traces
      return $ (cs,double cs'):(cc,double cc'):(ss,sReal ss'):subst
    go _sr _cr _idx ((_cs, _cc, _ss):_syms) (D.TrGaussian _cc' _ _cs':_traces) =
      error "not implemented yet..."
    go sr cr _    syms                traces                         =
      error $ "impossible: trace and symbol triples have different lengths...\n"
            ++ show (D.dropProvenance cr)
            ++ "\n===========\n"
            ++ show (D.dropProvenance sr)
            ++ "\n===========\n"
            ++ show traces
            ++ "\n===========\n"
            ++ show syms

buildFullConstraints :: ( D.HasProvenance concrete
                        , D.HasProvenance symbolic
                        , Show concrete
                        , Show symbolic
                        , Show (D.DropProvenance concrete)
                        , Show (D.DropProvenance symbolic)
                        , SEq (D.DropProvenance concrete) (D.DropProvenance symbolic))
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
        --liftIO (Z3.optimizerAssertAndTrack cxt solver ast trackedBoolVar)
      toZ3 cond = do
        ast <- liftIO $ symbolicExprToZ3AST cxt (getBoolExpr cond)
        let prettyStr = pretty (getBoolExpr cond)
        return (prettyStr, ast)
      --toZ3R val = do
      --  ast <- liftIO $ symbolicExprToZ3AST cxt (getRealExpr val)
      --  let prettyStr = pretty (getRealExpr val)
      --  return (prettyStr, ast)
  $(logInfo) "loading constraints..."

  forM_ conditions $ \(pcs, cpls, eqCond) -> do
    forM_ pcs $ toZ3 >=> addToSolver
    forM_ cpls $ toZ3 >=> addToSolver
    toZ3 eqCond >>= addToSolver

  toZ3 (symCost %<= double eps) >>= addToSolver
  --toZ3R symCost >>= \(_label, symCostZ3) -> do
  --  liftIO $ Z3.optimizerMinimize cxt solver symCostZ3
  $(logInfo) "checking constraints..."
  r <- liftIO $ Z3.solverCheck cxt solver
  --r <- liftIO $ Z3.optimizerCheck cxt solver []
  case r of
    Z3.Sat -> do
      $(logInfo) "solver returned sat, retrieving total privacy cost..."
      model <- liftIO $ Z3.solverGetModel cxt solver
      --model <- liftIO $ Z3.optimizerGetModel cxt solver
      let getCostValue sym = do
            ast <- liftIO $ symbolicExprToZ3AST cxt (getRealExpr sym)
            liftIO $ Z3.evalReal cxt model ast
      cost <- liftIO $ getCostValue symCost
      case cost of
        Just cost' -> do
          costForced <- liftIO $ evaluate (force cost')
          let costForced' = fromRational costForced
          if costForced' <= eps
          then return (Ok costForced')
          else return (FailedEps eps costForced')
        Nothing ->
          error "failed to retrieve total privacy cost..."
    Z3.Unsat -> do
      $(logInfo) "solver returned unsat, retrieving unsat core..."
      cores <- liftIO $ Z3.solverGetUnsatCore cxt solver
      --cores <- liftIO $ Z3.optimizerGetUnsatCore cxt solver
      strs <- liftIO $ mapM ((liftIO . evaluate . force) <=< Z3.astToString cxt) cores
      return (FailedUnSat strs)
    Z3.Undef -> do
      $(logInfo) "solver returned undef, retrieving reason..."
      reason <- liftIO $ Z3.solverGetReasonUnknown cxt solver
      --reason <- liftIO $ Z3.optimizerGetReasonUnknown cxt solver
      return (Unknown reason)

solve :: ( MonadIO m
         , MonadLogger m
         , SEq (D.DropProvenance concrete) (D.DropProvenance symbolic)
         , Show concrete
         , Show symbolic
         , Show (D.DropProvenance concrete)
         , Show (D.DropProvenance symbolic)
         , D.HasProvenance concrete
         , D.HasProvenance symbolic)
      => symbolic
      -> SymbolicConstraints
      -> Bucket concrete
      -> Epsilon
      -> m (Either SymExecError (TestResult concrete symbolic))
solve sym sc bucket eps = do
  let totalCostExpr = sum (sc ^. costSymbols)
  case buildFullConstraints sym sc bucket of
    Left err -> return (Left err)
    Right conds -> do
      r <- solve_ conds totalCostExpr eps
      return (Right (TestResult r sym (map fst bucket)))

isAbsurd :: (MonadIO m, MonadLogger m) => SymbolicConstraints -> m (Maybe [String])
isAbsurd sc = do
  (cxt, solver) <- z3Init
  let addToSolver (label, ast) = do
        trackedBoolVar <- liftIO $ Z3.mkFreshBoolVar cxt label
        liftIO (Z3.solverAssertAndTrack cxt solver ast trackedBoolVar)
  let toZ3 cond = do
        ast <- liftIO $ symbolicExprToZ3AST cxt (getBoolExpr cond)
        let prettyStr = pretty (getBoolExpr cond)
        return (prettyStr, ast)
  forM_ (sc ^. pathConstraints) $ \(cond, truth) -> do
    (label, condZ3) <- toZ3 (if truth then cond else neg cond)
    addToSolver (label, condZ3)
  forM_ (sc ^. couplingConstraints) (toZ3 >=> addToSolver)

  r <- liftIO $ Z3.solverCheck cxt solver
  case r of
    Z3.Unsat -> do
      cores <- liftIO $ Z3.solverGetUnsatCore cxt solver
      strs <- liftIO $ mapM ((liftIO . evaluate . force) <=< Z3.astToString cxt) cores
      return (Just strs)
    _ -> return Nothing

gatherConstraints :: ( Monad m
                     , MonadIO m
                     , MonadLogger m
                     , Matchable r a
                     , Show r
                     , Show a
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
          notMatching = filter (not . flip match a) (map fst bucket)
          sc = SymbolicConstraints pc cc csyms osyms [code']
      in do absurdCore <- isAbsurd sc
            case absurdCore of
              Nothing ->
                if null notMatching
                then
                  return (Right (a, sc))
                else do
                  $(logInfo) ("definitely not equal to symbolic result: " <> pack (show a))
                  $(logInfo) (pack (show notMatching))
                  return (Left ResultDefinitelyNotEqual)
              Just cores -> return (Left (AbsurdConstraints cores))
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
sReal = RealExpr k_FLOAT_TOLERANCE . RealVar

sReal' :: Rational -> String -> RealExpr
sReal' tol = RealExpr tol . RealVar

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
laplaceSymbolic = laplaceSymbolic' k_FLOAT_TOLERANCE

laplaceSymbolic' :: (Monad m)
                 => Rational
                 -> D.WithDistributionProvenance RealExpr
                 -> Double
                 -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
laplaceSymbolic' tol centerWithProvenance w = do
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

  traceIdx <- gets (\st -> length (st ^. costSymbols))

  let shiftCond =
        if tol == 0
        then (sReal' 0 concreteSampleSym + sReal' 0 shiftSym) %== sReal' 0 lapSym
        else abs (sReal' tol concreteSampleSym + sReal' tol shiftSym - sReal' tol lapSym)
             %<= fromRational tol
  modify (\st -> st & couplingConstraints %~ (S.|> shiftCond))
  let costCond =
        sReal epsSym %>= (abs (sReal concreteCenterSym + sReal shiftSym - c)
                          / (fromRational . toRational $ w))
  modify (\st -> st & couplingConstraints %~ (S.|> costCond))

  modify (\st -> st & costSymbols %~ (S.|> sReal epsSym))
  modify (\st -> st & openSymbols %~ (S.|> (concreteSampleSym, concreteCenterSym, lapSym)))

  let provenance = D.Laplace traceIdx (D.provenance centerWithProvenance) w
  return (D.WithDistributionProvenance (sReal' tol lapSym) provenance)

gaussianSymbolic :: (Monad m)
                 => D.WithDistributionProvenance RealExpr
                 -> Double
                 -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
gaussianSymbolic = gaussianSymbolic' k_FLOAT_TOLERANCE

gaussianSymbolic' :: (Monad m)
                  => Rational
                  -> D.WithDistributionProvenance RealExpr
                  -> Double
                  -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
gaussianSymbolic' _ _ _ = error "not yet implemented"

substituteB :: BoolExpr -> [(String, RealExpr)] -> BoolExpr
substituteB (BoolExpr a) fts =
  let ftsAst = map (second getRealExpr) fts
  in BoolExpr $ Substitute a ftsAst

substituteR :: RealExpr -> [(String, RealExpr)] -> RealExpr
substituteR (RealExpr tol a) fts =
  let ftsAst = map (second getRealExpr) fts
  in RealExpr tol $ Substitute a ftsAst

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
  RealExpr tol left + RealExpr tol' right = RealExpr (max tol tol') (Add left right)
  RealExpr tol left - RealExpr tol' right = RealExpr (max tol tol') (Sub left right)
  RealExpr tol left * RealExpr tol' right = RealExpr (max tol tol') (Mul left right)
  abs (RealExpr tol ast) =
    let geZero = ast `Ge` Rat 0
        negAst = Rat 0 `Sub` ast
    in RealExpr tol $ Ite geZero ast negAst
  signum (RealExpr tol ast) =
    let eqZero = ast `Eq_` Rat 0
        gtZero = ast `Gt` Rat 0
    in RealExpr tol $ Ite eqZero (Rat 0) (Ite gtZero (Rat 1) (Rat (-1)))
  fromInteger v = RealExpr 0 $ Rat (fromInteger v)

instance Fractional RealExpr where
  RealExpr tol left / RealExpr tol' right = RealExpr (max tol tol') (Div left right)
  fromRational = RealExpr 0 . Rat

instance Boolean BoolExpr where
  and = coerce And
  or  = coerce Or
  neg = coerce Not

instance Ordered RealExpr where
  type CmpResult RealExpr = BoolExpr

  lhs %< rhs  = BoolExpr (getRealExpr lhs `Lt` getRealExpr rhs)
  lhs %<= rhs = BoolExpr (getRealExpr lhs `Le` getRealExpr rhs)
  lhs %> rhs  = BoolExpr (getRealExpr lhs `Gt` getRealExpr rhs)
  lhs %>= rhs = BoolExpr (getRealExpr lhs `Ge` getRealExpr rhs)
  lhs %== rhs = BoolExpr (getRealExpr lhs `Eq_` getRealExpr rhs)
  a %/= b = neg (a %== b)

instance Numeric     RealExpr
instance FracNumeric RealExpr
instance FuzziType   RealExpr
instance FuzziType   BoolExpr

instance (Monad m, Typeable m, Typeable r)
  => MonadDist (SymbolicT r m) where
  type NumDomain (SymbolicT r m) = D.WithDistributionProvenance RealExpr
  laplace   = laplaceSymbolic
  laplace'  = laplaceSymbolic'
  gaussian  = gaussianSymbolic
  gaussian' = gaussianSymbolic'

instance (Monad m, Typeable m, Typeable r)
  => MonadAssert (SymbolicT r m) where
  type BoolType (SymbolicT r m) = BoolExpr
  assertTrue  cond =
    case tryEvalBool cond of
      Nothing ->
        modify (\st -> st & pathConstraints %~ (S.|> (cond, True)))
      Just True -> return ()
      Just False ->
        throwError (AssertImpossible cond True)

  assertFalse cond =
    case tryEvalBool cond of
      Nothing ->
        modify (\st -> st & pathConstraints %~ (S.|> (cond, False)))
      Just False -> return ()
      Just True ->
        throwError (AssertImpossible cond False)

instance Matchable Double RealExpr where
  match v sv =
    case tryEvalReal sv of
      Just v' -> toRational v == v'
      Nothing -> True

instance SEq Int Int where
  symEq a b = bool (a == b)

instance SEq Bool Bool where
  symEq a b = bool (a == b)

instance SEq Double RealExpr where
  symEq a b =
    let tol = getTolerance b
    in if tol == 0
    then double a %== b
    else abs (double a - b) %<= fromRational (getTolerance b)

instance SEq (D.WithDistributionProvenance Double) (D.WithDistributionProvenance RealExpr) where
  symEq a b = symEq (D.value a) (D.value b)

instance (SEq a b, SEq c d) => SEq (a, c) (b, d) where
  symEq (a, c) (b, d) =
    BoolExpr (And (getBoolExpr (a `symEq` b)) (getBoolExpr (c `symEq` d)))

instance SEq a b => SEq (Maybe a) (Maybe b) where
  symEq (Just a) (Just b) = symEq a b
  symEq Nothing  Nothing  = bool True
  symEq _        _        = bool False

instance SEq a b => SEq [a] [b] where
  symEq [] []         = BoolExpr (JustBool True)
  symEq (x:xs) (y:ys) =
    BoolExpr $
    And (getBoolExpr (x `symEq` y))
        (getBoolExpr (xs `symEq` ys))
  symEq _      _      = BoolExpr (JustBool False)

instance SEq a b => SEq (PrivTree1D a) (PrivTree1D b) where
  symEq (PrivTree1D a) (PrivTree1D b) =
    case MM.mergeA whenMissing whenMissing whenMatched a b of
      Nothing         -> bool False
      Just equalities -> foldr Data.Fuzzi.Types.and (bool True) equalities
    where whenMissing = MM.traverseMissing (\_ _ -> Nothing)
          whenMatched = MM.zipWithAMatched (\_ c s -> Just (symEq c s))

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

tryEvalBool :: BoolExpr -> Maybe Bool
tryEvalBool = tryEvalBool' . getBoolExpr

tryEvalBool' :: SymbolicExpr -> Maybe Bool
tryEvalBool' (JustBool b) = Just b
tryEvalBool' (Lt a b)  = (<)  <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Le a b)  = (<=) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Gt a b)  = (>)  <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Ge a b)  = (>=) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalBool' (Eq_ a b) =
  case (==) <$> tryEvalReal' a <*> tryEvalReal' b of
    Just a -> Just a
    Nothing -> (==) <$> tryEvalBool' a <*> tryEvalBool' b
tryEvalBool' (And a b) = (&&) <$> tryEvalBool' a <*> tryEvalBool' b
tryEvalBool' (Or  a b) = (||) <$> tryEvalBool' a <*> tryEvalBool' b
tryEvalBool' (Not a)   = not <$> tryEvalBool' a
tryEvalBool' (Ite cond a b) = do
  cond' <- tryEvalBool' cond
  if cond'
  then tryEvalBool' a
  else tryEvalBool' b
tryEvalBool' _ = Nothing

tryEvalReal :: RealExpr -> Maybe Rational
tryEvalReal = tryEvalReal' . getRealExpr

tryEvalReal' :: SymbolicExpr -> Maybe Rational
tryEvalReal' (Rat v) = Just v
tryEvalReal' (Add a b) = (+) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Sub a b) = (-) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Mul a b) = (*) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Div a b) = (/) <$> tryEvalReal' a <*> tryEvalReal' b
tryEvalReal' (Ite cond a b) = do
  cond' <- tryEvalBool' cond
  if cond'
  then tryEvalReal' a
  else tryEvalReal' b
tryEvalReal' _ = Nothing

instance Monad m => MonadThrow (SymbolicT r m) where
  throwM (exc :: e) =
    case eqTypeRep (typeRep @e) (typeRep @AbortException) of
      Just HRefl -> throwError (ComputationAborted exc)
      _          -> throwError (InternalError ("unexpected exception: " ++ show exc))

instance D.HasProvenance (D.WithDistributionProvenance RealExpr) where
  type GetProvenance (D.WithDistributionProvenance RealExpr) = D.DistributionProvenance RealExpr
  type DropProvenance (D.WithDistributionProvenance RealExpr) = RealExpr
  getProvenance = D.provenance
  dropProvenance = D.value
