module Data.Fuzzi.Symbol where

{- HLINT ignore "Use newtype instead of data" -}
{- HLINT ignore "Use mapM" -}

import Control.DeepSeq
import Control.Exception
import Control.Lens
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Bifunctor
import Data.Foldable
import Data.Fuzzi.Interp
import Data.Fuzzi.Logging
import Data.Fuzzi.Types
import Data.Fuzzi.Z3
import Data.Text (pack)
import Data.Void
import Type.Reflection
import qualified Data.Fuzzi.Distribution as D
import qualified Data.Fuzzi.EDSL as EDSL
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.Map.Merge.Strict as MM
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S
import qualified Z3.Base as Z3
import System.Exit

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
  | WidthMustBeConstant
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
  {-
  liftIO $ putStrLn "-----------DEBUG-------------"
  forM (zip [0..] conditions) $ \(idx, cond) -> do
    liftIO $ putStrLn $ "======" ++ show idx ++ "======"
    forM_ (view _1 cond) $ liftIO . print . show
    forM_ (view _2 cond) $ liftIO . print . show
    (liftIO . print . show) (view _3 cond)
    liftIO $ putStrLn $ "===END" ++ show idx ++ "======"
  liftIO $ putStrLn "-----------DEBUG END---------"
  liftIO $ exitFailure
-}

  (cxt, solver) <- z3Init
  let addToSolver (label, ast) = do
        trackedBoolVar <- liftIO $ Z3.mkFreshBoolVar cxt label
        liftIO (Z3.solverAssertAndTrack cxt solver ast trackedBoolVar)
        --liftIO (Z3.optimizerAssertAndTrack cxt solver ast trackedBoolVar)
      toZ3 cond = do
        ast <- liftIO $ flip runReaderT M.empty $ symbolicExprToZ3AST cxt (getBoolExpr cond)
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
            ast <- liftIO $ flip runReaderT M.empty $ symbolicExprToZ3AST cxt (getRealExpr sym)
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
        ast <- liftIO $ flip runReaderT M.empty $ symbolicExprToZ3AST cxt (getBoolExpr cond)
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
                 -> D.WithDistributionProvenance RealExpr
                 -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
laplaceSymbolic = laplaceSymbolic' k_FLOAT_TOLERANCE

laplaceSymbolic' :: (Monad m)
                 => Rational
                 -> D.WithDistributionProvenance RealExpr
                 -> D.WithDistributionProvenance RealExpr
                 -> SymbolicT r m (D.WithDistributionProvenance RealExpr)
laplaceSymbolic' tol centerWithProvenance widthWithProvenance = do
  case tryEvalReal (D.value widthWithProvenance) of
    Nothing -> throwError WidthMustBeConstant
    Just (realToFrac -> w) -> do
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

      let provenance =
            D.Laplace
              traceIdx
              (D.provenance centerWithProvenance)
              (D.provenance widthWithProvenance)
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
