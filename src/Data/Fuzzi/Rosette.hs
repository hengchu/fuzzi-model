module Data.Fuzzi.Rosette where

import Control.Applicative
import Control.DeepSeq
import Control.Lens hiding ((<|), at)
import Control.Monad
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.State.Class
import Control.Monad.Trans.Reader
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Coerce
import Data.Foldable hiding (and, or)
import Data.Fuzzi.Distribution (Trace(..))
import Data.Fuzzi.EDSL
import Data.Fuzzi.IfCxt
import Data.Fuzzi.Interp
import Data.Fuzzi.Logging
import Data.Fuzzi.Types
import Data.Fuzzi.Z3
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Proxy
import Data.Text (pack)
import Data.Time.Clock
import GHC.Generics
import Prelude hiding (and, or, head)
import Type.Reflection
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.HashMap.Strict as HM
import qualified Data.List.NonEmpty as NL
import qualified Data.Map.Strict as M
import qualified Data.Sequence as SS
import qualified Data.Set as S
import qualified Z3.Base as Z3

data CouplingInfo = CouplingInfo {
  _ciTraceIndex :: IntExpr
  , _ciCouplingConstraints :: BoolExpr
  } deriving (Show, Eq, Ord, Generic)

makeLensesWith abbreviatedFields ''CouplingInfo

instance NFData CouplingInfo

type NameMap = M.Map String Int

-- |Instantiate the 3 trace arrays and the 1 symbolic sample array for each run
-- in a bucket, and take the conjunction over all runs in a bucket.
data SymbolicState = SymbolicState {
  _ssNameMap :: NameMap
  , _ssAliasMemoization :: HM.HashMap SymbolicExpr String
  , _ssAliasBoolPrefix :: String
  , _ssSymbolicSamplePrefix :: String
  , _ssSymbolicShiftArray :: ArrayDecl RealExpr
  , _ssSymbolicCostArray :: ArrayDecl RealExpr
  , _ssTraceSampleArray :: ArrayDecl RealExpr
  , _ssTraceCenterArray :: ArrayDecl RealExpr
  , _ssTraceWidthArray :: ArrayDecl RealExpr
  , _ssTraceSize :: IntExpr
  , _ssCouplingInfo :: NonEmpty CouplingInfo
  , _ssAssertions :: S.Set BoolExpr
  -- , _ssSourceCode :: PP.SomeFuzzi
  } deriving (Show, Eq, Ord, Generic)

instance NFData SymbolicState

makeLensesWith abbreviatedFields ''SymbolicState

dummyState :: SymbolicState
dummyState =
  SymbolicState
    M.empty
    HM.empty
    "bool"
    "lap"
    array
    array
    array
    array
    array
    0
    (dummyCouplingInfo :| [])
    S.empty
    -- (PP.MkSomeFuzzi (Lit 1 :: Fuzzi Int))
  where array = newArrayDecl getRealExpr (RealExpr k_FLOAT_TOLERANCE) [] 0
        dummyCouplingInfo = CouplingInfo 0 (bool True)

data RosetteException = ComputationAborted AbortException
                      | WidthMustBeConstant
                      | BucketSizeMismatch [Int]
                      | EmptyBucket
                      | InternalError String
  deriving (Show, Eq, Ord, Generic, Typeable)

instance Exception RosetteException
instance NFData RosetteException

newtype RosetteT m a =
  RosetteT { runRosetteT_ :: ExceptT RosetteException (StateT SymbolicState m) a }
  deriving (Functor, Applicative, Monad, MonadLogger)
    via (ExceptT RosetteException (StateT SymbolicState m))
  deriving ( MonadState SymbolicState
           , MonadError RosetteException
           , MonadCatch
           , MonadMask
           , MonadIO
           )
    via (ExceptT RosetteException (StateT SymbolicState m))

instance MonadTrans RosetteT where
  lift = RosetteT . lift . lift

type Bucket r = [(r, SS.Seq (Trace Double))]

newtype AnySat m = AnySat { runAnySat :: m BoolExpr }
newtype AllSat m = AllSat { runAllSat :: m BoolExpr }

instance Monad m => Semigroup (AnySat m) where
  (AnySat m1) <> (AnySat m2) = AnySat $ liftA2 or m1 m2

instance Monad m => Monoid (AnySat m) where
  mempty = AnySat (return (bool False))

instance Monad m => Semigroup (AllSat m) where
  (AllSat m1) <> (AllSat m2) =
    AllSat $ liftA2 and m1 m2

instance Monad m => Monoid (AllSat m) where
  mempty = AllSat (return (bool True))

runRosetteT :: SymbolicState
            -> RosetteT m a
            -> m (Either RosetteException a, SymbolicState)
runRosetteT init =
  (flip runStateT init) . runExceptT . runRosetteT_

type Epsilon = Double

data SolverResult =
  Ok Epsilon
  | Failed
  deriving (Show, Eq, Ord)

isOk :: SolverResult -> Bool
isOk (Ok _) = True
isOk _      = False

isFailed :: SolverResult -> Bool
isFailed  = not . isOk

check :: ( MonadIO m
         , MonadLogger m
         , MonadCatch m
         , MonadMask m
         , Typeable m
         , SEq r a
         , Show r
         , Show a
         )
      => Epsilon
      -> [Bucket r]
      -> Fuzzi (RosetteT m a)
      -> m [SolverResult]
check eps buckets prog =
  mapM (\bkt -> runWithBucket eps bkt prog) buckets

runWithBucket :: ( MonadIO m
                 , MonadLogger m
                 , MonadCatch m
                 , MonadMask m
                 , Typeable m
                 , SEq r a
                 , Show r
                 , Show a
                 )
              => Epsilon
              -> Bucket r
              -> Fuzzi (RosetteT m a)
              -> m SolverResult
runWithBucket eps bucket prog = runWithBucket' eps bucket (evalM prog)

runWithBucket' :: ( MonadIO m
                  , MonadLogger m
                  , MonadCatch m
                  , SEq r a
                  , Show r
                  , Show a
                  )
               => Epsilon
               -> Bucket r
               -> RosetteT m (GuardedSymbolicUnion a)
               -> m SolverResult
runWithBucket' eps bucket action = do
  !start <- liftIO $ getCurrentTime
  (ctx, solver)  <- z3Init
  let handler (e :: RosetteException) = do
        $(logError) (pack $ "rosette symbolic execution exception: " ++ show e)
        return Nothing
  maybeArraysAndCondition <- (Just <$> coupleBucket ctx solver eps bucket action) `catch` handler
  case maybeArraysAndCondition of
    Just (costSum, cond) -> do
      -- $(logError) (pack $ show cond)
      z3Ast <- symbolicExprToZ3AST ctx (getBoolExpr cond)
      let condPretty = pretty (getBoolExpr cond)
      label <- liftIO $ Z3.mkFreshBoolVar ctx condPretty
      liftIO $ Z3.solverAssertAndTrack ctx solver z3Ast label
      !constraintGenerationEndTime <- liftIO $ getCurrentTime
      $(logInfo) (pack $ "constraint generation took " ++ show (constraintGenerationEndTime `diffUTCTime` start))
      r <- liftIO $ Z3.solverCheck ctx solver
      !solverReturnedTime <- liftIO $ getCurrentTime
      $(logInfo) (pack $ "solver took " ++ show (solverReturnedTime `diffUTCTime` constraintGenerationEndTime))
      case r of
        Z3.Sat -> do
          model <- liftIO $ Z3.solverGetModel ctx solver
          costAst <- symbolicExprToZ3AST ctx (getRealExpr costSum)
          maybeCost <- liftIO $ Z3.evalReal ctx model costAst
          case maybeCost of
            Just (fromRational -> cost) -> return (Ok cost)
            _ -> throwM (InternalError "failed to retrieve total cost from SMT model")
        _ -> return Failed
    Nothing -> return Failed

-- |For each result and trace value in the bucket, we need to find a symbolic
-- result and trace that is equal to the concrete result, and couples with the
-- concrete trace under the specified privacy budget.
-- May throw 'RosetteException'.
coupleBucket :: ( Monad m
                , MonadIO m
                , MonadThrow m
                , MonadLogger m
                , SEq r a
                , Show r
                , Show a
                )
             => Z3.Context
             -> Z3.Solver
             -> Epsilon
             -> Bucket r
             -> RosetteT m (GuardedSymbolicUnion a)
             -> m (RealExpr, BoolExpr)
coupleBucket ctx solver eps bucket symbolicResults = do
  let shiftArrayName = "shift"
  let costArrayName = "cost"
  let bucketLengths = map (length . snd) bucket
  len <-
    case bucketLengths of
      [] -> throwM EmptyBucket
      (len:lens) -> if any (/= len) lens
                    then throwM (BucketSizeMismatch bucketLengths)
                    else return len

  let shiftSymbols = map (\idx -> sReal $ shiftArrayName ++ show idx) [0..len-1]
  let shiftArray = newArrayDecl getRealExpr (RealExpr k_FLOAT_TOLERANCE) shiftSymbols 0

  let costSymbols = map (\idx -> sReal $ costArrayName ++ show idx) [0..len-1]
  let costArray = newArrayDecl getRealExpr (RealExpr k_FLOAT_TOLERANCE) costSymbols 0
  let costSum = sumArray costArray

  cond <- runAllSat $ forEach (zip [0..] bucket) $ forEachConcrete ctx solver costArray shiftArray
  return (costSum, cond `and` costSum %<= double eps)
  where forEach :: Monoid m => [a] -> (a -> m) -> m
        forEach = flip foldMap

        flattenTrace (TrLaplace c w s) = (c, w, s)
        flattenTrace (TrGaussian _ _ _) = error "not implemented"

        forEachSymbolic
          concreteRunIdx
          concreteResult
          symbolicState
          (idx :: Integer, (guardCond, symResult)) = AnySat $ do

          let coupling = NL.head $ symbolicState ^. couplingInfo
          let equality = concreteResult `symEq` symResult
          let asserts  = S.foldr and (bool True) (symbolicState ^. assertions)
          let cond     = equality
                         `and` guardCond
                         `and` (coupling ^. couplingConstraints)
                         `and` asserts
          -- $(logDebug) (pack $ "============possible world " ++ show (concreteRunIdx, idx) ++ "============")
          -- $(logDebug) (pack $ "concrete: " ++ show concreteResult)
          -- $(logDebug) (pack $ "symbolic: " ++ show symResult)
          -- $(logDebug) (pack $ "equality: " ++ show equality)
          -- $(logDebug) (pack $ "cost: " ++ show costCond)
          -- $(logDebug) (pack $ "guard: " ++ show guardCond)
          -- $(logDebug) (pack $ "coupling: " ++ show (coupling ^. couplingConstraints))
          -- $(logDebug) ("============END===============")
          return cond

        forEachConcrete
          ctx solver
          costArray shiftArray (runIdx :: Integer, (concreteResult, trace)) = AllSat $ do

          let runPrefix = "run_" ++ (show runIdx)
          let runSymbolicPrefix = runPrefix ++ "_symbolic"
          let runSymbolicSample = runSymbolicPrefix ++ "_sample"
          let runAliasBoolPrefix = runPrefix ++ "_bool"

          let traceValues = toList (fmap flattenTrace trace)

          let centerArray =
                newArrayDecl
                  getRealExpr
                  (RealExpr k_FLOAT_TOLERANCE)
                  (map (double . view _1) traceValues)
                  0
          let widthArray =
                newArrayDecl
                  getRealExpr
                  (RealExpr k_FLOAT_TOLERANCE)
                  (map (double . view _2) traceValues)
                  0
          let sampleArray =
                newArrayDecl
                  getRealExpr
                  (RealExpr k_FLOAT_TOLERANCE)
                  (map (double . view _3) traceValues)
                  0

          -- a guarded symbolic union of symbolic results
          let state = dummyState & symbolicSamplePrefix .~ runSymbolicSample
                                 & symbolicShiftArray   .~ shiftArray
                                 & symbolicCostArray    .~ costArray
                                 & traceSampleArray     .~ sampleArray
                                 & traceCenterArray     .~ centerArray
                                 & traceWidthArray      .~ widthArray
                                 & aliasBoolPrefix      .~ runAliasBoolPrefix
                                 & traceSize            .~ (fromIntegral $ length trace)

          (possibleSymbolicResults, symbolicState) <- runRosetteT state symbolicResults
          symbolicResultUnion {- :: [(BoolExpr, a)] -} <-
            case possibleSymbolicResults of
              Left  err       -> liftIO (throwM err)
              Right symResult -> return (flatten symResult)

          cond <- runAnySat
            $ forEach (zip [0..] symbolicResultUnion) (forEachSymbolic runIdx concreteResult symbolicState)

          -- $(logInfo) (pack $ "=========RUN " ++ show runIdx ++ "===========")
          -- $(logInfo) (pack $ show cond)
          -- $(logInfo) (pack $ "=========END RUN " ++ show runIdx ++ "===========")

          return $ optimizeBool cond

mergeCouplingInfo :: BoolExpr -> CouplingInfo -> CouplingInfo -> CouplingInfo
mergeCouplingInfo cond left right =
  CouplingInfo
    (IntExpr $ iteCond (coerce $ left ^. traceIndex) (coerce $ right ^. traceIndex))
    (BoolExpr $ iteCond (coerce $ left ^. couplingConstraints) (coerce $ right ^. couplingConstraints))
  where iteCond = ite' (coerce cond)

pushCouplingInfo :: MonadState SymbolicState m => m ()
pushCouplingInfo = do
  info <- gets (NL.head . (view couplingInfo))
  couplingInfo %= (info <|)

popCouplingInfo :: MonadState SymbolicState m => m CouplingInfo
popCouplingInfo = do
  info <- gets (NL.head . (view couplingInfo))
  couplingInfo %= \infoList -> NL.fromList (NL.tail infoList)
  return info

replaceCouplingInfo :: MonadState SymbolicState m => CouplingInfo -> m ()
replaceCouplingInfo info = do
  tail <- gets (NL.tail . (view couplingInfo))
  couplingInfo .= info :| tail

getCurrentTraceIndex :: MonadState SymbolicState m => m IntExpr
getCurrentTraceIndex = do
  info <- gets (NL.head . (view couplingInfo))
  return (info ^. traceIndex)

setTraceIndex :: MonadState SymbolicState m => IntExpr -> m ()
setTraceIndex idx = do
  info <- gets (NL.head . (view couplingInfo))
  replaceCouplingInfo (info & traceIndex .~ idx)

conjunctCouplingConstraint :: MonadState SymbolicState m => BoolExpr -> m ()
conjunctCouplingConstraint cond = do
  info <- gets (NL.head . (view couplingInfo))
  replaceCouplingInfo (info & couplingConstraints %~ (and cond))

freshName :: Monad m => String -> RosetteT m String
freshName hint = do
  names <- gets (view nameMap)
  case M.lookup hint names of
    Nothing -> do
      nameMap %= M.insert hint 0
      return (hint ++ "0")
    Just idx -> do
      nameMap %= M.insert hint (idx+1)
      return $ hint ++ (show (idx + 1))

freshSReal' :: Monad m => Rational -> String -> RosetteT m RealExpr
freshSReal' tol hint = do
  name <- freshName hint
  return $ sReal' tol name

laplaceRosette' :: Monad m
                => Rational
                -> RealExpr
                -> RealExpr
                -> RosetteT m RealExpr
laplaceRosette' tolerance symCenter symWidth = do
  case tryEvalReal symWidth of
    Nothing -> throwError WidthMustBeConstant
    Just (realToFrac -> doubleWidth) -> do
      idx <- getCurrentTraceIndex
      setTraceIndex (simplifyInt $ idx + 1)

      sampleName <- gets (view symbolicSamplePrefix)

      shiftArray  <- gets (view symbolicShiftArray)
      costArray   <- gets (view symbolicCostArray)
      sampleArray <- gets (view traceSampleArray)
      centerArray <- gets (view traceCenterArray)
      widthArray  <- gets (view traceWidthArray)

      symbolicSample <- freshSReal' tolerance sampleName
      let shift          = at shiftArray  idx
      let sample         = at sampleArray idx
      let center         = at centerArray idx
      let width          = at widthArray  idx
      let cost           = at costArray   idx

      let symbolicCost   = (abs (center + shift - symCenter)) / (double doubleWidth)
      let couplingAssertion = if tolerance == 0
                              then symbolicSample %== (sample + shift)
                              else abs (symbolicSample - sample - shift) %<= fromRational tolerance
      let widthIdenticalAssertion = (width %== double doubleWidth)

      traceLength <- gets (view traceSize)

      conjunctCouplingConstraint (cost %>= symbolicCost)
      conjunctCouplingConstraint (idx %< traceLength)
      conjunctCouplingConstraint widthIdenticalAssertion
      conjunctCouplingConstraint couplingAssertion

      return symbolicSample

laplaceRosette :: (Monad m)
               => RealExpr
               -> RealExpr
               -> RosetteT m RealExpr
laplaceRosette = laplaceRosette' k_FLOAT_TOLERANCE

evalM :: (MonadLogger m, Typeable m, MonadMask m, MonadIO m)
      => Fuzzi (RosetteT m a) -> RosetteT m (GuardedSymbolicUnion a)
evalM (Return a) = return (pure $ evalPure a)
evalM (Sequence a b) = do
  ua <- evalM a
  ub <- mapM (evalM . const b) ua
  return (joinGuardedSymbolicUnion ub)
evalM (Bind a f) = {-# SCC "evalM_Bind" #-} do
  ua <- evalM a
  ub <- mapM (evalM . f . Lit) ua
  return (joinGuardedSymbolicUnion ub)
evalM (IfM ((tryEvalBool . evalPure) -> Just True) a _) = evalM a
evalM (IfM ((tryEvalBool . evalPure) -> Just False) _ b) = evalM b
evalM (IfM cond a b) = {-# SCC "evalM_IfM" #-} do
  let cond' = evalPure cond
  let acquire = pushCouplingInfo
  let release _ _ = popCouplingInfo

  (maybeA, infoA) <-
    generalBracket acquire release (const $ Just <$> evalM a)
  (maybeB, infoB) <-
    generalBracket acquire release (const $ Just <$> evalM b)

  case (maybeA, maybeB) of
    (Just a', Just b') -> do
      replaceCouplingInfo (mergeCouplingInfo cond' infoA infoB)
      mergeUnionM cond' a' b'
    (Just a', _) -> do
      $(logWarn) ("false branch lead to abort, ignoring its results...")
      replaceCouplingInfo infoA
      return a'
    (_, Just b') -> do
      $(logWarn) ("true branch lead to abort, ignoring its results...")
      replaceCouplingInfo infoB
      return b'
    (_, _) -> do
      $(logError) "both branch leads to abort"
      throwM (AbortException "both branches of ifM abort")
evalM (Abort reason) = do
  throwM (AbortException reason)
evalM (Laplace' tolerance center width) = {-# SCC "evalM_Laplace'" #-} do
  sample <- laplace' tolerance (evalPure center) (evalPure width)
  return (pure sample)
evalM (Laplace center width) = {-# SCC "evalM_Laplace" #-} do
  sample <- laplace (evalPure center) (evalPure width)
  return (pure sample)
evalM (Gaussian' tolerance center width) = do
  sample <- gaussian' tolerance (evalPure center) width
  return (pure sample)
evalM (Gaussian center width) = do
  sample <- gaussian (evalPure center) width
  return (pure sample)
evalM (If (cond :: Fuzzi bool) a b) = do
  let cond' = evalPure cond
  case eqTypeRep (typeRep @bool) (typeRep @BoolExpr) of
    Just HRefl -> do
      let symNegCond = getBoolExpr (neg cond')
      (z3Cxt, z3Solver) <- z3Init
      ast <- symbolicExprToZ3AST z3Cxt symNegCond
      liftIO $ Z3.solverAssertCnstr z3Cxt z3Solver ast
      r <- liftIO $ Z3.solverCheck z3Cxt z3Solver
      case r of
        Z3.Unsat -> -- this means it's impossible to get the negation, so the
                    -- condition is always true
          evalM a
        _ -> do
          liftIO $ Z3.solverReset z3Cxt z3Solver
          let symCond = getBoolExpr cond'
          ast <- symbolicExprToZ3AST z3Cxt symCond
          liftIO $ Z3.solverAssertCnstr z3Cxt z3Solver ast
          r <- liftIO $ Z3.solverCheck z3Cxt z3Solver
          case r of
            Z3.Unsat -> -- this means it's impossible to get the condition, so
                        -- it's always false
              evalM b
            _ -> liftM2 union (evalM a) (evalM b)
    Nothing ->
      ifCxt (Proxy :: Proxy (ConcreteBoolean bool))
            (if toBool cond' then evalM a else evalM b)
            (liftM2 union (evalM a) (evalM b))
evalM other =
  throwError . InternalError
  $ "evalM: received a non-monadic Fuzzi construct " ++ show (PP.MkSomeFuzzi other)

evalPure :: FuzziType a => Fuzzi a -> a
evalPure = eval

instance (Monad m, Typeable m) => MonadDist (RosetteT m) where
  type NumDomain (RosetteT m) = RealExpr
  laplace   = laplaceRosette
  laplace'  = laplaceRosette'

  gaussian  = error "not implemented"
  gaussian' = error "not implemented"

instance (Monad m, MonadThrow m, Typeable m) => MonadAssert (RosetteT m) where
  type BoolType (RosetteT m) = BoolExpr
  assertTrue cond =
    assertions %= S.insert cond

instance (Monad m, MonadThrow m) => MonadThrow (RosetteT m) where
  throwM (exc :: e) =
    case eqTypeRep (typeRep @e) (typeRep @AbortException) of
      Just HRefl -> lift $ throwM (ComputationAborted exc)
      _          -> throwError (InternalError ("unexpected exception: " ++ show exc))

instance (Monad m, MonadThrow m, Typeable m) => MonadSymbolicMerge (RosetteT m) where
  -- no point in aliasing something twice
  alias bool@(BoolExpr (BoolVar _)) = return bool
  alias bool = do
    memo <- gets (view aliasMemoization)
    -- hash-consing
    case HM.lookup (getBoolExpr bool) memo of
      Just name -> return (BoolExpr (BoolVar name))
      Nothing -> do
        prefix <- gets (view aliasBoolPrefix)
        var <- freshName prefix
        let expr = BoolExpr (BoolVar var)
        assertTrue (beq expr bool)
        aliasMemoization %= HM.insert (getBoolExpr bool) var
        return expr
