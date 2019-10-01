module Data.Fuzzi.Rosette where

import Control.Applicative
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
import Data.Fuzzi.Interp
import Data.Fuzzi.Logging
import Data.Fuzzi.Types
import Data.Fuzzi.Z3
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Text (pack)
import Prelude hiding (and, or, head)
import Type.Reflection
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.List.NonEmpty as NL
import qualified Data.Map.Strict as M
import qualified Data.Sequence as SS
import qualified Data.Set as S
import qualified Z3.Base as Z3

data CouplingInfo = CouplingInfo {
  _ciTraceIndex :: IntExpr
  , _ciTotalCost :: RealExpr
  , _ciCouplingConstraints :: BoolExpr
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''CouplingInfo

type NameMap = M.Map String Int

-- |Instantiate the 3 trace arrays and the 1 symbolic sample array for each run
-- in a bucket, and take the conjunction over all runs in a bucket.
data SymbolicState = SymbolicState {
  _ssNameMap :: NameMap
  , _ssSymbolicSampleArray :: ArrayExpr
  , _ssSymbolicShiftArray :: ArrayExpr
  , _ssTraceSampleArray :: ArrayExpr
  , _ssTraceCenterArray :: ArrayExpr
  , _ssTraceWidthArray :: ArrayExpr
  , _ssTraceSize :: IntExpr
  , _ssCouplingInfo :: NonEmpty CouplingInfo
  , _ssAssertions :: S.Set BoolExpr
  , _ssSourceCode :: PP.SomeFuzzi
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''SymbolicState

dummyState :: SymbolicState
dummyState =
  SymbolicState
    M.empty
    (array "ssample")
    (array "shift")
    (array "csample")
    (array "ccenter")
    (array "cwidth")
    0
    (dummyCouplingInfo :| [])
    S.empty
    (PP.MkSomeFuzzi (Lit 1 :: Fuzzi Int))
  where array = ArrayExpr . RealArrayVar
        dummyCouplingInfo = CouplingInfo 0 0 (bool True)

data RosetteException = ComputationAborted AbortException
                      | InternalError String
  deriving (Show, Eq, Ord, Typeable)

instance Exception RosetteException

newtype RosetteT m a =
  RosetteT { runRosetteT_ :: ExceptT RosetteException (StateT SymbolicState m) a }
  deriving (Functor, Applicative, Monad, MonadLogger)
    via (ExceptT RosetteException (StateT SymbolicState m))
  deriving ( MonadState SymbolicState
           , MonadError RosetteException
           )
    via (ExceptT RosetteException (StateT SymbolicState m))

type Bucket r = [(r, SS.Seq (Trace Double))]

newtype AnySat m = AnySat { runAnySat :: m BoolExpr }
newtype AllSat m = AllSat { runAllSat :: m (AllocatedArrays, BoolExpr) }

instance Monad m => Semigroup (AnySat m) where
  (AnySat m1) <> (AnySat m2) = AnySat $ liftA2 or m1 m2

instance Monad m => Monoid (AnySat m) where
  mempty = AnySat (return (bool False))

instance Monad m => Semigroup (AllSat m) where
  (AllSat m1) <> (AllSat m2) = AllSat $ do
    (env1, r1) <- m1
    (env2, r2) <- m2
    return (env1 <> env2, r1 `and` r2)

instance Monad m => Monoid (AllSat m) where
  mempty = AllSat (return (M.empty, bool True))

runRosetteT :: SymbolicState -> RosetteT m a -> m (Either RosetteException a, SymbolicState)
runRosetteT init =
  (flip runStateT init) . runExceptT . runRosetteT_

type Epsilon = Double

check :: ( MonadIO m
         , MonadLogger m
         , MonadCatch m
         , SEq r a
         , Show r
         , Show a
         )
      => Epsilon
      -> [Bucket r]
      -> Fuzzi (RosetteT m a)
      -> m Bool
check eps buckets prog = do
  rs <- mapM (\bkt -> runWithBucket eps bkt prog) buckets
  return (all id rs)

runWithBucket :: ( MonadIO m
                 , MonadLogger m
                 , MonadCatch m
                 , SEq r a
                 , Show r
                 , Show a
                 )
              => Epsilon
              -> Bucket r
              -> Fuzzi (RosetteT m a)
              -> m Bool
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
               -> m Bool
runWithBucket' eps bucket action = do
  (ctx, solver)  <- z3Init
  let handler (e :: RosetteException) = do
        $(logError) (pack $ "rosette symbolic execution exception: " ++ show e)
        return Nothing
  maybeArraysAndCondition <- (Just <$> coupleBucket ctx solver eps bucket action) `catch` handler
  case maybeArraysAndCondition of
    Just (arrays, cond) -> do
      z3Ast <- (flip runReaderT arrays) (symbolicExprToZ3AST ctx (getBoolExpr cond))
      let condPretty = pretty (getBoolExpr cond)
      label <- liftIO $ Z3.mkFreshBoolVar ctx condPretty
      liftIO $ Z3.solverAssertAndTrack ctx solver z3Ast label
      r <- liftIO $ Z3.solverCheck ctx solver
      case r of
        Z3.Sat -> return True
        _      -> return False
    Nothing -> return False

-- |For each result and trace value in the bucket, we need to find a symbolic
-- result and trace that is equal to the concrete result, and couples with the
-- concrete trace under the specified privacy budget.
-- May throw 'RosetteException'.
coupleBucket :: ( Monad m
                , MonadIO m
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
             -> m (AllocatedArrays, BoolExpr)
coupleBucket ctx solver eps bucket symbolicResults = do
  let shiftArrayName = "shift"
  shiftArray <- z3NewRealArray ctx solver shiftArrayName []
  runAllSat $ forEach (zip [0..] bucket) $ forEachConcrete ctx solver (shiftArrayName, shiftArray)
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
          let costCond = (coupling ^. totalCost) %<= (double eps)
          let cond     = equality `and` guardCond `and` costCond `and` (coupling ^. couplingConstraints)
          $(logDebug) (pack $ "============possible world " ++ show (concreteRunIdx, idx) ++ "============")
          $(logDebug) (pack $ "concrete: " ++ show concreteResult)
          $(logDebug) (pack $ "symbolic: " ++ show symResult)
          $(logDebug) (pack $ "equality: " ++ show equality)
          $(logDebug) (pack $ "cost: " ++ show costCond)
          $(logDebug) (pack $ "guard: " ++ show guardCond)
          $(logDebug) (pack $ "coupling: " ++ show (coupling ^. couplingConstraints))
          $(logDebug) ("============END===============")
          return cond

        forEachConcrete
          ctx solver
          (shiftArrayName, shiftArray) (runIdx :: Integer, (concreteResult, trace)) = AllSat $ do

          let runPrefix = "run_" ++ (show runIdx)
          let runConcretePrefix = runPrefix ++ "_concrete"
          let runSymbolicPrefix = runPrefix ++ "_symbolic"
          let runConcreteCenter = runConcretePrefix ++ "_center"
          let runConcreteWidth  = runConcretePrefix ++ "_width"
          let runConcreteSample = runConcretePrefix ++ "_sample"
          let runSymbolicSample = runSymbolicPrefix ++ "_sample"

          let traceValues = toList (fmap flattenTrace trace)

          centerArray <- z3NewRealArray ctx solver runConcreteCenter (map (view _1) traceValues)
          widthArray  <- z3NewRealArray ctx solver runConcreteWidth  (map (view _2) traceValues)
          sampleArray <- z3NewRealArray ctx solver runConcreteSample (map (view _3) traceValues)
          symSampleArray <- z3NewRealArray ctx solver runSymbolicSample []

          let env = M.fromList [ (shiftArrayName,    shiftArray)
                               , (runConcreteCenter, centerArray)
                               , (runConcreteWidth,  widthArray)
                               , (runConcreteSample, sampleArray)
                               , (runSymbolicSample, symSampleArray)
                               ]

          -- a guarded symbolic union of symbolic results
          let state = dummyState & symbolicSampleArray .~ (ArrayExpr (RealArrayVar runSymbolicSample))
                                 & symbolicShiftArray  .~ (ArrayExpr (RealArrayVar shiftArrayName))
                                 & traceSampleArray    .~ (ArrayExpr (RealArrayVar runConcreteSample))
                                 & traceCenterArray    .~ (ArrayExpr (RealArrayVar runConcreteCenter))
                                 & traceWidthArray     .~ (ArrayExpr (RealArrayVar runConcreteWidth))
                                 & traceSize           .~ (fromIntegral $ length trace)

          (possibleSymbolicResults, symbolicState) <- runRosetteT state symbolicResults
          symbolicResultUnion {- :: [(BoolExpr, a)] -} <-
            case possibleSymbolicResults of
              Left  err       -> liftIO (throwM err)
              Right symResult -> return (flatten symResult)

          cond <- runAnySat
            $ forEach (zip [0..] symbolicResultUnion) (forEachSymbolic runIdx concreteResult symbolicState)

          $(logInfo) (pack $ "=========RUN " ++ show runIdx ++ "===========")
          $(logInfo) (pack $ show cond)
          $(logInfo) (pack $ "=========END RUN " ++ show runIdx ++ "===========")

          return (env, optimizeBool cond)

mergeCouplingInfo :: BoolExpr -> CouplingInfo -> CouplingInfo -> CouplingInfo
mergeCouplingInfo cond left right =
  CouplingInfo
    (IntExpr $ iteCond (coerce $ left ^. traceIndex) (coerce $ right ^. traceIndex))
    (RealExpr tol $ iteCond (getRealExpr $ left ^. totalCost) (getRealExpr $ right ^. totalCost))
    (BoolExpr $ iteCond (coerce $ left ^. couplingConstraints) (coerce $ right ^. couplingConstraints))
  where tol = max (getTolerance (left ^. totalCost)) (getTolerance (right ^. totalCost))
        iteCond = ite' (coerce cond)

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

incTotalCost :: MonadState SymbolicState m => RealExpr -> m ()
incTotalCost cost = do
  info <- gets (NL.head . (view couplingInfo))
  replaceCouplingInfo (info & totalCost %~ (+cost))

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
                -> Double
                -> RosetteT m RealExpr
laplaceRosette' tolerance symCenter symWidth = do
  idx <- getCurrentTraceIndex
  setTraceIndex (simplifyInt $ idx + 1)

  shiftArray  <- gets (view symbolicShiftArray)
  symSampleArray <- gets (view symbolicSampleArray)
  sampleArray <- gets (view traceSampleArray)
  centerArray <- gets (view traceCenterArray)
  widthArray  <- gets (view traceWidthArray)

  let symbolicSample = at' tolerance symSampleArray idx
  let shift          = at' tolerance shiftArray  idx
  let sample         = at' tolerance sampleArray idx
  let center         = at' tolerance centerArray idx
  let width          = at' tolerance widthArray  idx

  let symbolicCost   = (abs (center + shift - symCenter)) / (double symWidth)
  let couplingAssertion = if tolerance == 0
                          then symbolicSample %== (sample + shift)
                          else abs (symbolicSample - sample - shift) %<= fromRational tolerance
  let widthIdenticalAssertion = (width %== double symWidth)

  traceLength <- gets (view traceSize)

  incTotalCost symbolicCost
  conjunctCouplingConstraint (idx %< traceLength)
  conjunctCouplingConstraint widthIdenticalAssertion
  conjunctCouplingConstraint couplingAssertion

  return symbolicSample

laplaceRosette :: Monad m
               => RealExpr
               -> Double
               -> RosetteT m RealExpr
laplaceRosette = laplaceRosette' k_FLOAT_TOLERANCE

evalM :: MonadLogger m
      => Fuzzi (RosetteT m a) -> RosetteT m (GuardedSymbolicUnion a)
evalM (Return a) = return (pure $ evalPure a)
evalM (Sequence a b) = do
  ua <- evalM a
  ub <- traverse (evalM . const b) ua
  return (joinGuardedSymbolicUnion ub)
evalM (Bind a f) = do
  ua <- evalM a
  ub <- traverse (evalM . f . Lit) ua
  return (joinGuardedSymbolicUnion ub)
evalM (IfM cond a b) = do
  let cond' = evalPure cond
  $(logInfo) (pack $ "branching on: " ++ show cond')
  pushCouplingInfo
  a' <- evalM a
  $(logInfo) "True branch results: "
  forM_ (flatten a') $ \(cond, value) -> do
    $(logInfo) (pack $ "guard = " ++ show cond ++ ", value = " ++ show value)
  infoA <- popCouplingInfo
  pushCouplingInfo
  b' <- evalM b
  $(logInfo) "False branch results: "
  forM_ (flatten b') $ \(cond, value) -> do
    $(logInfo) (pack $ "guard = " ++ show cond ++ ", value = " ++ show value)
  infoB <- popCouplingInfo
  replaceCouplingInfo (mergeCouplingInfo cond' infoA infoB)
  return $ mergeUnion cond' a' b'
evalM (Abort reason) = do
  let msg = pack ("computation may diverge due to reason: " ++ reason)
  $(logWarn) msg
  throwM (AbortException reason)
evalM (Laplace' tolerance center width) = do
  sample <- laplace' tolerance (evalPure center) width
  return (pure sample)
evalM (Laplace center width) = do
  sample <- laplace (evalPure center) width
  return (pure sample)
evalM (Gaussian' tolerance center width) = do
  sample <- gaussian' tolerance (evalPure center) width
  return (pure sample)
evalM (Gaussian center width) = do
  sample <- gaussian (evalPure center) width
  return (pure sample)
evalM other =
  error $ "evalM: received a non-monadic Fuzzi construct " ++ show (PP.MkSomeFuzzi other)

evalPure :: FuzziType a => Fuzzi a -> a
evalPure = eval

instance (Monad m, Typeable m) => MonadDist (RosetteT m) where
  type NumDomain (RosetteT m) = RealExpr
  laplace   = laplaceRosette
  laplace'  = laplaceRosette'

  gaussian  = error "not implemented"
  gaussian' = error "not implemented"

instance (Monad m, Typeable m) => MonadAssert (RosetteT m) where
  type BoolType (RosetteT m) = BoolExpr
  assertTrue cond =
    assertions %= S.insert cond

instance Monad m => MonadThrow (RosetteT m) where
  throwM (exc :: e) =
    case eqTypeRep (typeRep @e) (typeRep @AbortException) of
      Just HRefl -> throwError (ComputationAborted exc)
      _          -> throwError (InternalError ("unexpected exception: " ++ show exc))
