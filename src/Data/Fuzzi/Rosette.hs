module Data.Fuzzi.Rosette where

import Control.Lens hiding ((<|), at)
import Control.Monad
import Control.Monad.Catch
import Control.Monad.Except
import Control.Monad.State.Class
import Control.Monad.Trans.State hiding (gets, put, modify)
import Data.Coerce
import Data.Fuzzi.EDSL
import Data.Fuzzi.Interp
import Data.Fuzzi.Logging
import Data.Fuzzi.Types
import Data.List.NonEmpty (NonEmpty(..), (<|))
import Data.Text (pack)
import Prelude hiding (and, head)
import Type.Reflection
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.List.NonEmpty as NL
import qualified Data.Map.Strict as M
import qualified Data.Set as S

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
  deriving (Functor, Applicative, Monad)
    via (ExceptT RosetteException (StateT SymbolicState m))
  deriving ( MonadState SymbolicState
           , MonadError RosetteException
           )
    via (ExceptT RosetteException (StateT SymbolicState m))

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

  incTotalCost symbolicCost
  conjunctCouplingConstraint widthIdenticalAssertion
  conjunctCouplingConstraint couplingAssertion

  return symbolicSample

laplaceRosette :: Monad m
                => RealExpr
                -> Double
                -> RosetteT m RealExpr
laplaceRosette = laplaceRosette' k_FLOAT_TOLERANCE

-- TODO: Also need MonadState to keep track of concrete traces, and for
-- generating fresh symbols
evalM :: ( MonadDist m
         , NumDomain m ~ RealExpr
         , MonadAssert m
         , BoolType m ~ BoolExpr
         , MonadLogger m)
      => Fuzzi (m a) -> m (GuardedSymbolicUnion a)
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
  -- TODO: push symbolic state here? laplace/gaussian will consume traces, but
  -- we can't let them diverge after the if statement
  a' <- evalM a
  b' <- evalM b
  return $ mergeUnion cond'
    (joinGuardedSymbolicUnion $ guardedSingleton cond' a')
    (joinGuardedSymbolicUnion $ guardedSingleton (neg cond') b')
evalM (Abort reason) = do
  let msg = pack ("computation may diverge due to reason: " ++ reason)
  $(logWarn) msg
  throwM (AbortException reason)
evalM (Laplace' tolerance center width) = do
  sample <- laplace' tolerance (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM (Laplace center width) = do
  sample <- laplace (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM (Gaussian' tolerance center width) = do
  sample <- gaussian' tolerance (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
  return (pure sample)
evalM (Gaussian center width) = do
  sample <- gaussian (evalPure center) width
  -- TODO: attach coupling constraints here instead of using pure
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
  -- TODO: do something special with abort exception
  throwM exc = throwError (InternalError ("unexpected exception: " ++ show exc))
