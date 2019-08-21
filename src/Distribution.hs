module Distribution where

import Control.Monad
import Control.Monad.State.Class
import Control.Monad.Trans.Identity
import Control.Monad.Trans.Maybe
import Control.Monad.Trans.State hiding (modify)
import Data.Functor.Classes
import Data.Functor.Identity
import Data.Random.Distribution.Normal
import Data.Random.Distribution.Uniform
import Data.Random.RVar
import Data.Sequence
import Type.Reflection
import Types
import qualified Control.Monad.Trans.Class as MT
import qualified Data.Map.Strict as M
import qualified Data.Random as R

newtype ConcreteDist a = ConcreteDist { runConcreteDist :: RVar a }
  deriving (Functor, Applicative, Monad)
  via RVar

data Trace :: * -> * where
  TrLaplace  :: a -> Double -> a -> Trace a
  TrGaussian :: a -> Double -> a -> Trace a
  deriving (Show, Eq, Ord, Functor)

type Profile a = Seq (Trace a)
type DProfile  = Profile Double
type DProvenance k = DistributionProvenance k

-- |Type parameter 'k' is the type of the result. 'Buckets' maps results
-- identical up to provenance into the actual value of the result, paired with
-- the profiled trace of that execution.
type Buckets k = M.Map (DProvenance k) [(k, DProfile)]

newtype TracedDist a =
  TracedDist { runTracedDist_ :: StateT DProfile RVar a }
  deriving (Functor, Applicative, Monad) via (StateT DProfile RVar)
  deriving (MonadState DProfile) via (StateT DProfile RVar)

laplaceConcrete :: Double -> Double -> ConcreteDist Double
laplaceConcrete center width = ConcreteDist $ do
  r <- uniform (-0.5) 0.5
  let positive = r > 0
  let sample = if positive
               then width * log (1 - 2 * abs r)
               else -width * log (1 - 2 * abs r)
  return $ center + sample

gaussianConcrete :: Double -> Double -> ConcreteDist Double
gaussianConcrete mean stddev =
  ConcreteDist $ normalT mean stddev

laplaceTraced :: WithDistributionProvenance Double
              -> Double
              -> TracedDist (WithDistributionProvenance Double)
laplaceTraced center width = do
  let centerValue = value center
  lapSample <- (TracedDist . MT.lift)
    (runConcreteDist (laplaceConcrete centerValue width))
  let prov  = Laplace (provenance center) width
  let trace = TrLaplace centerValue width lapSample
  modify (|> trace)
  return (WithDistributionProvenance lapSample prov)

gaussianTraced :: WithDistributionProvenance Double
              -> Double
              -> TracedDist (WithDistributionProvenance Double)
gaussianTraced center width = do
  let centerValue = value center
  gaussSample <- (TracedDist . MT.lift)
    (runConcreteDist (gaussianConcrete centerValue width))
  let prov  = Gaussian (provenance center) width
  let trace = TrGaussian centerValue width gaussSample
  modify (|> trace)
  return (WithDistributionProvenance gaussSample prov)

sampleConcrete :: ConcreteDist a -> IO a
sampleConcrete = R.sample . runConcreteDist

sampleTraced :: TracedDist a -> IO (a, DProfile)
sampleTraced m = R.sample ((runStateT . runTracedDist_) m mempty)

newtype NoRandomness a = NoRandomness { runNoRandomness :: a }
  deriving (Functor, Applicative, Monad, Show1)
  via Identity
  deriving (Show, Eq, Ord)

laplaceNoRandomness :: Double -> Double -> NoRandomness Double
laplaceNoRandomness center _ = NoRandomness center

gaussianNoRandomness :: Double -> Double -> NoRandomness Double
gaussianNoRandomness center _ = NoRandomness center

data ArithOp = Add | Mult | Sub | Div
  deriving (Show, Eq, Ord)

data UOp = Abs | Sign
  deriving (Show, Eq, Ord)

data DistributionProvenance (a :: *) where
  Deterministic :: a
                -> DistributionProvenance a
  ListEmpty     :: DistributionProvenance [a]
  ListCons      :: (Show a, Eq a, Ord a)
                => DistributionProvenance a
                -> DistributionProvenance [a]
                -> DistributionProvenance [a]
  ListSnoc      :: (Show a, Eq a, Ord a)
                => DistributionProvenance [a]
                -> DistributionProvenance a
                -> DistributionProvenance [a]
  Laplace       :: DistributionProvenance a
                -> Double
                -> DistributionProvenance a
  Gaussian      :: DistributionProvenance a
                -> Double
                -> DistributionProvenance a
  Arith         :: DistributionProvenance a
                -> ArithOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  Unary         :: UOp
                -> DistributionProvenance a
                -> DistributionProvenance a

deriving instance (Show a) => Show (DistributionProvenance a)
deriving instance (Eq a) => Eq (DistributionProvenance a)
deriving instance (Ord a) => Ord (DistributionProvenance a)
deriving instance Typeable DistributionProvenance

instance Num a => Num (DistributionProvenance a) where
  a + b         = Arith a Add  b
  a * b         = Arith a Mult b
  a - b         = Arith a Sub  b
  abs           = Unary Abs
  signum        = Unary Sign
  fromInteger v = Deterministic (fromInteger v)

instance Fractional a => Fractional (DistributionProvenance a) where
  a / b          = Arith a Div b
  fromRational v = Deterministic (fromRational v)

data WithDistributionProvenance a =
  WithDistributionProvenance { value :: a
                             , provenance :: DistributionProvenance a
                             }
  deriving (Show, Eq, Ord, Typeable)

inject :: a -> WithDistributionProvenance a
inject a = WithDistributionProvenance a (Deterministic a)

instance Num a => Num (WithDistributionProvenance a) where
  a + b = WithDistributionProvenance (value a + value b) (provenance a + provenance b)
  a * b = WithDistributionProvenance (value a * value b) (provenance a * provenance b)
  a - b = WithDistributionProvenance (value a - value b) (provenance a - provenance b)
  abs a = WithDistributionProvenance (abs (value a)) (abs (provenance a))
  signum a = WithDistributionProvenance (signum (value a)) (signum (provenance a))
  fromInteger v = WithDistributionProvenance (fromInteger v) (fromInteger v)

instance Fractional a => Fractional (WithDistributionProvenance a) where
  a / b = WithDistributionProvenance (value a / value b) (provenance a / provenance b)
  fromRational v = WithDistributionProvenance (fromRational v) (fromRational v)

instance Ordered a => Ordered (WithDistributionProvenance a) where
  type CmpResult (WithDistributionProvenance a) = CmpResult a
  a %<  b = value a %<  value b
  a %<= b = value a %<= value b
  a %>  b = value a %>  value b
  a %>= b = value a %>= value b
  a %== b = value a %== value b
  a %/= b = value a %/= value b

instance (Show a, Eq a, Ord a, Typeable a)
  => ListLike (WithDistributionProvenance [a]) where
  type Elem       (WithDistributionProvenance [a]) =
    WithDistributionProvenance (Elem [a])
  type TestResult (WithDistributionProvenance [a]) = TestResult [a]

  nil       = WithDistributionProvenance nil ListEmpty
  cons x xs = WithDistributionProvenance
                (cons (value x) (value xs))
                (ListCons (provenance x) (provenance xs))
  snoc xs x = WithDistributionProvenance
                (snoc (value xs) (value x))
                (ListSnoc (provenance xs) (provenance x))
  isNil xs  = isNil (value xs)

instance Numeric a     => Numeric     (WithDistributionProvenance a)
instance FracNumeric a => FracNumeric (WithDistributionProvenance a)
instance {-# OVERLAPS #-} FuzziType a   => FuzziType   (WithDistributionProvenance a)

instance MonadDist ConcreteDist where
  type NumDomain ConcreteDist = Double
  laplace = laplaceConcrete
  gaussian = gaussianConcrete

instance MonadDist NoRandomness where
  type NumDomain NoRandomness = Double
  laplace = laplaceNoRandomness
  gaussian = gaussianNoRandomness

instance MonadDist m => MonadDist (MaybeT m) where
  type NumDomain (MaybeT m) = NumDomain m
  laplace c w  = MT.lift $ laplace c w
  gaussian c w = MT.lift $ gaussian c w

instance MonadDist m => MonadDist (IdentityT m) where
  type NumDomain (IdentityT m) = NumDomain m
  laplace c w = MT.lift $ laplace c w
  gaussian c w = MT.lift $ gaussian c w

instance (Monad m, Typeable m) => MonadAssert (MaybeT m) where
  type BoolType (MaybeT m) = Bool
  assertTrue = guard

instance (Monad m, Typeable m) => MonadAssert (IdentityT m) where
  type BoolType (IdentityT m) = Bool
  assertTrue _ = return ()

instance MonadDist TracedDist where
  type NumDomain TracedDist = WithDistributionProvenance Double
  laplace  = laplaceTraced
  gaussian = gaussianTraced

instance Matchable a b => Matchable (WithDistributionProvenance a) b where
  match a b = match (value a) b
