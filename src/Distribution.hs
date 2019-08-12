module Distribution where

import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Trans.Maybe
import Data.Functor.Identity
import Data.Functor.Classes
import Data.Random.Distribution.Normal
import Data.Random.Distribution.Uniform
import Data.Random.RVar
import Type.Reflection
import Types
import qualified Control.Monad.Trans.Class as MT
import qualified Data.Random as R
import qualified Data.Random.Lift as RL

newtype ConcreteDist a = ConcreteDist { runConcreteDist :: RVar a }
  deriving (Functor, Applicative, Monad)
  via (RVar)

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

sampleConcrete :: ConcreteDist a -> IO a
sampleConcrete = R.sample . runConcreteDist

newtype NoRandomness a = NoRandomness { runNoRandomness :: a }
  deriving (Functor, Applicative, Monad, Show1)
  via (Identity)
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
  Deterministic :: a -> DistributionProvenance a
  Laplace       :: a -> Double -> DistributionProvenance a
  Gaussian      :: a -> Double -> DistributionProvenance a
  Arith         :: DistributionProvenance a
                -> ArithOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  Unary         :: UOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  deriving (Show, Eq, Ord, Functor, Typeable)

instance Num a => Num (DistributionProvenance a) where
  a + b         = Arith a Add  b
  a * b         = Arith a Mult b
  a - b         = Arith a Sub  b
  abs a         = Unary Abs  a
  signum a      = Unary Sign a
  fromInteger v = Deterministic (fromInteger v)

instance Fractional a => Fractional (DistributionProvenance a) where
  a / b          = Arith a Div b
  fromRational v = Deterministic (fromRational v)

data WithDistributionProvenance a =
  WithDistributionProvenance { value :: a
                             , provenance :: DistributionProvenance a
                             }
  deriving (Show, Eq, Ord, Functor, Typeable)

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

instance Numeric a     => Numeric     (WithDistributionProvenance a)
instance FracNumeric a => FracNumeric (WithDistributionProvenance a)

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

instance (Monad m, Typeable m) => MonadAssert (MaybeT m) where
  type BoolType (MaybeT m) = Bool
  assertTrue v = guard v
