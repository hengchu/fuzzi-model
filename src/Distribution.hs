module Distribution where

import qualified Data.Random as R
import qualified Data.Random.Lift as RL
import Data.Random.RVar
import Data.Random.Distribution.Uniform
import Data.Random.Distribution.Normal
import Control.Monad.IO.Class
import Types

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

data ArithOp = Add | Mult | Sub | Div
  deriving (Show, Eq, Ord)

data DistributionProvenance (a :: *) where
  Deterministic :: a -> DistributionProvenance a
  Laplace       :: a -> Double -> DistributionProvenance a
  Gaussian      :: a -> Double -> DistributionProvenance a
  Arith         :: DistributionProvenance a
                -> ArithOp
                -> DistributionProvenance a
                -> DistributionProvenance a
  deriving (Show, Eq, Ord)

instance MonadDist ConcreteDist where
  type NumDomain ConcreteDist = Double
  laplace = laplaceConcrete
  gaussian = gaussianConcrete
