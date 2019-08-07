module Distribution where

import qualified Data.Random as R
import qualified Data.Random.Lift as RL
import Data.Random.RVar
import Data.Random.Distribution.Uniform
import Data.Random.Distribution.Normal
import Control.Monad.IO.Class

type Dist  = Data.Random.RVar.RVar
type DistT = Data.Random.RVar.RVarT

laplace :: (Applicative f) => Double -> Double -> DistT f Double
laplace center width = do
  r <- uniformT (-0.5) 0.5
  let positive = r > 0
  let sample = if positive
               then width * log (1 - 2 * abs r)
               else -width * log (1 - 2 * abs r)
  return $ center + sample

gaussian :: (Applicative f) => Double -> Double -> DistT f Double
gaussian mean stddev =
  normalT mean stddev

sample :: Dist a -> IO a
sample = R.sample
