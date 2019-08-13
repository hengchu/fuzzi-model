module Test where

import Control.Monad.Trans.Maybe
import Distribution
import EDSL
import Interp
import Types
import qualified Data.Map.Strict as M
import Data.Bifunctor
import Data.Maybe
import Control.Monad
import Type.Reflection

type DProvenance k   = DistributionProvenance k
type Buckets     k v = M.Map (DProvenance k) [(v, DProfile)]

liftProvenance :: (Monad m, Typeable m, FuzziType a)
               => Fuzzi (m a)
               -> Fuzzi (m (WithDistributionProvenance a))
liftProvenance prog =
  Bind prog (Return . InjectProvenance)

profile :: Int -- ^The number of tries
        -> Fuzzi (MaybeT TracedDist (WithDistributionProvenance a))
        -> IO [(WithDistributionProvenance a, DProfile)]
profile ntimes prog = do
  resultsAndProfiles <- replicateM ntimes ((sampleTraced . runMaybeT . eval) prog)
  return (map (first fromJust) resultsAndProfiles)
