module Test where

import Control.Monad
import Control.Monad.Trans.Identity
import Distribution
import EDSL
import Interp
import Type.Reflection
import Types
import qualified Data.Map.Strict as M

type DProvenance k   = DistributionProvenance k
type Buckets     k v = M.Map (DProvenance k) [(v, DProfile)]

liftProvenance :: (Monad m, Typeable m, FuzziType a)
               => Fuzzi (m a)
               -> Fuzzi (m (WithDistributionProvenance a))
liftProvenance prog =
  Bind prog (Return . InjectProvenance)

profile :: Int -- ^The number of tries
        -> Fuzzi (IdentityT TracedDist (WithDistributionProvenance a))
        -> IO [(WithDistributionProvenance a, DProfile)]
profile ntimes prog = replicateM ntimes ((sampleTraced . runIdentityT . eval) prog)
