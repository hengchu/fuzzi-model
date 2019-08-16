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

buildMapAux :: (Ord a)
            => [(WithDistributionProvenance a, DProfile)]
            -> M.Map (DistributionProvenance a) [(a, DProfile)]
            -> M.Map (DistributionProvenance a) [(a, DProfile)]
buildMapAux []                m = m
buildMapAux ((k, profile):xs) m =
  buildMapAux xs (M.insertWith (++) (provenance k) [(value k, profile)] m)

profile :: (Ord a)
        => Int -- ^The number of tries
        -> Fuzzi (IdentityT TracedDist (WithDistributionProvenance a))
        -> IO (M.Map (DistributionProvenance a) [(a, DProfile)])
profile ntimes prog = do
  outputs <- replicateM ntimes ((sampleTraced . runIdentityT . eval) prog)
  return (buildMapAux outputs M.empty)
