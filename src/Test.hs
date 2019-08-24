module Test where

{- HLINT ignore "Use mapM" -}

import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans.Identity
import Distribution
import Symbol
import EDSL
import Interp
import Type.Reflection
import Types
import qualified Data.Map.Strict as M
import qualified PrettyPrint as PP

liftProvenance :: (Monad m, Typeable m, FuzziType a)
               => Fuzzi (m a)
               -> Fuzzi (m (WithDistributionProvenance a))
liftProvenance prog =
  Bind prog (Return . InjectProvenance)

buildMapAux :: (Ord a)
            => [(WithDistributionProvenance a, DProfile)]
            -> Buckets a
            -> Buckets a
buildMapAux []                m = m
buildMapAux ((k, profile):xs) m =
  buildMapAux xs (M.insertWith (++) (provenance k) [(value k, profile)] m)

profile :: (Ord a)
        => Int -- ^The number of tries
        -> Fuzzi (IdentityT TracedDist (WithDistributionProvenance a))
        -> IO (Buckets a)
profile ntimes prog = do
  outputs <- replicateM ntimes ((sampleTraced . runIdentityT . eval) prog)
  return (buildMapAux outputs M.empty)

symExec :: (Typeable r, Typeable a)
        => Fuzzi (SymbolicT r Identity (WithDistributionProvenance a))
        -> Either SymExecError [(WithDistributionProvenance a, SymbolicConstraints)]
symExec code =
  let codes = streamline code
  in sequence $ map (\c -> (runIdentity . gatherConstraints [] (PP.MkSomeFuzzi c) . eval) c) codes

bucketSymbolicConstraints :: (Ord a)
                          => [(WithDistributionProvenance a, SymbolicConstraints)]
                          -> M.Map (DistributionProvenance a)
                                   [( WithDistributionProvenance a
                                    , SymbolicConstraints)
                                   ]
                          -> M.Map (DistributionProvenance a)
                                   [( WithDistributionProvenance a
                                    , SymbolicConstraints)
                                   ]
bucketSymbolicConstraints []          m = m
bucketSymbolicConstraints ((k,sc):xs) m =
  bucketSymbolicConstraints xs (M.insertWith (++) (provenance k) [(k, sc)] m)

symExecGeneralize :: (Typeable r, Typeable a, Ord a)
                  => Fuzzi (SymbolicT r Identity (WithDistributionProvenance a))
                  -> Either SymExecError
                            [( WithDistributionProvenance a
                             , SymbolicConstraints)
                            ]
symExecGeneralize prog = do
  paths <- symExec prog
  let buckets  = bucketSymbolicConstraints paths M.empty
  buckets' <- sequence $ M.map
    (\xs -> let a = head (map fst xs)
            in do {sc <- generalize (map snd xs); return (a, sc)})
    buckets
  return $ (map snd . M.toList) buckets'
