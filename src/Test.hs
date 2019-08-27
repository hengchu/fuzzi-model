module Test where

{- HLINT ignore "Use mapM" -}

import Data.Text (pack)
import Control.Lens
import UnliftIO.Async
import Control.Monad
import Control.Monad.Identity
import Control.Monad.Trans.Identity
import Data.Either
import Debug.Trace
import Distribution
import EDSL
import Interp
import Symbol
import Type.Reflection
import Types
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S
import qualified PrettyPrint as PP
import Data.Void
import Control.Monad.Except
import qualified Z3.Base as Z3
import Control.Monad.Logger
import Control.Monad.IO.Unlift

data Result :: * where
  TestSuccess      :: Double -> Result
  TestFailure      :: String -> Result
  TestInconclusive :: Result
  deriving (Show, Eq, Ord)

data TestBundle concrete symbolic = TestBundle {
  _tbConstraints :: SymbolicConstraints
  , _tbSymbolicResult :: symbolic
  , _tbBucket :: [(concrete, S.Seq (Trace Double))]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''TestBundle

liftProvenance :: (Monad m, Typeable m, FuzziType a)
               => Fuzzi (m a)
               -> Fuzzi (m (WithDistributionProvenance a))
liftProvenance prog =
  Bind prog (Return . InjectProvenance)

buildMapAux :: (Ord a)
            => [(WithDistributionProvenance a, S.Seq (Trace Double))]
            -> Buckets a
            -> Buckets a
buildMapAux []                m = m
buildMapAux ((k, profile):xs) m =
  buildMapAux xs (M.insertWith (++) (provenance k) [(value k, profile)] m)

bucketsDistributions :: Buckets a
                     -> M.Map (DProvenance a) Int
bucketsDistributions m = M.map length m

profile :: (Show a, Ord a, MonadIO m, MonadLogger m, MonadUnliftIO m)
        => Int -- ^The number of tries
        -> Fuzzi (TracedDist (WithDistributionProvenance a))
        -> m (Buckets a)
profile ntimes prog = do
  outputs <- replicateConcurrently ntimes (liftIO $ (sampleTraced . eval) prog)
  $(logInfo) ("collected " <> pack (show (length outputs)) <> " buckets")
  let bucketsWithKey = (buildMapAux outputs M.empty)
  $(logInfo) ("bucket distribution: "
              <> (pack . show $ bucketsDistributions bucketsWithKey))
  return bucketsWithKey

profileIO :: (Show a, Ord a)
          => Int -- ^The number of tries
          -> Fuzzi (TracedDist (WithDistributionProvenance a))
          -> IO (Buckets a)
profileIO ntimes prog = runStderrLoggingT $ profile ntimes prog

symExec :: ( Typeable concreteResult
           , Typeable symbolicResult
           , Show symbolicResult
           , Matchable
               concreteResult
               (WithDistributionProvenance symbolicResult))
        => Buckets concreteResult
        -> Fuzzi (Symbolic concreteResult (WithDistributionProvenance symbolicResult))
        -> [(WithDistributionProvenance symbolicResult, SymbolicConstraints)]
symExec buckets code =
  let codes = streamline code
      errorsAndPaths {-:: [([SymExecError], [_])]-} =
        map
        (\(bucket :: Bucket concreteResult) ->
             partitionEithers $
             map (go bucket) codes)
        buckets'
      -- maybe log the errors to console?
      _errors = concatMap fst errorsAndPaths
      paths  = concatMap snd errorsAndPaths
  in paths
  where
    buckets' = map snd (M.toList buckets)
    go bucket code =
      (runIdentity . gatherConstraints bucket (PP.MkSomeFuzzi code) . eval) code

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

symExecGeneralize :: ( Typeable concreteResult
                     , Typeable symbolicResult
                     , Show symbolicResult
                     , Ord symbolicResult
                     , Matchable
                         concreteResult
                         (WithDistributionProvenance symbolicResult)
                     )
                  => Buckets concreteResult
                  -> Fuzzi (Symbolic
                              concreteResult
                              (WithDistributionProvenance symbolicResult))
                  -> Either SymExecError [TestBundle concreteResult symbolicResult]
symExecGeneralize concreteBuckets prog = do
  let paths = symExec concreteBuckets prog
  let symBuckets = bucketSymbolicConstraints paths M.empty
  symBuckets' <- sequence $ M.map
    (\xs -> let a = head (map fst xs)
            in do {sc <- generalize (map snd xs); return (a, sc)})
    symBuckets
  return $ zipWith merge (values concreteBuckets) (values symBuckets')
  where
    values = map snd . M.toList
    merge bucket (symResult, constraints) =
      TestBundle constraints (value symResult) bucket

runTestBundle :: (MonadIO m, MonadLogger m, SEq concreteResult symbolicResult)
              => Epsilon
              -> TestBundle concreteResult symbolicResult
              -> m (Either SymExecError SolverResult)
runTestBundle eps (TestBundle sc sr bucket) =
  solve sr sc bucket eps

runTests :: (SEq concreteResult symbolicResult)
         => Epsilon
         -> [TestBundle concreteResult symbolicResult]
         -> IO (Either SymExecError [SolverResult])
runTests eps bundles = runStderrLoggingT $ do
  results <- mapM (runTestBundle eps) bundles
  return (sequence results)
