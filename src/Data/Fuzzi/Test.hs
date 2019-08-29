module Data.Fuzzi.Test where

{- HLINT ignore "Use mapM" -}

import Control.Lens
import Control.Monad.Except
import Control.Monad.IO.Unlift
import Control.Monad.Logger
import Data.Either
import Data.Fuzzi.Distribution
import Data.Fuzzi.EDSL
import Data.Fuzzi.Interp
import Data.Fuzzi.Symbol
import Data.Fuzzi.Types
import Data.Text (pack)
import Debug.Trace
import Type.Reflection
import UnliftIO.Async
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S

data TestBundle concrete symbolic = TestBundle {
  _tbConstraints :: SymbolicConstraints
  , _tbSymbolicResult :: symbolic
  , _tbBucket :: [(concrete, S.Seq (Trace Double))]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''TestBundle

buildMapAux :: (Ord a)
            => [(WithDistributionProvenance a, S.Seq (Trace Double))]
            -> Buckets a
            -> Buckets a
buildMapAux []                m = m
buildMapAux ((k, profile):xs) m =
  buildMapAux xs (M.insertWith (++) (provenance k) [(value k, profile)] m)

buildMapAuxNoProvenance :: (Ord a)
                        => [(a, S.Seq (Trace Double))]
                        -> BucketsNoProvenance a
                        -> BucketsNoProvenance a
buildMapAuxNoProvenance []                m = m
buildMapAuxNoProvenance ((k, profile):xs) m =
  buildMapAuxNoProvenance xs (M.insertWith (++) k [(k, profile)] m)

bucketsDistributions :: (Foldable t)
                     => M.Map a (t b)
                     -> M.Map a Int
bucketsDistributions = M.map length

profile :: (Show a, Ord a, MonadIO m, MonadLogger m, MonadUnliftIO m)
        => Int -- ^The number of tries
        -> Fuzzi (TracedDist (WithDistributionProvenance a))
        -> m (Buckets a)
profile ntimes prog = do
  outputs <- replicateConcurrently ntimes (liftIO $ (sampleTraced . eval) prog)
  $(logInfo) ("collected " <> pack (show (length outputs)) <> " buckets")
  let bucketsWithKey = buildMapAux outputs M.empty
  $(logInfo) ("bucket distribution: "
              <> (pack . show $ bucketsDistributions bucketsWithKey))
  return bucketsWithKey

profileNoProvenance :: (Show a, Ord a, MonadIO m, MonadLogger m, MonadUnliftIO m)
                    => Int -- ^The number of tries
                    -> Fuzzi (TracedDist a)
                    -> m (BucketsNoProvenance a)
profileNoProvenance ntimes prog = do
  outputs <- replicateConcurrently ntimes (liftIO $ (sampleTraced . eval) prog)
  $(logInfo) ("collected " <> pack (show (length outputs)) <> " buckets")
  let bucketsWithKey = buildMapAuxNoProvenance outputs M.empty
  $(logInfo) ("bucket distribution: "
              <> (pack . show $ bucketsDistributions bucketsWithKey))
  return bucketsWithKey

profileIOVerbose :: (Show a, Ord a)
                 => Int -- ^The number of tries
                 -> Fuzzi (TracedDist (WithDistributionProvenance a))
                 -> IO (Buckets a)
profileIOVerbose ntimes prog = runStderrLoggingT $ profile ntimes prog

profileIO :: (Show a, Ord a)
          => Int -- ^The number of tries
          -> Fuzzi (TracedDist (WithDistributionProvenance a))
          -> IO (Buckets a)
profileIO ntimes prog = runNoLoggingT $ profile ntimes prog

profileNoProvenanceIO :: (Show a, Ord a)
                      => Int -- ^The number of tries
                      -> Fuzzi (TracedDist a)
                      -> IO (BucketsNoProvenance a)
profileNoProvenanceIO ntimes prog = runNoLoggingT $ profileNoProvenance ntimes prog

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

symExecNoProvenance :: ( Typeable concreteResult
                       , Typeable symbolicResult
                       , Show symbolicResult
                       , Matchable
                         concreteResult
                         symbolicResult)
                    => BucketsNoProvenance concreteResult
                    -> Fuzzi (Symbolic concreteResult symbolicResult)
                    -> [(symbolicResult, SymbolicConstraints)]
symExecNoProvenance buckets code =
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

bucketSymbolicConstraintsNoProvenance :: (Ord a)
                                      => [(a, SymbolicConstraints)]
                                      -> M.Map a [(a, SymbolicConstraints)]
                                      -> M.Map a [(a, SymbolicConstraints)]
bucketSymbolicConstraintsNoProvenance []          m = m
bucketSymbolicConstraintsNoProvenance ((k,sc):xs) m =
  bucketSymbolicConstraintsNoProvenance xs (M.insertWith (++) k [(k, sc)] m)

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

symExecGeneralizeNoProvenance :: ( Typeable concreteResult
                                 , Typeable symbolicResult
                                 , Show symbolicResult
                                 , Ord symbolicResult
                                 , Matchable
                                   concreteResult
                                   symbolicResult
                     )
                  => BucketsNoProvenance concreteResult
                  -> Fuzzi (Symbolic concreteResult symbolicResult)
                  -> Either SymExecError [TestBundle concreteResult symbolicResult]
symExecGeneralizeNoProvenance concreteBuckets prog = do
  let paths = symExecNoProvenance concreteBuckets prog
  let symBuckets = bucketSymbolicConstraintsNoProvenance paths M.empty
  symBuckets' <- sequence $ M.map
    (\xs -> let a = head (map fst xs)
            in do {sc <- generalize (map snd xs); return (a, sc)})
    symBuckets
  return $ zipWith merge (values concreteBuckets) (values symBuckets')
  where
    values = map snd . M.toList
    merge bucket (symResult, constraints) =
      TestBundle constraints symResult bucket

runTestBundle :: ( MonadIO m
                 , MonadLogger m
                 , SEq concreteResult symbolicResult)
              => Epsilon
              -> TestBundle concreteResult symbolicResult
              -> m (Either SymExecError SolverResult)
runTestBundle eps (TestBundle sc sr bucket) =
  solve sr sc bucket eps

runTests :: ( MonadIO m
            , MonadLogger m
            , SEq concreteResult symbolicResult)
         => Epsilon
         -> [TestBundle concreteResult symbolicResult]
         -> m (Either SymExecError [SolverResult])
runTests eps bundles = do
  results <- mapM (runTestBundle eps) bundles
  return (sequence results)
