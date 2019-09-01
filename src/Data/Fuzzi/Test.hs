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

profile :: ( Show (GetProvenance a)
           , Ord (GetProvenance a)
           , HasProvenance a
           , MonadIO m
           , MonadLogger m
           , MonadUnliftIO m
           )
        => Int
        -> Fuzzi (TracedDist a)
        -> m (Buckets a)
profile ntimes prog = do
  outputs <- replicateConcurrently ntimes (liftIO $ (sampleTraced . eval) prog)
  $(logInfo) ("collected " <> pack (show (length outputs)) <> " buckets")
  let bucketsWithKey = buildMapAux outputs M.empty
  $(logInfo) ("bucket distribution: "
              <> (pack . show $ bucketsDistributions bucketsWithKey))
  return bucketsWithKey
  where bucketsDistributions = M.map length

profileIO :: ( Show (GetProvenance a)
             , Ord (GetProvenance a)
             , HasProvenance a
             )
          => Int
          -> Fuzzi (TracedDist a)
          -> IO (Buckets a)
profileIO ntimes prog = runNoLoggingT $ profile ntimes prog

profileIOVerbose :: ( Show (GetProvenance a)
                    , Ord (GetProvenance a)
                    , HasProvenance a
                    )
                 => Int
                 -> Fuzzi (TracedDist a)
                 -> IO (Buckets a)
profileIOVerbose ntimes prog = runStderrLoggingT $ profile ntimes prog

buildMapAux :: ( Ord (GetProvenance a)
               , HasProvenance a
               )
            => [(a, S.Seq (Trace Double))]
            -> Buckets a
            -> Buckets a
buildMapAux []                m = m
buildMapAux ((k, profile):xs) m =
  buildMapAux xs (M.insertWith (++) (getProvenance k) [(k, profile)] m)

symExec :: ( Typeable concreteResult
           , Typeable symbolicResult
           -- , Show symbolicResult
           , HasProvenance concreteResult
           , HasProvenance symbolicResult
           , Matchable
               (DropProvenance concreteResult)
               (DropProvenance symbolicResult))
        => Buckets concreteResult
        -> Fuzzi (Symbolic concreteResult symbolicResult)
        -> [(symbolicResult, SymbolicConstraints)]
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

symExecGeneralize :: ( Typeable concreteResult
                     , Typeable symbolicResult
                     -- , Show symbolicResult
                     , Ord (GetProvenance symbolicResult)
                     , HasProvenance concreteResult
                     , HasProvenance symbolicResult
                     , Matchable
                         (DropProvenance concreteResult)
                         (DropProvenance symbolicResult)
                     )
                  => Buckets concreteResult
                  -> Fuzzi (Symbolic concreteResult symbolicResult)
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
      TestBundle constraints symResult bucket

bucketSymbolicConstraints :: ( Ord (GetProvenance a)
                             , HasProvenance a
                             )
                          => [(a, SymbolicConstraints)]
                          -> M.Map (GetProvenance a)
                                   [(a, SymbolicConstraints)]
                          -> M.Map (GetProvenance a)
                                   [(a, SymbolicConstraints)]
bucketSymbolicConstraints []          m = m
bucketSymbolicConstraints ((k,sc):xs) m =
  bucketSymbolicConstraints xs (M.insertWith (++) (getProvenance k) [(k, sc)] m)

runTestBundle :: ( MonadIO m
                 , MonadLogger m
                 , HasProvenance concreteResult
                 , HasProvenance symbolicResult
                 , SEq (DropProvenance concreteResult) (DropProvenance symbolicResult))
              => Epsilon
              -> TestBundle concreteResult symbolicResult
              -> m (Either SymExecError SolverResult)
runTestBundle eps (TestBundle sc sr bucket) =
  solve sr sc bucket eps

runTests :: ( MonadIO m
            , MonadLogger m
            , HasProvenance concreteResult
            , HasProvenance symbolicResult
            , SEq (DropProvenance concreteResult) (DropProvenance symbolicResult))
         => Epsilon
         -> [TestBundle concreteResult symbolicResult]
         -> m (Either SymExecError [SolverResult])
runTests eps bundles = do
  results <- mapM (runTestBundle eps) bundles
  return (sequence results)
