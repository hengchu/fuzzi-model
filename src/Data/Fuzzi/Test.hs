{-# OPTIONS_HADDOCK prune #-}

{-|
Module: Data.Fuzzi.Test
Description: Test combinators that checks DP/non-DP properties.
-}
module Data.Fuzzi.Test (
  -- ** A type that groups symbolic return values, constraints, and concrete sampled traces together
  TestBundle(..)
  , constraints
  , symbolicResult
  , bucket
  -- *** Sample concrete probabilistic traces from a program
  , profile
  , profileIO
  , profileIOVerbose
  -- *** Top-level test combinators for testing DP/non-DP properties
  , expectDP
  , expectDPRosette
  , expectDPVerbose
  , expectDPRosetteVerbose
  , expectNotDP
  , expectNotDPVerbose
  , expectNotDPRosette
  , expectNotDPRosetteVerbose

  , symExecGeneralize
  ) where

{- HLINT ignore "Use mapM" -}

-- import Control.Exception
import Control.Lens
import Control.Monad.Catch
import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.IO.Unlift
import Data.Either
import Data.Fuzzi.Distribution
import Data.Fuzzi.EDSL
import Data.Fuzzi.Interp
import Data.Fuzzi.Logging
import Data.Fuzzi.Rosette hiding (Bucket, Epsilon, isOk, isFailed)
import Data.Fuzzi.Symbol
import Data.Fuzzi.Types
import Data.Kind
import Data.Maybe (isJust)
import Data.Text (pack)
import Data.Time.Clock
import Test.QuickCheck
import Test.QuickCheck.Monadic
import Type.Reflection
import qualified Data.Fuzzi.PrettyPrint as PP
import qualified Data.Fuzzi.Rosette as R
import qualified Data.Map.Strict as M
import qualified Data.Sequence as S
import qualified Data.Set as SS

-- | A test bundle is a grouped symbolic return value grouped with matching
-- concrete return values and their sampled traces.
data TestBundle concrete symbolic = TestBundle {
  _tbConstraints :: SymbolicConstraints
  , _tbSymbolicResult :: symbolic
  , _tbBucket :: [(concrete, S.Seq AnyTrace)]
  } deriving (Show, Eq, Ord)

makeLensesWith abbreviatedFields ''TestBundle

-- | Sample 'ntimes' traces from the given program 'prog'.
profile :: ( Show (GetProvenance a)
           , Ord (GetProvenance a)
           , HasProvenance a
           , MonadIO m
           , MonadLogger m
           , MonadUnliftIO m
           )
        => Int -- ^ The number of traces to sample
        -> Fuzzi (TracedDist a) -- ^ The program to sample from
        -> m (Buckets a)
profile ntimes prog = do
  outputs <- replicateM ntimes (liftIO $ run prog `catch` (\(_ :: AbortException) -> return Nothing))
  let Just outputs' = sequence (filter isJust outputs)
  $(logInfo) ("collected " <> pack (show (length outputs')) <> " buckets")
  let bucketsWithKey = buildMapAux outputs' M.empty
  $(logInfo) ("bucket distribution: "
              <> (pack . show $ bucketsDistributions bucketsWithKey))
  return bucketsWithKey
  where bucketsDistributions = M.map length
        run prog = do
          r <- (sampleTraced . eval) prog
          return (Just r)

-- | Same as 'profile', but monomorphize the monad to 'IO'.
profileIO :: ( Show (GetProvenance a)
             , Ord (GetProvenance a)
             , HasProvenance a
             )
          => Int -- ^ The number of traces to sample
          -> Fuzzi (TracedDist a) -- ^ The program to sample from
          -> IO (Buckets a)
profileIO ntimes prog = runNoLoggingT $ profile ntimes prog

-- | Same as 'profile', but monomorphize the monad to 'IO', and enable verbose logging.
profileIOVerbose :: ( Show (GetProvenance a)
                    , Ord (GetProvenance a)
                    , HasProvenance a
                    )
                 => Int -- ^ The number of traces to sample
                 -> Fuzzi (TracedDist a) -- ^ The program to sample from
                 -> IO (Buckets a)
profileIOVerbose ntimes prog = runStdoutColoredLoggingT $ profile ntimes prog

buildMapAux :: ( Ord (GetProvenance a)
               , HasProvenance a
               )
            => [(a, S.Seq AnyTrace)]
            -> M.Map (GetProvenance a) [(a, S.Seq AnyTrace)]
            -> M.Map (GetProvenance a) [(a, S.Seq AnyTrace)]
buildMapAux []                m = m
buildMapAux ((k, profile):xs) m =
  buildMapAux xs (M.insertWith (++) (getProvenance k) [(k, profile)] m)

symExec :: forall m concreteResult symbolicResult.
           ( Typeable concreteResult
           , Typeable symbolicResult
           , Typeable m
           , Show concreteResult
           , Show symbolicResult
           , Show (GetProvenance symbolicResult)
           , Ord (GetProvenance concreteResult)
           , Show (GetProvenance concreteResult)
           , HasProvenance concreteResult
           , HasProvenance symbolicResult
           , Matchable concreteResult symbolicResult
           , MonadLogger m
           , MonadIO m
           , Eq symbolicResult
           )
        => Buckets concreteResult
        -> Fuzzi (SymbolicT concreteResult m symbolicResult)
        -> m [(Bucket concreteResult, [(symbolicResult, SymbolicConstraints)])]
symExec buckets code = do
  let codes = streamline code
  (errorsAndPaths :: [([SymExecError], (GetProvenance concreteResult, Bucket concreteResult, [(symbolicResult, SymbolicConstraints)]))])
    <- mapM
    (\(prov, bucket :: Bucket concreteResult) -> do
         rs <- mapM (go bucket) codes
         let (errors, paths) = partitionEithers rs
         return (errors, (prov, bucket, paths))
    )
    (M.toList buckets)
  -- maybe log the errors to console?
  let _branchErrors  = concatMap fst errorsAndPaths
  let bucketAndPaths = map snd errorsAndPaths

  let successfulProvenances = SS.fromList $ map (view _1) bucketAndPaths
  let originalProvenances = SS.fromList $ M.keys buckets
  let droppedProvenances = originalProvenances SS.\\ successfulProvenances

  forM_ (SS.toList droppedProvenances) $ \p -> do
    $(logWarn) "dropped this provenance:"
    $(logWarn) (pack (show p))

  return $ map (\a -> (a ^. _2, a ^. _3)) bucketAndPaths
  where
    go :: Bucket concreteResult
       -> Fuzzi (SymbolicT concreteResult m symbolicResult)
       -> m (Either SymExecError (symbolicResult, SymbolicConstraints))
    go bucket code =
      (gatherConstraints bucket (PP.MkSomeFuzzi code) . eval) code

symExecGeneralize :: forall m concreteResult symbolicResult.
                     ( Typeable concreteResult
                     , Typeable symbolicResult
                     , Typeable m
                     , Ord (GetProvenance symbolicResult)
                     , Ord (GetProvenance concreteResult)
                     , Ord symbolicResult
                     , Show concreteResult
                     , Show symbolicResult
                     , HasProvenance concreteResult
                     , HasProvenance symbolicResult
                     , Show (GetProvenance symbolicResult)
                     , Show (GetProvenance concreteResult)
                     , Matchable concreteResult symbolicResult
                     , MonadIO m
                     , MonadLogger m
                     )
                  => Buckets concreteResult
                  -> Fuzzi (SymbolicT concreteResult m symbolicResult)
                  -> m (Either SymExecError [TestBundle concreteResult symbolicResult])
symExecGeneralize concreteBuckets prog = runExceptT $ do
  bucketAndPaths <- lift $ symExec concreteBuckets prog
  let symBuckets = for bucketAndPaths $ \(bucket, paths) ->
        (bucket, bucketSymbolicConstraints paths M.empty)

  buckets <-
    forM symBuckets $ \(bucket, thisSymBuckets) ->
      forM (map snd (M.toList thisSymBuckets)) $ \symValsAndConstraints -> do
        let symVals = map fst symValsAndConstraints
        let constraints = map snd symValsAndConstraints
        genConstraints <- liftEither (generalize constraints)
        return (TestBundle genConstraints (head symVals) bucket)

  return (concat buckets)

  where for = flip map

bucketSymbolicConstraints :: ( Ord (GetProvenance symbolicResult)
                             , HasProvenance symbolicResult
                             )
                          => [(symbolicResult, SymbolicConstraints)]
                          -> M.Map (GetProvenance symbolicResult)
                                   [(symbolicResult, SymbolicConstraints)]
                          -> M.Map (GetProvenance symbolicResult)
                                   [(symbolicResult, SymbolicConstraints)]
bucketSymbolicConstraints []          m = m
bucketSymbolicConstraints ((k,sc):xs) m =
  bucketSymbolicConstraints xs (M.insertWith (++) (getProvenance k) [(k, sc)] m)

runTestBundle :: ( MonadIO m
                 , MonadLogger m
                 , HasProvenance concreteResult
                 , HasProvenance symbolicResult
                 , Show concreteResult
                 , Show symbolicResult
                 , Show (DropProvenance concreteResult)
                 , Show (DropProvenance symbolicResult)
                 , SEq (DropProvenance concreteResult) (DropProvenance symbolicResult))
              => Epsilon
              -> TestBundle concreteResult symbolicResult
              -> m (Either SymExecError (TestResult concreteResult symbolicResult))
runTestBundle eps (TestBundle sc sr bucket) =
  solve sr sc bucket eps

runTests :: ( MonadIO m
            , MonadLogger m
            , HasProvenance concreteResult
            , HasProvenance symbolicResult
            , Show concreteResult
            , Show symbolicResult
            , Show (DropProvenance concreteResult)
            , Show (DropProvenance symbolicResult)
            , SEq (DropProvenance concreteResult) (DropProvenance symbolicResult))
         => Epsilon
         -> [TestBundle concreteResult symbolicResult]
         -> m (Either SymExecError [TestResult concreteResult symbolicResult])
runTests eps bundles = do
  forM_ bundles $ \bundle -> do
    $(logInfo) "symbolic result..."
    $(logInfo) (pack (show $ _tbSymbolicResult bundle))
    $(logInfo) "constraints..."
    $(logInfo) (pack (show $ _tbConstraints bundle))
  results <- mapM (runTestBundle eps) bundles
  return (sequence results)

type IOConstraints m = (MonadIO m, MonadLogger m, MonadUnliftIO m)
type ConstraintsWithProvenance (c :: * -> Constraint) a =
  (c a, c (GetProvenance a), c (DropProvenance a))

expectDP' :: ( IOConstraints m
             , Typeable m
             , Typeable concrete
             , Typeable symbolic
             , Matchable concrete symbolic
             , HasProvenance concrete
             , HasProvenance symbolic
             , ConstraintsWithProvenance Ord concrete
             , ConstraintsWithProvenance Ord symbolic
             , ConstraintsWithProvenance Show concrete
             , ConstraintsWithProvenance Show symbolic
             , SEq (DropProvenance concrete) (DropProvenance symbolic)
             )
         => (forall a. m a -> IO a)
         -> Epsilon
         -> Int
         -> ( Fuzzi (TracedDist concrete)
            , Fuzzi (SymbolicT concrete m symbolic)
            )
         -> PropertyM IO ()
expectDP' logHandler eps ntrials (left, right) = do
  success <- (run . logHandler) $ do
    buckets <- profile ntrials left
    spec <- symExecGeneralize buckets right
    case spec of
      Left err -> do
        liftIO $ print err
        return False
      Right bundles -> do
        errorOrResults <- runTests eps bundles
        case errorOrResults of
          Left  err     -> do
            liftIO $ print err
            return False
          Right results -> do
            liftIO $ print $ map (view solverResult) results
            return (all isOk results)
  Test.QuickCheck.Monadic.assert success

expectDPRosette' :: ( IOConstraints m
                    , MonadMask m
                    , Typeable m
                    , Typeable concrete
                    , Typeable symbolic
                    , HasProvenance concrete
                    , ConstraintsWithProvenance Ord concrete
                    , ConstraintsWithProvenance Show concrete
                    , Show symbolic
                    , SEq concrete symbolic
                    )
                 => (forall a. m a -> IO a)
                 -> Epsilon
                 -> Int
                 -> ( Fuzzi (TracedDist concrete)
                    , Fuzzi (RosetteT m symbolic)
                    )
                 -> PropertyM IO ()
expectDPRosette' logHandler eps ntrials (left, right) = do
  results <- (run . logHandler) $ do
    buckets <- profile ntrials left
    check eps (map snd $ M.toList buckets) right
  run (print results)
  Test.QuickCheck.Monadic.assert (all R.isOk results)

expectNotDPRosette' :: ( IOConstraints m
                       , MonadMask m
                       , Typeable m
                       , Typeable concrete
                       , Typeable symbolic
                       , HasProvenance concrete
                       , ConstraintsWithProvenance Ord concrete
                       , ConstraintsWithProvenance Show concrete
                       , Show concreteInput
                       , Show symbolicInput
                       , Show symbolic
                       , SEq concrete symbolic
                       )
                    => (forall a. m a -> IO a)
                    -> Epsilon
                    -> Int
                    -> Int
                    -> Gen (concreteInput, symbolicInput)
                    -> ( concreteInput -> Fuzzi (TracedDist concrete)
                       , symbolicInput -> Fuzzi (RosetteT m symbolic)
                       )
                    -> PropertyM IO ()
expectNotDPRosette' logHandler eps ntrials nretries gen (left, right) = do
  !startTime <- run getCurrentTime
  forM_ [0..nretries] $ \iter -> do
    (concreteInput, symbolicInput) <- pick gen
    buckets <- run . logHandler $ profile ntrials (left concreteInput)
    results <- run . logHandler $ check eps (map snd $ M.toList buckets) (right symbolicInput)
    run (print results)
    when (any R.isFailed results) $ do
      !endTime <- run getCurrentTime
      let dur = endTime `diffUTCTime` startTime
      let durStr = show dur
      let iterStr = show (iter + 1)
      run . putStrLn $ "found a bug in " ++ durStr ++ ", " ++ iterStr ++ " iterations"
      stop True
  Test.QuickCheck.Monadic.assert False

-- | Test a program using an *experimental* (probably very buggy!) optimized
-- symbolic execution engine (based on Rosette's type-based state-merging
-- algorithm), expecting the program to be differentially private.
expectDPRosette :: ( Typeable concrete
                    , Typeable symbolic
                    , HasProvenance concrete
                    , ConstraintsWithProvenance Ord concrete
                    , ConstraintsWithProvenance Show concrete
                    , Show symbolic
                    , SEq concrete symbolic
                    )
                 => Epsilon -- ^ The expected epsilon privacy parameter
                 -> Int -- ^ The number of concrete traces to sample in this test
                 -> ( Fuzzi (TracedDist concrete)
                    , Fuzzi (RosetteT (LoggingT IO) symbolic)
                    ) -- ^ The pair of programs, one monomorphized for concrete execution, and the other one monomorphized for symbolic execution, and both have been partially applied on their respective inputs
                 -> PropertyM IO ()
expectDPRosette = expectDPRosette' runStdoutColoredLoggingWarnT

-- | Test a program using an *experimental* (probably very buggy!) optimized
-- symbolic execution engine (based on Rosette's type-based state-merging
-- algorithm), expecting the program to be differentially private, while
-- enabling verbose logging.
expectDPRosetteVerbose :: ( Typeable concrete
                          , Typeable symbolic
                          , HasProvenance concrete
                          , ConstraintsWithProvenance Ord concrete
                          , ConstraintsWithProvenance Show concrete
                          , Show symbolic
                          , SEq concrete symbolic
                          )
                       => Epsilon -- ^ The expected epsilon privacy parameter
                       -> Int -- ^ The number of concrete traces to sample in this test
                       -> ( Fuzzi (TracedDist concrete)
                          , Fuzzi (RosetteT (LoggingT IO) symbolic)
                          ) -- ^ The pair of programs, one monomorphized for concrete execution, and the other one monomorphized for symbolic execution, and both have been partially applied on their respective inputs
                       -> PropertyM IO ()
expectDPRosetteVerbose = expectDPRosette' (runStdoutColoredLoggingAboveLevelT LevelInfo)

-- | Test a program, expecting the program to be differentially private, while
-- enabling verbose logging.
expectDPVerbose :: ( Typeable concrete
                   , Typeable symbolic
                   , Matchable concrete symbolic
                   , HasProvenance concrete
                   , HasProvenance symbolic
                   , ConstraintsWithProvenance Ord concrete
                   , ConstraintsWithProvenance Ord symbolic
                   , ConstraintsWithProvenance Show concrete
                   , ConstraintsWithProvenance Show symbolic
                   , SEq (DropProvenance concrete) (DropProvenance symbolic)) =>
                   Epsilon -- ^ The expected epsilon privacy parameter
                -> Int -- ^ The number of concrete traces to sample in this test
                -> (Fuzzi (TracedDist concrete),
                    Fuzzi (SymbolicT concrete (LoggingT IO) symbolic)) -- ^ The pair of programs, one monomorphized for concrete execution, and the other one monomorphized for symbolic execution, and both have been partially applied on their respective inputs
                -> PropertyM IO ()
expectDPVerbose = expectDP' runStdoutColoredLoggingT

-- | Test a program, expecting the program to be differentially private.
expectDP :: ( Typeable concrete
            , Typeable symbolic
            , Matchable concrete symbolic
            , HasProvenance concrete
            , HasProvenance symbolic
            , ConstraintsWithProvenance Ord concrete
            , ConstraintsWithProvenance Ord symbolic
            , ConstraintsWithProvenance Show concrete
            , ConstraintsWithProvenance Show symbolic
            , SEq (DropProvenance concrete) (DropProvenance symbolic)) =>
            Epsilon -- ^ The expected epsilon privacy parameter
         -> Int -- ^ The number of concrete traces to sample in this test
         -> (Fuzzi (TracedDist concrete),
             Fuzzi (SymbolicT concrete (LoggingT IO) symbolic)) -- ^ The pair of programs, one monomorphized for concrete execution, and the other one monomorphized for symbolic execution, and both have been partially applied on their respective inputs
         -> PropertyM IO ()
expectDP = expectDP' runStdoutColoredLoggingWarnT

expectNotDP' :: ( IOConstraints m
                , Typeable m
                , Typeable concrete
                , Typeable symbolic
                , Matchable concrete symbolic
                , HasProvenance concrete
                , HasProvenance symbolic
                , ConstraintsWithProvenance Ord concrete
                , ConstraintsWithProvenance Ord symbolic
                , ConstraintsWithProvenance Show concrete
                , ConstraintsWithProvenance Show symbolic
                , Show concreteInput
                , Show symbolicInput
                , SEq (DropProvenance concrete) (DropProvenance symbolic)
                )
             => (forall a. m a -> IO a)
             -> Epsilon
             -> Int
             -> Int
             -> Gen (concreteInput, symbolicInput)
             -> ( concreteInput -> Fuzzi (TracedDist concrete)
                , symbolicInput -> Fuzzi (SymbolicT concrete m symbolic)
                )
             -> PropertyM IO ()
expectNotDP' logHandler eps ntrials nretries gen (left, right) = do
  !startTime <- run getCurrentTime
  forM_ [0..nretries] $ \iter -> do
    (concreteInput, symbolicInput) <- pick gen
    buckets <- run . logHandler $ profile ntrials (left concreteInput)
    spec <- run . logHandler $ symExecGeneralize buckets (right symbolicInput)
    case spec of
      Left err -> do
        liftIO $ print err
        stop False
      Right bundles -> do
        errorOrResults <- run . logHandler $ runTests eps bundles
        case errorOrResults of
          Left err -> do
            liftIO $ print err
            stop False
          Right results -> do
            liftIO $ print $ map (view solverResult) results
            when (any isFailed results) $ do
              !endTime <- run getCurrentTime
              let dur = endTime `diffUTCTime` startTime
              let durStr = show dur
              let iterStr = show (iter + 1)
              run . putStrLn $ "found a bug in " ++ durStr ++ ", " ++ iterStr ++ " iterations"
              stop True
  Test.QuickCheck.Monadic.assert False

-- | Test a program, expecting the program to *NOT* be epsilon-differentially
-- private. This test passes only if the program under test is detected faulty
-- within a given number of trials, and fails if no fault is detected before
-- giving up. This runs the test while also turning on verbose logging.
expectNotDPVerbose :: ( Typeable concrete
                      , Typeable symbolic
                      , Matchable concrete symbolic
                      , HasProvenance concrete
                      , HasProvenance symbolic
                      , ConstraintsWithProvenance Ord concrete
                      , ConstraintsWithProvenance Ord symbolic
                      , ConstraintsWithProvenance Show concrete
                      , ConstraintsWithProvenance Show symbolic
                      , Show concreteInput
                      , Show symbolicInput
                      , SEq (DropProvenance concrete) (DropProvenance symbolic)
                      )
                   => Epsilon -- ^ The epsilon privacy parameter that the program is expected to violate
                   -> Int -- ^ The number of concrete sampled traces to use per trial
                   -> Int -- ^ The number of of trials to run before giving up
                   -> Gen (concreteInput, symbolicInput) -- ^ The generator for neighboring inputs
                   -> ( concreteInput -> Fuzzi (TracedDist concrete)
                      , symbolicInput -> Fuzzi (SymbolicT concrete (LoggingT IO) symbolic)
                      ) -- ^ The program to test, with one of them monomorphized for concrete execution, and the other one monomorphized for symbolic execution
                   -> PropertyM IO ()
expectNotDPVerbose = expectNotDP' runStdoutColoredLoggingT

-- | Test a program, expecting the program to *NOT* be epsilon-differentially
-- private. This test passes only if the program under test is detected faulty
-- within a given number of trials, and fails if no fault is detected before
-- giving up.
expectNotDP :: ( Typeable concrete
               , Typeable symbolic
               , Matchable concrete symbolic
               , HasProvenance concrete
               , HasProvenance symbolic
               , ConstraintsWithProvenance Ord concrete
               , ConstraintsWithProvenance Ord symbolic
               , ConstraintsWithProvenance Show concrete
               , ConstraintsWithProvenance Show symbolic
               , Show concreteInput
               , Show symbolicInput
               , SEq (DropProvenance concrete) (DropProvenance symbolic)
               )
            => Epsilon -- ^ The epsilon privacy parameter that the program is expected to violate
            -> Int -- ^ The number of concrete sampled traces to use per trial
            -> Int -- ^ The number of of trials to run before giving up
            -> Gen (concreteInput, symbolicInput) -- ^ The generator for neighboring inputs
            -> ( concreteInput -> Fuzzi (TracedDist concrete)
               , symbolicInput -> Fuzzi (SymbolicT concrete (LoggingT IO) symbolic)
               ) -- ^ The program to test, with one of them monomorphized for concrete execution, and the other one monomorphized for symbolic execution
            -> PropertyM IO ()
expectNotDP = expectNotDP' runStdoutColoredLoggingWarnT

-- | Test a program, using an *experimental* (probably very buggy!) optimized
-- symbolic execution engine (based on Rosette's type-based state-merging
-- algorithm), expecting the program to *NOT* be epsilon-differentially
-- private. This test passes only if the program under test is detected faulty
-- within a given number of trials, and fails if no fault is detected before
-- giving up.
expectNotDPRosette :: ( Typeable concrete
                      , Typeable symbolic
                      , HasProvenance concrete
                      , ConstraintsWithProvenance Ord concrete
                      , ConstraintsWithProvenance Show concrete
                      , Show concreteInput
                      , Show symbolicInput
                      , Show symbolic
                      , SEq concrete symbolic
                      )
                   => Epsilon -- ^ The epsilon privacy parameter that the program is expected to violate
                   -> Int -- ^ The number of concrete sampled traces to use per trial
                   -> Int -- ^ The number of of trials to run before giving up
                   -> Gen (concreteInput, symbolicInput) -- ^ The generator for neighboring inputs
                   -> ( concreteInput -> Fuzzi (TracedDist concrete)
                      , symbolicInput -> Fuzzi (RosetteT (LoggingT IO) symbolic)
                      ) -- ^ The program to test, with one of them monomorphized for concrete execution, and the other one monomorphized for symbolic execution
                   -> PropertyM IO ()
expectNotDPRosette = expectNotDPRosette' runStdoutColoredLoggingWarnT

-- | Test a program, using an *experimental* (probably very buggy!) optimized
-- symbolic execution engine (based on Rosette's type-based state-merging
-- algorithm), expecting the program to *NOT* be epsilon-differentially
-- private. This test passes only if the program under test is detected faulty
-- within a given number of trials, and fails if no fault is detected before
-- giving up. This runs the test while turning on verbose logging.
expectNotDPRosetteVerbose :: ( Typeable concrete
                             , Typeable symbolic
                             , HasProvenance concrete
                             , ConstraintsWithProvenance Ord concrete
                             , ConstraintsWithProvenance Show concrete
                             , Show concreteInput
                             , Show symbolicInput
                             , Show symbolic
                             , SEq concrete symbolic
                             )
                          => Epsilon -- ^ The epsilon privacy parameter that the program is expected to violate
                          -> Int -- ^ The number of concrete sampled traces to use per trial
                          -> Int -- ^ The number of of trials to run before giving up
                          -> Gen (concreteInput, symbolicInput)
                          -> ( concreteInput -> Fuzzi (TracedDist concrete)
                             , symbolicInput -> Fuzzi (RosetteT (LoggingT IO) symbolic)
                             ) -- ^ The program to test, with one of them monomorphized for concrete execution, and the other one monomorphized for symbolic execution
                          -> PropertyM IO ()
expectNotDPRosetteVerbose = expectNotDPRosette' (runStdoutColoredLoggingAboveLevelT LevelInfo)
