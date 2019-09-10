module Data.Fuzzi.Test where

{- HLINT ignore "Use mapM" -}

import Control.Exception
import Control.Lens
import Control.Monad.Cont
import Control.Monad.Except
import Control.Monad.IO.Unlift
import Control.Monad.Logger
import Data.Either
import Data.Fuzzi.Distribution
import Data.Fuzzi.EDSL
import Data.Fuzzi.Interp
import Data.Fuzzi.Symbol
import Data.Fuzzi.Types
import Data.Kind
import Data.Maybe (isJust)
import Data.Text (pack)
import Debug.Trace
import Test.QuickCheck
import Test.QuickCheck.Monadic
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
            -> M.Map (GetProvenance a) [(a, S.Seq (Trace Double))]
            -> M.Map (GetProvenance a) [(a, S.Seq (Trace Double))]
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
  (errorsAndPaths :: [([SymExecError], (Bucket concreteResult, [(symbolicResult, SymbolicConstraints)]))])
    <- mapM
    (\(bucket :: Bucket concreteResult) -> do
         rs <- mapM (go bucket) codes
         let (errors, paths) = partitionEithers rs
         return (errors, (bucket, paths))
    )
    buckets'
  -- maybe log the errors to console?
  let branchErrors   = concatMap fst errorsAndPaths
  let bucketAndPaths = map snd errorsAndPaths
  $(logInfo) ("throwing away " <> pack (show (length branchErrors)) <> " branches")
  return bucketAndPaths
  where
    buckets' = map snd (M.toList buckets)

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
                     , Ord symbolicResult
                     , Show concreteResult
                     , Show symbolicResult
                     , HasProvenance concreteResult
                     , HasProvenance symbolicResult
                     , Show (GetProvenance symbolicResult)
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
                   Epsilon
                -> Int
                -> (Fuzzi (TracedDist concrete),
                    Fuzzi (SymbolicT concrete (LoggingT IO) symbolic))
                -> PropertyM IO ()
expectDPVerbose = expectDP' runStderrLoggingT

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
            Epsilon
         -> Int
         -> (Fuzzi (TracedDist concrete),
             Fuzzi (SymbolicT concrete (NoLoggingT IO) symbolic))
         -> PropertyM IO ()
expectDP = expectDP' runNoLoggingT

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
  forM_ [0..nretries] $ \_ -> do
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
            when (any isFailed results) (stop True)
  Test.QuickCheck.Monadic.assert False

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
                   => Epsilon
                   -> Int
                   -> Int
                   -> Gen (concreteInput, symbolicInput)
                   -> ( concreteInput -> Fuzzi (TracedDist concrete)
                      , symbolicInput -> Fuzzi (SymbolicT concrete (LoggingT IO) symbolic)
                      )
                   -> PropertyM IO ()
expectNotDPVerbose = expectNotDP' runStderrLoggingT

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
            => Epsilon
            -> Int
            -> Int
            -> Gen (concreteInput, symbolicInput)
            -> ( concreteInput -> Fuzzi (TracedDist concrete)
               , symbolicInput -> Fuzzi (SymbolicT concrete (NoLoggingT IO) symbolic)
               )
            -> PropertyM IO ()
expectNotDP = expectNotDP' runNoLoggingT
