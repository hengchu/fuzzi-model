import Control.Concurrent.Async
import Control.Monad
import Control.Monad.IO.Class
import Control.Monad.Logger
import Control.Monad.Trans.Identity
import Data.Functor.Identity
import Data.Fuzzi.Distribution
import Data.Fuzzi.EDSL
import Data.Fuzzi.Examples
import Data.Fuzzi.NeighborGen
import Data.Fuzzi.Symbol as S
import Data.Fuzzi.Test
import Data.Fuzzi.Types hiding (or)
import System.Exit
import Test.HUnit (runTestTT, errors, failures)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Map.Strict as M
import qualified Test.HUnit.Base as H
import qualified Z3.Base as Z3

smtTests :: H.Test
smtTests = H.TestList [
  ]

provenanceTests :: H.Test
provenanceTests = H.TestList [
  H.TestCase (H.assert testSmartSumProvenance)
  ]

testSmartSumProvenance :: IO Bool
testSmartSumProvenance = do
  results <- (profileIO 100 . reify)
    (smartSum
      @(TracedDist)
      @_
      @(WithDistributionProvenance [Double])
      [1, 2, 3, 4, 5])
  let k = M.keys results !! 0
  return (M.size results == 1 &&
          length (results M.! k) == 100)

allTests :: H.Test
allTests = H.TestList [
  H.TestLabel "Distribution" provenanceTests,
  H.TestLabel "Symbol" smtTests
  ]

prop_symbolCongruence :: Double -> Double -> Bool
prop_symbolCongruence a b =
  let sa = (fromRational . toRational) a :: S.RealExpr
      sb = (fromRational . toRational) b :: S.RealExpr
  in if a == b
     then sa == sb
     else sa /= sb

prop_rnmLengthConstraints :: SmallList Double -> Property
prop_rnmLengthConstraints (SmallList xs) = monadicIO $ do
  let prog1 = liftProvenance (reify (reportNoisyMax (map (fromRational . toRational) xs)))
  let prog2 = liftProvenance (reify (reportNoisyMax (map (fromRational . toRational) xs)))
  buckets <- run $ profileIO 100 prog1
  case symExecGeneralize buckets prog2 of
    Left  err -> run (print err) >> assert False
    Right constraints -> assert (length buckets == length constraints)

smartSumPrivacyTest :: L1List Double -> Property
smartSumPrivacyTest xs = label ("smartsum input size: " ++ show (length xs)) $ monadicIO $ do
  let xs1 = map (fromRational . toRational) (left xs)
  let xs2 = map (fromRational . toRational) (right xs)
  let prog1 = reify (smartSum xs1) :: Fuzzi (TracedDist (WithDistributionProvenance [Double]))
  let prog2 = reify (smartSum xs2) :: Fuzzi (Symbolic [Double] (WithDistributionProvenance [RealExpr]))
  buckets <- run $ profileIO 100 prog1
  let spec = symExecGeneralize buckets prog2
  case spec of
    Left err -> run (print err) >> assert False
    Right bundles -> do
      results <- run $ runNoLoggingT (runTests 2.0 bundles)
      case results of
        Left err -> run (print err) >> assert False
        Right results' -> do
          run (print results')
          assert (length bundles == length buckets)
          assert (all isOk results')

rnmPrivacyTest :: PairWiseL1List Double -> Property
rnmPrivacyTest xs = label ("rnm input size: " ++ show (length xs)) $ monadicIO $ do
  let xs1   = map (fromRational . toRational) (left xs)
  let xs2   = map (fromRational . toRational) (right xs)
  let prog1 = (liftProvenance . reify) (reportNoisyMax xs1)
  let prog2 = (liftProvenance . reify) (reportNoisyMax xs2)
  buckets <- run $ profileIO 100 prog1
  let spec = symExecGeneralize buckets prog2
  case spec of
    Left err -> run (print err) >> assert False
    Right bundles -> do
      results <- run $ runNoLoggingT (runTests 2.0 bundles)
      case results of
        Left err -> run (print err) >> assert False
        Right results' -> do
          run (print results')
          assert (length bundles == length buckets)
          assert (all isOk results')

rnmNotPrivateTest :: Property
rnmNotPrivateTest = monadicIO $ do
  results <- forM [0..10] $ \_ -> do
    (xs :: PairWiseL1List Double) <- pick (pairWiseL1 1.0)
    let xs1   = map (fromRational . toRational) (left xs)
    let xs2   = map (fromRational . toRational) (right xs)
    let prog1 = (liftProvenance . reify) (reportNoisyMaxBuggy xs1)
    let prog2 = (liftProvenance . reify) (reportNoisyMaxBuggy xs2)
    buckets <- run $ runNoLoggingT (profile 300 prog1)
    let spec = symExecGeneralize buckets prog2
    case spec of
      Left err -> run (print err) >> stop False
      Right bundles -> do
        results <- run $ runNoLoggingT (runTests 2.0 bundles)
        case results of
          Left err -> run (print err) >> stop False
          Right results' -> do
            run (print results')
            case any isFailed results' of
              True -> stop True
              False -> return False
  assert (or results)

prop_rnmIsDifferentiallyPrivate :: Property
prop_rnmIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 rnmPrivacyTest

prop_rnmBuggyIsNotDifferentiallyPrivate :: Property
prop_rnmBuggyIsNotDifferentiallyPrivate = rnmNotPrivateTest

prop_smartSumIsDifferentiallyPrivate :: Property
prop_smartSumIsDifferentiallyPrivate =
  forAll (l1List 1.0) smartSumPrivacyTest

smartSumSpec :: _
smartSumSpec =
  smartSum
  @(SymbolicT ([Double]) Identity)
  @(WithDistributionProvenance RealExpr)
  @(WithDistributionProvenance [RealExpr])

newtype SmallList a = SmallList {
  getSmallList :: [a]
  } deriving (Show, Eq, Ord)

instance Arbitrary a => Arbitrary (SmallList a) where
  arbitrary = do
    len <- elements [1..12]
    xs <- replicateM len arbitrary
    return (SmallList xs)

  shrink xs = SmallList <$> (filter (not . null) . shrink) (getSmallList xs)


main :: IO ()
main = do
  putStrLn $
    "\n#######################################"
    ++ "\n#          QuickCheck Tests           #"
    ++ "\n#######################################"
{-
  quickCheckWithResult
    stdArgs{maxSuccess=20}
    prop_rnmIsDifferentiallyPrivate >>= print
  quickCheckWithResult
    stdArgs{maxSuccess=20}
    prop_rnmBuggyIsNotDifferentiallyPrivate >>= print
-}
  quickCheckWithResult
    stdArgs{maxSuccess=20}
    prop_smartSumIsDifferentiallyPrivate >>= print

  putStrLn $
    "\n#######################################"
    ++ "\n#              Unit Tests             #"
    ++ "\n#######################################"
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
