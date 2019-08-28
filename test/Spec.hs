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
import Data.Fuzzi.Types
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

prop_rnmIsDifferentiallyPrivate :: Property
prop_rnmIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 rnmPrivacyTest

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

prop_all :: Property
prop_all = {-label "congruence" prop_symbolCongruence
  .&&. label "rnmLength1" prop_rnmLengthConstraints
  .&&. -}label "rnmDP" prop_rnmIsDifferentiallyPrivate

main :: IO ()
main = do
  putStrLn $
    "\n#######################################"
    ++ "\n#          QuickCheck Tests           #"
    ++ "\n#######################################"

  quickCheckWithResult stdArgs{chatty=True, maxSuccess=100} prop_all >>= print

  putStrLn $
    "\n#######################################"
    ++ "\n#              Unit Tests             #"
    ++ "\n#######################################"
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
