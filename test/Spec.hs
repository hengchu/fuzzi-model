import Control.Monad
import Control.Monad.Logger
import Data.Fuzzi.Distribution
import Data.Fuzzi.EDSL
import Data.Fuzzi.Examples
import Data.Fuzzi.NeighborGen
import Data.Fuzzi.Symbol as S
import Data.Fuzzi.Test
import Data.Fuzzi.Types hiding (or)
import Data.Maybe
import System.Exit
import System.Posix.Env
import Test.HUnit (runTestTT, errors, failures)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Map.Strict as M
import qualified Test.HUnit.Base as H

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
      @TracedDist
      @(WithDistributionProvenance Double)
      [1, 2, 3, 4, 5])
  let k = head (M.keys results)
  return (M.size results == 1 &&
          length (results M.! k) == 100)

allTests :: H.Test
allTests = H.TestList [
  H.TestLabel "Distribution" provenanceTests,
  H.TestLabel "Symbol" smtTests
  ]

prop_symbolCongruence :: Double -> Double -> Bool
prop_symbolCongruence a b =
  let sa = realToFrac a :: S.RealExpr
      sb = realToFrac b :: S.RealExpr
  in if a == b
     then sa == sb
     else sa /= sb

prop_rnmLengthConstraints :: SmallList Double -> Property
prop_rnmLengthConstraints (SmallList xs) = monadicIO $ do
  let prog1 = reify (reportNoisyMax (map realToFrac xs))
  let prog2 = reify (reportNoisyMax (map realToFrac xs))
  buckets <- run $ profileIO 100 prog1
  spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
  case spec of
    Left  err -> run (print err) >> assert False
    Right constraints -> assert (length buckets == length constraints)

smartSumPrivacyTest :: L1List Double -> Property
smartSumPrivacyTest xs =
  label ("smartsum input size: " ++ show (length xs)) $
  monadicIO $
    expectDP
      2.0
      500
      ( reify . smartSum . map realToFrac $ left xs
      , reify . smartSum . map realToFrac $ right xs
      )

rnmPrivacyTest :: PairWiseL1List Double -> Property
rnmPrivacyTest xs = label ("rnm input size: " ++ show (length xs)) $
  monadicIO $
    expectDP
      2.0
      500
      ( reify . reportNoisyMax . map realToFrac $ left xs
      , reify . reportNoisyMax . map realToFrac $ right xs
      )

rnmGapPrivacyTest :: PairWiseL1List Double -> Property
rnmGapPrivacyTest xs = label ("rnmGap input size: " ++ show (length xs)) $
  monadicIO $
    expectDP
      2.0
      500
      ( reify . reportNoisyMaxGap . map realToFrac $ left xs
      , reify . reportNoisyMaxGap . map realToFrac $ right xs
      )


rnmNotPrivateTest :: Property
rnmNotPrivateTest = monadicIO $
  expectNotDP
    2.0
    300
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . reportNoisyMaxBuggy . map realToFrac
    , reify . reportNoisyMaxBuggy . map realToFrac
    ) -- code duplication because of let bindings monomorphises the types

smartSumNotPrivateTest :: Property
smartSumNotPrivateTest = monadicIO $
  expectNotDP
    2.0
    500
    50
    (l1List 1.0 >>= \(xs :: L1List Double) -> return (left xs, right xs))
    ( reify . smartSumBuggy . map realToFrac
    , reify . smartSumBuggy . map realToFrac
    )

sparseVectorPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorPrivacyTest xs =
  label ("sparseVector input length: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . (\xs -> sparseVector xs 2 0) . map realToFrac $ left xs
      , reify . (\xs -> sparseVector xs 2 0) . map realToFrac $ left xs
      )

sparseVectorGapPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorGapPrivacyTest xs =
  label ("sparseVectorGap input length: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . (\xs -> sparseVectorGap xs 2 0) . map realToFrac $ left xs
      , reify . (\xs -> sparseVectorGap xs 2 0) . map realToFrac $ left xs
      )

sparseVectorNotPrivateTest :: Property
sparseVectorNotPrivateTest = monadicIO $
  expectNotDP
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorBuggy xs 2 0) . map realToFrac
    , reify . (\xs -> sparseVectorBuggy xs 2 0) . map realToFrac
    )

privTreePrivacyTest :: BagList Double -> Property
privTreePrivacyTest xs = monadicIO $
  expectDP
    k_PT_EPSILON
    500
    ( reify . privTree . map realToFrac $ left xs
    , reify . privTree . map realToFrac $ right xs
    )

privTreeBuggyNotPrivateTest :: Property
privTreeBuggyNotPrivateTest = monadicIO $
  expectNotDP
    k_PT_EPSILON
    100
    20
    (bagListSmall (0, 1) 1 >>= \(xs :: BagList Double) -> return (left xs, right xs))
    ( reify . privTreeBuggy . map realToFrac
    , reify . privTreeBuggy . map realToFrac
    )

privTreeBuggy2NotPrivateTest :: Property
privTreeBuggy2NotPrivateTest = monadicIO $
  expectNotDP
    k_PT_EPSILON
    100
    20
    (bagListSmall (0, 1) 1 >>= \(xs :: BagList Double) -> return (left xs, right xs))
    ( reify . privTreeBuggy2 . map realToFrac
    , reify . privTreeBuggy2 . map realToFrac
    )

simpleCountPrivacyTest :: BagList Int -> Property
simpleCountPrivacyTest xs = monadicIO $
  expectDP
    1.0
    500
    ( reify . flip simpleCount 0 $ left xs
    , reify . flip simpleCount 0 $ right xs
    )

simpleCountEpsTooSmallTest :: Property
simpleCountEpsTooSmallTest = monadicIO $
  expectNotDP
    0.5
    500
    50
    (bagListLarge (-10, 10) 1 >>= \(xs :: BagList Int) -> return (left xs, right xs))
    ( reify . flip simpleCount 0
    , reify . flip simpleCount 0
    )

simpleMeanPrivacyTest :: Double -> BagList Double -> Property
simpleMeanPrivacyTest clipBound xs = monadicIO $
  expectDP
    (clipBound + 1.0)
    500
    ( reify . flip simpleMean (realToFrac clipBound) . map realToFrac $ left xs
    , reify . flip simpleMean (realToFrac clipBound) . map realToFrac $ right xs
    )

unboundedMeanNotPrivateTest :: Property
unboundedMeanNotPrivateTest = monadicIO $
  expectNotDP
    1.0
    500
    50
    (bagListLarge (-2.0, 2.0) 1 >>= \(xs :: BagList Double) -> return (left xs, right xs))
    ( reify . unboundedMean . map realToFrac
    , reify . unboundedMean . map realToFrac
    )

prop_rnmIsDifferentiallyPrivate :: Property
prop_rnmIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 rnmPrivacyTest

prop_rnmGapIsDifferentiallyPrivate :: Property
prop_rnmGapIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 rnmGapPrivacyTest

prop_rnmBuggyIsNotDifferentiallyPrivate :: Property
prop_rnmBuggyIsNotDifferentiallyPrivate = rnmNotPrivateTest

prop_smartSumIsDifferentiallyPrivate :: Property
prop_smartSumIsDifferentiallyPrivate =
  forAll (l1List 1.0) smartSumPrivacyTest

prop_smartSumBuggyIsNotDifferentiallyPrivate :: Property
prop_smartSumBuggyIsNotDifferentiallyPrivate =
  smartSumNotPrivateTest

prop_sparseVectorIsDifferentiallyPrivate :: Property
prop_sparseVectorIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorPrivacyTest

prop_sparseVectorBuggyIsNotDifferentiallyPrivate :: Property
prop_sparseVectorBuggyIsNotDifferentiallyPrivate =
  sparseVectorNotPrivateTest

prop_privTreeIsDifferentiallyPrivate :: Property
prop_privTreeIsDifferentiallyPrivate =
  forAll (bagListSmall (0.0, 1.0) 1) privTreePrivacyTest

prop_privTreeBuggyIsNotDifferentiallyPrivate :: Property
prop_privTreeBuggyIsNotDifferentiallyPrivate =
  privTreeBuggyNotPrivateTest

prop_privTreeBuggy2IsNotDifferentiallyPrivate :: Property
prop_privTreeBuggy2IsNotDifferentiallyPrivate =
  privTreeBuggy2NotPrivateTest

prop_sparseVectorGapIsDifferentiallyPrivate :: Property
prop_sparseVectorGapIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorGapPrivacyTest

prop_simpleCountIsDifferentiallyPrivate :: Property
prop_simpleCountIsDifferentiallyPrivate =
  forAll (bagListLarge (-10, 10) 1) simpleCountPrivacyTest

prop_simpleCountEpsTooSmallIsNotDifferentiallyPrivate :: Property
prop_simpleCountEpsTooSmallIsNotDifferentiallyPrivate =
  simpleCountEpsTooSmallTest

prop_simpleMeanIsDifferentiallyPrivate :: Property
prop_simpleMeanIsDifferentiallyPrivate =
  forAll (bagListLarge (-2.0, 2.0) 1) (simpleMeanPrivacyTest 1.0)

prop_unboundedMeanIsNotDifferentiallyPrivate :: Property
prop_unboundedMeanIsNotDifferentiallyPrivate =
  unboundedMeanNotPrivateTest

newtype SmallList a = SmallList {
  getSmallList :: [a]
  } deriving (Show, Eq, Ord)

instance Arbitrary a => Arbitrary (SmallList a) where
  arbitrary = do
    len <- elements [1..12]
    xs <- replicateM len arbitrary
    return (SmallList xs)

  shrink xs = SmallList <$> (filter (not . null) . shrink) (getSmallList xs)

instance Arbitrary PrivTreeNode1D where
  arbitrary =
    let genDir = frequency [(1, pure LeftDir), (1, pure RightDir)] in
    PrivTreeNode1D <$> listOf genDir

  shrink (PrivTreeNode1D dirs) =
    PrivTreeNode1D <$> shrinkList (:[]) dirs

prop_nodeSplit :: PrivTreeNode1D -> Bool
prop_nodeSplit node =
  let (left, right) = endpoints node
      (leftSubNode, rightSubNode) = split node
      (lleft, lright) = endpoints leftSubNode
      (rleft, rright) = endpoints rightSubNode
  in lleft == left && lright == rleft && rright == right

prop_matchReflList :: [Int] -> Bool
prop_matchReflList xs =
  match xs xs

prop_matchSymList :: [(Double, String)] -> Bool
prop_matchSymList xys =
  let xs = map fst xys in
  let ys = map snd xys in
  match xs (map sReal ys)

prop_matchSymDiffLengthList :: [Double] -> [String] -> Property
prop_matchSymDiffLengthList xs ys = length xs /= length ys ==>
  not $ match xs (map sReal ys)

prop_matchDiffLengthList :: [Int] -> [Int] -> Property
prop_matchDiffLengthList xs ys = length xs /= length ys ==>
  not (match xs ys)

prop_pairWiseL1ListLength :: Property
prop_pairWiseL1ListLength =
  forAll (pairWiseL1 1.0) $ \(xs :: PairWiseL1List Double) -> length (left xs) == length (right xs)

prop_rnmGapLemma7 :: Property
prop_rnmGapLemma7 =
  forAll (pairWiseL1 1.0) $
  \(xs :: PairWiseL1List Double) ->
    let xs1 = left  xs
        xs2 = right xs
        max1 = maximum xs1
        max2 = maximum xs2
    in abs (max1 - max2) <= 1.0

printAndExitIfFailed :: Result -> IO ()
printAndExitIfFailed r = do
  print r
  unless (isSuccess r) $
    exitWith (ExitFailure 1)

main :: IO ()
main = do
  putStrLn $
    "\n#######################################"
    ++ "\n#          QuickCheck Tests           #"
    ++ "\n#######################################"
  let simpleProperties = prop_nodeSplit
                         .&&. prop_matchReflList
                         .&&. prop_matchSymList
                         .&&. prop_matchSymDiffLengthList
                         .&&. prop_matchDiffLengthList
                         .&&. prop_pairWiseL1ListLength
                         .&&. prop_rnmGapLemma7

  githubCIEnv <- getEnv "GITHUB_WORKFLOW"

  if (isJust githubCIEnv)
  then putStrLn "running on github CI"
  else putStrLn "running locally"

  let expectSuccessArgs =
        if isJust githubCIEnv
        then stdArgs{maxSuccess = 100, maxShrinks = 20}
        else stdArgs{maxSuccess = 20, maxShrinks = 20}
  let expectFailureArgs = stdArgs{maxSuccess = 5, maxShrinks = 20}

  quickCheckWithResult
    stdArgs{maxSuccess=2000}
    simpleProperties >>= printAndExitIfFailed

  quickCheckWithResult
    expectSuccessArgs
    prop_rnmIsDifferentiallyPrivate >>= printAndExitIfFailed
    {-
  quickCheckWithResult
    expectSuccessArgs
    prop_rnmGapIsDifferentiallyPrivate >>= printAndExitIfFailed
-}
  quickCheckWithResult
    expectFailureArgs
    prop_rnmBuggyIsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectSuccessArgs
    prop_smartSumIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    stdArgs{maxSuccess=5}
    prop_smartSumBuggyIsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectSuccessArgs
    prop_sparseVectorIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectSuccessArgs
    prop_sparseVectorGapIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_sparseVectorBuggyIsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectSuccessArgs
    prop_privTreeIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_privTreeBuggyIsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectSuccessArgs
    prop_simpleCountIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_simpleCountEpsTooSmallIsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_unboundedMeanIsNotDifferentiallyPrivate >>= printAndExitIfFailed


  putStrLn $
    "\n#######################################"
    ++ "\n#              Unit Tests             #"
    ++ "\n#######################################"
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
