import Control.Monad
import Data.Fuzzi.Distribution
import Data.Fuzzi.EDSL
import Data.Fuzzi.Examples
import Data.Fuzzi.Logging
import Data.Fuzzi.NeighborGen
import Data.Fuzzi.Test
import Data.Fuzzi.Types hiding (or)
import Data.Maybe
import Spec.Types.Structures
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
  let sa = realToFrac a :: RealExpr
      sb = realToFrac b :: RealExpr
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
      100
      ( reify . smartSum . map realToFrac $ left xs
      , reify . smartSum . map realToFrac $ right xs
      )

smartSumPrivacyTestRosette :: L1List Double -> Property
smartSumPrivacyTestRosette xs =
  label ("smartsum input size: " ++ show (length xs)) $
  monadicIO $
    expectDPRosette
      2.0
      100
      ( reify . smartSum . map realToFrac $ left xs
      , reify . smartSum . map realToFrac $ right xs
      )

prefixSumPrivacyTest :: L1List Double -> Property
prefixSumPrivacyTest xs =
  label ("prefixsum input size: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . prefixSum . map realToFrac $ left xs
      , reify . prefixSum . map realToFrac $ right xs
      )

prefixSumBuggyNotPrivateTest :: Property
prefixSumBuggyNotPrivateTest = label "prefixSumBuggy" $
  monadicIO $
    expectNotDPRosette
      1.0
      500
      50
      (l1List 1.0 >>= \(input :: L1List Double) -> return (left input, right input))
      ( reify . prefixSumBuggy . map realToFrac
      , reify . prefixSumBuggy . map realToFrac
      )

simpleSumBuggyNotPrivateTest :: Property
simpleSumBuggyNotPrivateTest = label "simpleSumBuggy" $
  monadicIO $
    expectNotDPRosette
      1.0
      500
      50
      (l1List 1.0 >>= \(input :: L1List Double) -> return (left input, right input))
      ( reify . simpleSumBuggy . map realToFrac
      , reify . simpleSumBuggy . map realToFrac
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

rnmPrivacyTestRosette :: PairWiseL1List Double -> Property
rnmPrivacyTestRosette xs = label ("rnmOpt input size: " ++ show (length xs)) $
  monadicIO $
    expectDPRosette
      2.0
      100
      ( reify . (reportNoisyMaxOpt @Integer) . map realToFrac $ left xs
      , reify . (reportNoisyMaxOpt @IntExpr) . map realToFrac $ right xs
      )

rnmGapPrivacyTest :: PairWiseL1List Double -> Property
rnmGapPrivacyTest xs = label ("rnmGap input size: " ++ show (length xs)) $
  monadicIO $
    expectDPRosette
      4.0
      100
      ( reify . reportNoisyMaxGapOpt @Integer . map realToFrac $ left xs
      , reify . reportNoisyMaxGapOpt @IntExpr . map realToFrac $ right xs
      )

rnmGapBuggyNotPrivateTest :: Property
rnmGapBuggyNotPrivateTest = label "rnmGapBuggy" $
  monadicIO $
    expectNotDPRosette
      4.0
      100
      50
      (pairWiseL1 1.0 >>= \(input :: PairWiseL1List Double) -> return (left input, right input))
      ( reify . reportNoisyMaxGapBuggy . map realToFrac
      , reify . reportNoisyMaxGapBuggy . map realToFrac
      )

rnmNotPrivateTest :: Property
rnmNotPrivateTest = label "rnmBuggy" $ monadicIO $
  expectNotDP
    2.0
    300
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . reportNoisyMaxBuggy . map realToFrac
    , reify . reportNoisyMaxBuggy . map realToFrac
    ) -- code duplication because of let bindings monomorphises the types

smartSumNotPrivateTest :: Property
smartSumNotPrivateTest = label "smartSumBuggy" $ monadicIO $
  expectNotDP
    2.0
    500
    50
    (l1List 1.0 >>= \(xs :: L1List Double) -> return (left xs, right xs))
    ( reify . smartSumBuggy . map realToFrac
    , reify . smartSumBuggy . map realToFrac
    )

numericSparseVectorPrivacyTest :: PairWiseL1List Double -> Property
numericSparseVectorPrivacyTest xs =
  label ("numericSparseVector input length: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . (\xs -> numericSparseVector xs 2 0) . map realToFrac $ left xs
      , reify . (\xs -> numericSparseVector xs 2 0) . map realToFrac $ right xs
      )

sparseVectorPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorPrivacyTest xs =
  label ("sparseVector input length: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . (\xs -> sparseVector xs 2 0.5) . map realToFrac $ left xs
      , reify . (\xs -> sparseVector xs 2 0.5) . map realToFrac $ right xs
      )

sparseVectorRenoiseThresholdPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorRenoiseThresholdPrivacyTest xs =
  label ("sparseVectorRenoiseThreshold input length: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . (\xs -> sparseVectorRenoiseThreshold xs 2 0.5) . map realToFrac $ left xs
      , reify . (\xs -> sparseVectorRenoiseThreshold xs 2 0.5) . map realToFrac $ right xs
      )

sparseVectorPrivacyTestRosette :: PairWiseL1List Double -> Property
sparseVectorPrivacyTestRosette xs =
  label ("sparseVectorOpt input length: " ++ show (length xs)) $
  monadicIO $
    expectDPRosette
      1.0
      500
      ( reify . (\xs -> sparseVectorOpt @Integer xs 2 0.5) . map realToFrac $ left xs
      , reify . (\xs -> sparseVectorOpt @IntExpr xs 2 0.5) . map realToFrac $ right xs
      )

sparseVectorGapPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorGapPrivacyTest xs =
  label ("sparseVectorGap input length: " ++ show (length xs)) $
  monadicIO $
    expectDP
      1.0
      500
      ( reify . (\xs -> sparseVectorGap xs 2 0.5) . map realToFrac $ left xs
      , reify . (\xs -> sparseVectorGap xs 2 0.5) . map realToFrac $ right xs
      )

sparseVectorGapPrivacyTestRosette :: PairWiseL1List Double -> Property
sparseVectorGapPrivacyTestRosette xs =
  label ("sparseVectorGap input length: " ++ show (length xs)) $
  monadicIO $
    expectDPRosette
      1.0
      500
      ( reify . (\xs -> sparseVectorGapOpt @Integer xs 2 0.5) . map realToFrac $ left xs
      , reify . (\xs -> sparseVectorGapOpt @IntExpr xs 2 0.5) . map realToFrac $ right xs
      )

sparseVectorNotPrivateTest :: Property
sparseVectorNotPrivateTest = label "sparseVectorBuggy" $ monadicIO $
  expectNotDPRosette
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorBuggy xs 2 0.5) . map realToFrac
    , reify . (\xs -> sparseVectorBuggy xs 2 0.5) . map realToFrac
    )

sparseVectorNotPrivateTestRosette :: Property
sparseVectorNotPrivateTestRosette = label "sparseVectorBuggyOpt" $ monadicIO $
  expectNotDPRosetteVerbose
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorBuggyOpt @Integer xs 2 0.5) . map realToFrac
    , reify . (\xs -> sparseVectorBuggyOpt @IntExpr xs 2 0.5) . map realToFrac
    )

sparseVector4NotPrivateTest :: Property
sparseVector4NotPrivateTest = label "sparseVectorBuggy4" $ monadicIO $
  expectNotDP
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorBuggy4 xs 2 0.5) . map realToFrac
    , reify . (\xs -> sparseVectorBuggy4 xs 2 0.5) . map realToFrac
    )

sparseVector5NotPrivateTest :: Property
sparseVector5NotPrivateTest = label "sparseVectorBuggy5" $ monadicIO $
  expectNotDP
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorBuggy5 xs 0.5) . map realToFrac
    , reify . (\xs -> sparseVectorBuggy5 xs 0.5) . map realToFrac
    )

sparseVector6NotPrivateTest :: Property
sparseVector6NotPrivateTest = label "sparseVectorBuggy6" $ monadicIO $
  expectNotDP
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorBuggy6 xs 0.5) . map realToFrac
    , reify . (\xs -> sparseVectorBuggy6 xs 0.5) . map realToFrac
    )

sparseVectorGapBuggyNotPrivateTest :: Property
sparseVectorGapBuggyNotPrivateTest = label "sparseVectorGapBuggy" $ monadicIO $
  expectNotDPRosette
    1.0
    500
    50
    (pairWiseL1 1.0 >>= \(xs :: PairWiseL1List Double) -> return (left xs, right xs))
    ( reify . (\xs -> sparseVectorGapBuggy xs 0.5) . map realToFrac
    , reify . (\xs -> sparseVectorGapBuggy xs 0.5) . map realToFrac
    )

privTreePrivacyTest :: BagList Double -> Property
privTreePrivacyTest xs = label ("privTree input length: " ++ show (bagListLength xs)) $
  monadicIO $
  expectDP
    k_PT_EPSILON
    500
    ( reify . privTree . map realToFrac $ left xs
    , reify . privTree . map realToFrac $ right xs
    )

privTreeBuggyNotPrivateTest :: Property
privTreeBuggyNotPrivateTest = label "privTreeBuggy" $
  monadicIO $
  expectNotDP
    k_PT_EPSILON
    100
    20
    (bagListSmall (0, 1) 1 >>= \(xs :: BagList Double) -> return (left xs, right xs))
    ( reify . privTreeBuggy . map realToFrac
    , reify . privTreeBuggy . map realToFrac
    )

privTreeBuggy2NotPrivateTest :: Property
privTreeBuggy2NotPrivateTest = label "privTreeBuggy2" $
  monadicIO $
  expectNotDP
    k_PT_EPSILON
    100
    20
    (bagListSmall (0, 1) 1 >>= \(xs :: BagList Double) -> return (left xs, right xs))
    ( reify . privTreeBuggy2 . map realToFrac
    , reify . privTreeBuggy2 . map realToFrac
    )

simpleGeometricPrivacyTest :: SensitiveCount Integer -> Property
simpleGeometricPrivacyTest xs = label ("simple geometric input: " ++ (show xs)) $
  monadicIO $
  expectDP
    (log (1 / alpha))
    500
    ( reify . flip simpleGeometric alpha $ (fromIntegral . left  $ xs)
    , reify . flip simpleGeometric alpha $ (fromIntegral . right $ xs)
    )
  where alpha :: Fractional a => a
        alpha = 0.3

geometricFixedSensPrivacyTest :: GeoFixedSensParam Integer -> Property
geometricFixedSensPrivacyTest xs@(GeoFixedSensParam a b sens eps) =
  label ("geometric fixed sensitivity input: " ++ (show xs)) $
  monadicIO $
  expectDP
    (eps + 1e-15)
    500
    ( reify $ geometricFixedSens (fromIntegral a) (realToFrac sens) (realToFrac eps)
    , reify $ geometricFixedSens (fromIntegral b) (realToFrac sens) (realToFrac eps)
    )

loopGeometricFixedSensPrivacyTest :: NonEmptyList (GeoFixedSensParam Integer) -> Property
loopGeometricFixedSensPrivacyTest (getNonEmpty -> xs) =
  label ("loop geometric input size: " ++ (show (length xs))) $
  monadicIO $
  expectDP
    (eps + 1e-15)
    500
    ( reify $ loopGeometricFixedSens (lit inputs1)
    , reify $ loopGeometricFixedSens (lit inputs2)
    )
  where sensValues = map (\(GeoFixedSensParam _ _ sens _)   -> sens) xs
        epsValues  = map (\(GeoFixedSensParam _ _ _    eps) -> eps)  xs
        counts1    = map (\(GeoFixedSensParam a _ _    _)   -> a)    xs
        counts2    = map (\(GeoFixedSensParam _ b _    _)   -> b)    xs
        inputs1    = zipWith3 (\count sens eps -> (fromIntegral count, (realToFrac sens, realToFrac eps))) counts1 sensValues epsValues
        inputs2    = zipWith3 (\count sens eps -> (fromIntegral count, (realToFrac sens, realToFrac eps))) counts2 sensValues epsValues
        eps        = sum epsValues

simpleCountPrivacyTest :: BagList Int -> Property
simpleCountPrivacyTest xs = label ("simpleCount input length: " ++ (show (bagListLength xs))) $
  monadicIO $
  expectDP
    1.0
    500
    ( reify . flip simpleCount 0 $ left xs
    , reify . flip simpleCount 0 $ right xs
    )

simpleCountEpsTooSmallTest :: Property
simpleCountEpsTooSmallTest = label "simpleCountEpsTooSmall" $ monadicIO $
  expectNotDP
    0.5
    500
    50
    (bagListLarge (-10, 10) 1 >>= \(xs :: BagList Int) -> return (left xs, right xs))
    ( reify . flip simpleCount 0
    , reify . flip simpleCount 0
    )

simpleMeanPrivacyTest :: Double -> BagList Double -> Property
simpleMeanPrivacyTest clipBound xs = label ("simpleMean input length: " ++ (show (bagListLength xs))) $
  monadicIO $
  expectDP
    (clipBound + 1.0)
    500
    ( reify . flip simpleMean (realToFrac clipBound) . map realToFrac $ left xs
    , reify . flip simpleMean (realToFrac clipBound) . map realToFrac $ right xs
    )

unboundedMeanNotPrivateTest :: Property
unboundedMeanNotPrivateTest = label "unboundedMeanBuggy" $
  monadicIO $
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

prop_rnmIsDifferentiallyPrivateRosette :: Property
prop_rnmIsDifferentiallyPrivateRosette =
  forAllShrink (pairWiseL1{-Sized (10, 20)-} 1.0) shrinkPairWiseL1 rnmPrivacyTestRosette

prop_rnmGapIsDifferentiallyPrivate :: Property
prop_rnmGapIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 rnmGapPrivacyTest

prop_rnmBuggyIsNotDifferentiallyPrivate :: Property
prop_rnmBuggyIsNotDifferentiallyPrivate = rnmNotPrivateTest

prop_smartSumIsDifferentiallyPrivate :: Property
prop_smartSumIsDifferentiallyPrivate =
  forAll (l1List 1.0) smartSumPrivacyTest

prop_smartSumIsDifferentiallyPrivateRosette :: Property
prop_smartSumIsDifferentiallyPrivateRosette =
  forAll (l1List 1.0) smartSumPrivacyTestRosette

prop_prefixSumIsDifferentiallyPrivate :: Property
prop_prefixSumIsDifferentiallyPrivate =
  forAll (l1List 1.0) prefixSumPrivacyTest

prop_smartSumBuggyIsNotDifferentiallyPrivate :: Property
prop_smartSumBuggyIsNotDifferentiallyPrivate =
  smartSumNotPrivateTest

prop_sparseVectorIsDifferentiallyPrivate :: Property
prop_sparseVectorIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorPrivacyTest

prop_numericSparseVectorIsDifferentiallyPrivate :: Property
prop_numericSparseVectorIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 numericSparseVectorPrivacyTest

prop_sparseVectorRenoiseThresholdIsDifferentiallyPrivate :: Property
prop_sparseVectorRenoiseThresholdIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorRenoiseThresholdPrivacyTest

prop_sparseVectorIsDifferentiallyPrivateRosette :: Property
prop_sparseVectorIsDifferentiallyPrivateRosette =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorPrivacyTestRosette

prop_sparseVectorBuggyIsNotDifferentiallyPrivate :: Property
prop_sparseVectorBuggyIsNotDifferentiallyPrivate =
  sparseVectorNotPrivateTest

prop_sparseVectorBuggyIsNotDifferentiallyPrivateRosette :: Property
prop_sparseVectorBuggyIsNotDifferentiallyPrivateRosette =
  sparseVectorNotPrivateTestRosette

prop_sparseVectorBuggy4IsNotDifferentiallyPrivate :: Property
prop_sparseVectorBuggy4IsNotDifferentiallyPrivate =
  sparseVector4NotPrivateTest

prop_sparseVectorBuggy5IsNotDifferentiallyPrivate :: Property
prop_sparseVectorBuggy5IsNotDifferentiallyPrivate =
  sparseVector5NotPrivateTest

prop_sparseVectorBuggy6IsNotDifferentiallyPrivate :: Property
prop_sparseVectorBuggy6IsNotDifferentiallyPrivate =
  sparseVector6NotPrivateTest

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

prop_sparseVectorGapIsDifferentiallyPrivateRosette :: Property
prop_sparseVectorGapIsDifferentiallyPrivateRosette =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorGapPrivacyTestRosette

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
    stdArgs{maxSuccess=500, maxShrinks=20}
    prop_mergeUnionResultIsSuperSet >>= printAndExitIfFailed
  quickCheckWithResult
    stdArgs{maxSuccess=500, maxShrinks=20}
    prop_mergeUnionCommutes >>= printAndExitIfFailed

  quickCheckWithResult
    expectSuccessArgs
    prop_rnmIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectSuccessArgs
    prop_rnmIsDifferentiallyPrivateRosette >>= printAndExitIfFailed
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
    prop_prefixSumIsDifferentiallyPrivate >>= printAndExitIfFailed
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
    prop_sparseVectorRenoiseThresholdIsDifferentiallyPrivate >>= printAndExitIfFailed
{-
  quickCheckWithResult
    expectSuccessArgs
    prop_sparseVectorIsDifferentiallyPrivateRosette >>= printAndExitIfFailed
-}
  quickCheckWithResult
    expectSuccessArgs
    prop_sparseVectorGapIsDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_sparseVectorBuggyIsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_sparseVectorBuggy4IsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_sparseVectorBuggy5IsNotDifferentiallyPrivate >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prop_sparseVectorBuggy6IsNotDifferentiallyPrivate >>= printAndExitIfFailed
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
  quickCheckWithResult
    expectFailureArgs
    simpleSumBuggyNotPrivateTest >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    prefixSumBuggyNotPrivateTest >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    sparseVectorGapBuggyNotPrivateTest >>= printAndExitIfFailed
  quickCheckWithResult
    expectFailureArgs
    rnmGapBuggyNotPrivateTest >>= printAndExitIfFailed


  putStrLn $
    "\n#######################################"
    ++ "\n#              Unit Tests             #"
    ++ "\n#######################################"
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
