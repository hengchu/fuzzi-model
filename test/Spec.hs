import Control.Lens (view)
import Control.Monad
import Control.Monad.Logger
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
  let sa = (fromRational . toRational) a :: S.RealExpr
      sb = (fromRational . toRational) b :: S.RealExpr
  in if a == b
     then sa == sb
     else sa /= sb

prop_rnmLengthConstraints :: SmallList Double -> Property
prop_rnmLengthConstraints (SmallList xs) = monadicIO $ do
  let prog1 = reify (reportNoisyMax (map (fromRational . toRational) xs))
  let prog2 = reify (reportNoisyMax (map (fromRational . toRational) xs))
  buckets <- run $ profileIO 100 prog1
  spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
  case spec of
    Left  err -> run (print err) >> assert False
    Right constraints -> assert (length buckets == length constraints)

smartSumPrivacyTest :: L1List Double -> Property
smartSumPrivacyTest xs = label ("smartsum input size: " ++ show (length xs)) $ monadicIO $ do
  let xs1 = map (fromRational . toRational) (left xs)
  let xs2 = map (fromRational . toRational) (right xs)
  let prog1 = reify (smartSum xs1)
  let prog2 = reify (smartSum xs2)
  buckets <- run $ profileIO 100 prog1
  spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
  case spec of
    Left err -> run (print err) >> assert False
    Right bundles -> do
      results <- run $ runNoLoggingT (runTests 2.0 bundles)
      case results of
        Left err -> run (print err) >> assert False
        Right results' -> do
          run (print (map (view solverResult) results'))
          -- assert (length bundles == length buckets)
          assert (all isOk results')

rnmPrivacyTest :: PairWiseL1List Double -> Property
rnmPrivacyTest xs = label ("rnm input size: " ++ show (length xs)) $ monadicIO $ do
  let xs1   = map (fromRational . toRational) (left xs)
  let xs2   = map (fromRational . toRational) (right xs)
  let prog1 = reify (reportNoisyMax xs1)
  let prog2 = reify (reportNoisyMax xs2)
  buckets <- run $ profileIO 100 prog1
  spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
  case spec of
    Left err -> run (print err) >> assert False
    Right bundles -> do
      results <- run $ runNoLoggingT (runTests 2.0 bundles)
      case results of
        Left err -> run (print err) >> assert False
        Right results' -> do
          run (print (map (view solverResult) results'))
          -- assert (length bundles == length buckets)
          assert (all isOk results')

rnmGapPrivacyTest :: PairWiseL1List Double -> Property
rnmGapPrivacyTest xs = label ("rnmGap input size: " ++ show (length xs)) $ monadicIO $ do
  let xs1   = map (fromRational . toRational) (left xs)
  let xs2   = map (fromRational . toRational) (right xs)
  let prog1 = reify (reportNoisyMaxGap xs1)
  let prog2 = reify (reportNoisyMaxGap xs2)
  buckets <- run $ profileIO 100 prog1
  spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
  case spec of
    Left err -> run (print err) >> assert False
    Right bundles -> do
      results <- run $ runNoLoggingT (runTests 2.0 bundles)
      case results of
        Left err -> run (print err) >> assert False
        Right results' -> do
          let failures = filter isFailed results'
          unless (null failures) $ do
            run (print failures)
            stop False
          run (print (map (view solverResult) results'))
          assert (all isOk results')

rnmNotPrivateTest :: Property
rnmNotPrivateTest = monadicIO $ do
  results <- forM ([0..50] :: [Int]) $ \_ -> do
    (xs :: PairWiseL1List Double) <- pick (pairWiseL1 1.0)
    let xs1   = map (fromRational . toRational) (left xs)
    let xs2   = map (fromRational . toRational) (right xs)
    let prog1 = reify (reportNoisyMaxBuggy xs1)
    let prog2 = reify (reportNoisyMaxBuggy xs2)
    buckets <- run $ runNoLoggingT (profile 300 prog1)
    spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
    case spec of
      Left err -> run (print err) >> stop False
      Right bundles -> do
        results <- run $ runNoLoggingT (runTests 2.0 bundles)
        case results of
          Left err -> run (print err) >> stop False
          Right results' -> do
            run (print (map (view solverResult) results'))
            if any isFailed results' then stop True else return False
  assert (or results)

smartSumNotPrivateTest :: Property
smartSumNotPrivateTest = monadicIO $ do
  results <- forM ([0..50] :: [Int]) $ \_ -> do
    (xs :: L1List Double) <- pick (l1List 1.0)
    let xs1   = map (fromRational . toRational) (left xs)
    let xs2   = map (fromRational . toRational) (right xs)
    let prog1 = reify (smartSumBuggy xs1)
    let prog2 = reify (smartSumBuggy xs2)
    buckets <- run $ runNoLoggingT (profile 500 prog1)
    spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
    case spec of
      Left err -> run (print err) >> stop False
      Right bundles -> do
        results <- run $ runNoLoggingT (runTests 2.0 bundles)
        case results of
          Left err -> run (print err) >> stop False
          Right results' -> do
            run (print (map (view solverResult) results'))
            if any isFailed results' then stop True else return False
  assert (or results)

sparseVectorPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorPrivacyTest xs =
  label ("sparseVector input length: " ++ show (length xs)) $ monadicIO $ do
    let xs1 = map (fromRational . toRational) (left xs)
    let xs2 = map (fromRational . toRational) (right xs)
    let prog1 = reify (sparseVector xs1 2 0)
    let prog2 = reify (sparseVector xs2 2 0)
    buckets <- run $ profileIO 100 prog1
    spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
    case spec of
      Left err -> run (print err) >> assert False
      Right bundles -> do
        results <- run $ runNoLoggingT (runTests 1.0 bundles)
        case results of
          Left err -> run (print err) >> assert False
          Right results' -> do
            run (print (map (view solverResult) results'))
            -- assert (length bundles == length buckets)
            assert (all isOk results')

sparseVectorGapPrivacyTest :: PairWiseL1List Double -> Property
sparseVectorGapPrivacyTest xs =
  label ("sparseVectorGap input length: " ++ show (length xs)) $ monadicIO $ do
    let xs1 = map (fromRational . toRational) (left xs)
    let xs2 = map (fromRational . toRational) (right xs)
    let prog1 = reify (sparseVectorGap xs1 2 0)
    let prog2 = reify (sparseVectorGap xs2 2 0)
    buckets <- run $ profileIO 100 prog1
    spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
    case spec of
      Left err -> run (print err) >> assert False
      Right bundles -> do
        results <- run $ runNoLoggingT (runTests 1.0 bundles)
        case results of
          Left err -> run (print err) >> assert False
          Right results' -> do
            run (print (map (view solverResult) results'))
            -- assert (length bundles == length buckets)
            assert (all isOk results')

sparseVectorNotPrivateTest :: Property
sparseVectorNotPrivateTest = monadicIO $ do
  results <- forM ([0..20] :: [Int]) $ \_ -> do
    (xs :: L1List Double) <- pick (l1List 1.0)
    let xs1   = map (fromRational . toRational) (left xs)
    let xs2   = map (fromRational . toRational) (right xs)
    let prog1 = reify (sparseVectorBuggy xs1 2 0)
    let prog2 = reify (sparseVectorBuggy xs2 2 0)
    buckets <- run $ runNoLoggingT (profile 500 prog1)
    spec <- run $ runNoLoggingT $ symExecGeneralize buckets prog2
    case spec of
      Left err -> run (print err) >> stop False
      Right bundles -> do
        results <- run $ runNoLoggingT (runTests 1.0 bundles)
        case results of
          Left err -> run (print err) >> stop False
          Right results' -> do
            --run (print results')
            --stop False
            run (print (map (view solverResult) results'))
            if any isFailed results' then stop True else return False
  assert (or results)

privTreePrivacyTest :: BagList Double -> Property
privTreePrivacyTest xs = monadicIO $ do
  let xs1 = map (fromRational . toRational) (left xs)
  let xs2 = map (fromRational . toRational) (right xs)
  let prog1 = reify (privTree xs1)
  let prog2 = reify (privTree xs2)
  buckets <- run $ runNoLoggingT (profile 100 prog1)
  spec <- run $ runNoLoggingT (symExecGeneralize buckets prog2)
  case spec of
    Left err -> run (print err) >> stop False
    Right bundles -> do
      results <- run $ runNoLoggingT (runTests k_PT_EPSILON bundles)
      case results of
        Left err -> run (print err) >> stop False
        Right results' -> do
          run (print (map (view solverResult) results'))
          let failures = filter isFailed results'
          unless (null failures) $
            run (print failures)
          assert (all isOk results')

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
  forAll (bagList (0.0, 1.0) 1) privTreePrivacyTest

prop_sparseVectorGapIsDifferentiallyPrivate :: Property
prop_sparseVectorGapIsDifferentiallyPrivate =
  forAllShrink (pairWiseL1 1.0) shrinkPairWiseL1 sparseVectorGapPrivacyTest

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

  let expectSuccessArgs = stdArgs{maxSuccess = 20, maxShrinks = 20}
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

  putStrLn $
    "\n#######################################"
    ++ "\n#              Unit Tests             #"
    ++ "\n#######################################"
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
