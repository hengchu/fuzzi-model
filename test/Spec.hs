import Control.Concurrent.Async
import Control.Monad.IO.Class
import Control.Monad.Trans.Identity
import Distribution
import EDSL
import SimpleSMT
import Symbol as S
import System.Exit
import Test.HUnit (runTestTT, errors, failures)
import Types
import qualified Test.HUnit.Base as H
import Test

smtTest1 :: IO Bool
smtTest1 = runSymbolicT $ do
  x <- sReal "x"
  y <- sReal "y"
  S.assert ((x + y) %>= 0)
  r <- S.check
  return $ r == Sat

smtTest2 :: IO Bool
smtTest2 = runSymbolicT @IO $ do
  x <- sReal "x"
  y <- sReal "y"
  S.assert (x %== 1)
  S.assert (y %== 1)
  S.assert ((x + y) %== 3)
  r <- S.check
  return $ r == Unsat

smtTest3 :: IO Bool
smtTest3 = runSymbolicT @IO $ do
  x <- sReal "x"
  y <- sReal "y"
  S.assert (x %>= 1)
  S.assert (y %< 1)
  S.assert ((x + y) %== 2)
  r <- S.check
  return $ r == Sat

smtTest4 :: IO Bool
smtTest4 = runSymbolicT @IO $ do
  x <- sReal "x"
  S.assert (x %== 1)
  r <- S.check
  v <- S.getRealValue "x"
  case r of
    Sat -> return $ v == Just 1
    _   -> return False

smtTest5 :: IO Bool
smtTest5 = do
  results <- mapConcurrently id [smtTest1, smtTest2, smtTest3, smtTest4]
  return (all id results)

smtTests :: H.Test
smtTests = H.TestList [
  H.TestCase (H.assert smtTest1)
  , H.TestCase (H.assert smtTest2)
  , H.TestCase (H.assert smtTest3)
  , H.TestCase (H.assert smtTest4)
  , H.TestCase (H.assert smtTest5)
  ]

provenanceTests :: H.Test
provenanceTests = H.TestList [
  H.TestCase (H.assert testSmartSumProvenance)
  ]

testSmartSumProvenance :: IO Bool
testSmartSumProvenance = do
  results <- (profile 100 . reify)
    (smartSum
      @(IdentityT TracedDist)
      @_
      @(WithDistributionProvenance [Double])
      [1, 2, 3, 4, 5])
  let provs = map (provenance . fst) results
  return (all (== (head provs)) provs)

allTests :: H.Test
allTests = H.TestList [
  H.TestLabel "Symbol" smtTests
  , H.TestLabel "Distribution" provenanceTests
  ]

main :: IO ()
main = do
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
