import Control.Concurrent.Async
import Control.Monad.IO.Class
import Control.Monad.Trans.Identity
import Distribution
import EDSL
import Examples
import Symbol as S
import System.Exit
import Test.HUnit (runTestTT, errors, failures)
import Types
import qualified Test.HUnit.Base as H
import Test
import Test.QuickCheck
import qualified Z3.Base as Z3
import qualified Data.Map.Strict as M

testSmtSimple :: IO Bool
testSmtSimple = do
  (_, r) <- S.runSymbolicT $ do
    x <- S.freshSReal "x"
    assert (x %< (x + 1)) True
  return (r == Z3.Sat)

testSmtSimple2 :: IO Bool
testSmtSimple2 = do
  (_, r) <- S.runSymbolicT $ do
    x <- S.freshSReal "x"
    assert (x %> (x + 1)) True
  return (r == Z3.Unsat)

testSmtSubstitute :: IO Bool
testSmtSubstitute = do
  (_, r) <- S.runSymbolicT $ do
    x <- S.freshSReal "x"
    y <- S.freshSReal "y"
    let cond = x %> (y + 1)
    assert (substituteB cond [(y, x)]) True
  return (r == Z3.Unsat)

smtTests :: H.Test
smtTests = H.TestList [
  H.TestCase (H.assert testSmtSimple)
  , H.TestCase (H.assert testSmtSimple2)
  , H.TestCase (H.assert testSmtSubstitute)
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

main :: IO ()
main = do
  putStrLn $
    "\n#######################################"
    ++ "\n#          QuickCheck Tests           #"
    ++ "\n#######################################"
  quickCheckWith stdArgs{chatty=True, maxSuccess=500} prop_symbolCongruence
  putStrLn $
    "\n#######################################"
    ++ "\n#              Unit Tests             #"
    ++ "\n#######################################"
  r <- runTestTT allTests
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
