import Symbol as S
import Types
import SimpleSMT
import qualified Test.HUnit.Base as H
import Test.HUnit (runTestTT, errors, failures)
import System.Exit
import Control.Monad.IO.Class

smtTest1 :: H.Assertion
smtTest1 = H.assert . runSymbolicT @IO $ do
  x <- sReal "x"
  y <- sReal "y"
  S.assert ((x + y) %>= 0)
  r <- S.check
  return $ r == Sat

smtTest2 :: H.Assertion
smtTest2 = H.assert . runSymbolicT @IO $ do
  x <- sReal "x"
  y <- sReal "y"
  S.assert (x %== 1)
  S.assert (y %== 1)
  S.assert ((x + y) %== 3)
  r <- S.check
  return $ r == Unsat

smtTest3 :: H.Assertion
smtTest3 = H.assert . runSymbolicT @IO $ do
  x <- sReal "x"
  y <- sReal "y"
  S.assert (x %>= 1)
  S.assert (y %< 1)
  S.assert ((x + y) %== 2)
  r <- S.check
  return $ r == Sat

smtTest4 :: H.Assertion
smtTest4 = H.assert . runSymbolicT @IO $ do
  x <- sReal "x"
  S.assert (x %== 1)
  r <- S.check
  v <- S.getRealValue "x"
  case r of
    Sat -> return $ v == (Just 1)
    _   -> return $ False

smtTests :: Solver -> H.Test
smtTests s = H.TestList [
  H.TestCase (smtTest1)
  , H.TestCase (smtTest2)
  , H.TestCase (smtTest3)
  , H.TestCase (smtTest4)
  ]

main :: IO ()
main = do
  solver <- defaultZ3Solver
  r <- runTestTT (smtTests solver)
  if errors r + failures r > 0
  then exitWith (ExitFailure 1)
  else exitSuccess
