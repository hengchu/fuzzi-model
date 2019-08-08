module Examples where

import Control.Applicative.Free
import Control.Monad.Writer.Strict
import Interp
import Term
import qualified Distribution as D
import qualified Model as M
import Model ((%>), (%>=), (%<), (%<=), (%==), (%/=))

prog1 :: (M.Model domain v, Show v, M.CmpResult v ~ bool)
      => Fuzzi domain bool v
prog1 = do
  x1 <- laplace (pure 1.0) 1.0
  x2 <- gaussian (pure 1.0) 1.0
  pure $ x1 + x2

prog2 :: (M.Model domain v, Show v, M.CmpResult v ~ bool)
      => Fuzzi domain bool v
prog2 =
  withSample (laplace (pure 1.0) 1.0) $ \x1 -> do
    x2 <- gaussian (pure x1) 1.0
    pure $ x1 + x2

reportNoisyMaxAux :: forall v domain bool.
                     (M.Model domain v, Show v, M.CmpResult v ~ bool)
                  => [v]
                  -> Int
                  -> v
                  -> Fuzzi domain bool Int
reportNoisyMaxAux []     idx currMax = pure idx
reportNoisyMaxAux (x:xs) idx currMax = do
  withSample (laplace (pure x) 1.0) $ \x -> do
    fif
      (pure $ x %> currMax)
      (reportNoisyMaxAux xs (idx+1) x)
      (reportNoisyMaxAux xs idx     currMax)

reportNoisyMax :: forall v domain bool.
                  (M.Model domain v, Show v, M.CmpResult v ~ bool)
               => [v]
               -> Fuzzi domain bool Int
reportNoisyMax []     = error "input must not be empty"
reportNoisyMax (x:xs) = do
  withSample (laplace (pure x) 1.0) $ \x -> do
    reportNoisyMaxAux xs 0 x

test1 :: Double
test1 = M.unwrapNoRandomness $ runInterpreter StraightForwardInterp prog1

test2 :: (Double, [SomeTrace])
test2 = M.unwrapNoRandomness $ runWriterT $ runInterpreter TracingInterp prog1

test3 :: IO (Double, [SomeTrace])
test3 = D.sample $ runWriterT $ runInterpreter TracingConcreteInterp prog1

test4 :: IO Double
test4 = D.sample $ runInterpreter ConcreteInterp prog1

{-
test5 :: [Double]
test5 = M.unwrapNoRandomness $ runMultiInterpreter StraightForwardInterp prog1

test6 :: ([Double], [SomeTrace])
test6 = M.unwrapNoRandomness . runWriterT $ runMultiInterpreter TracingInterp prog1

test7 :: IO ([Double], [SomeTrace])
test7 = (D.sample . runWriterT) $ runMultiInterpreter TracingConcreteInterp prog1

test8 :: IO [Double]
test8 = D.sample $ runMultiInterpreter ConcreteInterp prog1
-}

test9 :: M.WithDistribution Double
test9 = M.unwrapNoRandomness $ runInterpreter StraightForwardInterp prog1

test10 :: (M.WithDistribution Double, [SomeTrace])
test10 = M.unwrapNoRandomness $ runWriterT $ runInterpreter TracingInterp prog1

test11 :: IO (M.WithDistribution Double, [SomeTrace])
test11 = D.sample $ runWriterT $ runInterpreter TracingConcreteInterp prog1

test12 :: IO (M.WithDistribution Double)
test12 = D.sample $ runInterpreter ConcreteInterp prog1

{-
test13 :: [M.WithDistribution Double]
test13 = M.unwrapNoRandomness $ runMultiInterpreter StraightForwardInterp prog1

test14 :: ([M.WithDistribution Double], [SomeTrace])
test14 = (M.unwrapNoRandomness . runWriterT) $ runMultiInterpreter TracingInterp prog1

test15 :: IO ([M.WithDistribution Double], [SomeTrace])
test15 = (D.sample . runWriterT) $ runMultiInterpreter TracingConcreteInterp prog1

test16 :: IO [M.WithDistribution Double]
test16 = D.sample $ runMultiInterpreter ConcreteInterp prog1
-}

test17 :: Int
test17 = M.unwrapNoRandomness $
  runInterpreter StraightForwardInterp (reportNoisyMax @Double [1, 3, 2])

test18 :: (Int, [SomeTrace])
test18 = M.unwrapNoRandomness . runWriterT $
  runInterpreter TracingInterp (reportNoisyMax @Double [1, 3, 2])

test19 :: IO (Int, [SomeTrace])
test19 = D.sample . runWriterT $
  runInterpreter TracingConcreteInterp (reportNoisyMax @Double [1, 3, 2])

test20 :: IO Int
test20 = D.sample $
  runInterpreter ConcreteInterp (reportNoisyMax @Double [1, 3, 2])

test21 :: Int
test21 = M.unwrapNoRandomness $
  runInterpreter StraightForwardInterp (reportNoisyMax @(M.WithDistribution Double) [1, 3, 2])

test22 :: (Int, [SomeTrace])
test22 = M.unwrapNoRandomness . runWriterT $
  runInterpreter TracingInterp (reportNoisyMax @(M.WithDistribution Double) [1, 3, 2])

test23 :: IO (Int, [SomeTrace])
test23 = D.sample . runWriterT $
  runInterpreter TracingConcreteInterp (reportNoisyMax @(M.WithDistribution Double) [1, 3, 2])

test24 :: IO Int
test24 = D.sample $
  runInterpreter ConcreteInterp (reportNoisyMax @(M.WithDistribution Double) [1, 3, 2])
