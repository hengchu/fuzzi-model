module Examples where

import Control.Applicative.Free
import Control.Monad.Writer.Strict
import Interp
import Term
import qualified Distribution as D
import qualified Model as M

prog1 :: M.Model domain Double => Fuzzi domain Double
prog1 = do
  x1 <- laplace (pure 1.0) 1.0
  x2 <- gaussian (pure 1.0) 1.0
  pure $ x1 + x2

prog2 :: M.Model domain Double => Fuzzi domain Double
prog2 =
  withSample (laplace (pure 1.0) 1.0) $ \(x1 :: Double) -> do
    x2 <- gaussian (pure x1) 1.0
    pure $ x1 + x2

test1 :: Double
test1 = M.unwrapNoRandomness $ runInterpreter @StraightForwardInterp prog1

test2 :: (Double, [SomeTrace])
test2 = M.unwrapNoRandomness $ runWriterT $ runInterpreter @TracingInterp prog1

test3 :: IO (Double, [SomeTrace])
test3 = D.sample $ runWriterT $ runInterpreter @TracingConcreteInterp prog1

test4 :: IO Double
test4 = D.sample $ runInterpreter @ConcreteInterp prog1


test5 :: [Double]
test5 = map M.unwrapNoRandomness $ runMultiInterpreter @StraightForwardInterp prog1

test6 :: [(Double, [SomeTrace])]
test6 = map (M.unwrapNoRandomness . runWriterT) $ runMultiInterpreter @TracingInterp prog1

test7 :: [IO (Double, [SomeTrace])]
test7 = map (D.sample . runWriterT) $ runMultiInterpreter @TracingConcreteInterp prog1

test8 :: [IO Double]
test8 = map D.sample $ runMultiInterpreter @ConcreteInterp prog1
