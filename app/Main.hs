module Main where

import Data.Fuzzi
import Data.Fuzzi.Examples
import Data.Functor.Identity
import Data.Fuzzi.Logging
import Data.Fuzzi.Rosette
import Data.Either
import Control.DeepSeq

main :: IO ()
main = do
  let prog = reify $ reportNoisyMax (take 10 $ repeat 1)
  let r = runIdentity . runNoLoggingT . (runRosetteT dummyState) $ (evalM prog)
  let rr = fromRight undefined (fst r)
  deepseq r $ return ()
