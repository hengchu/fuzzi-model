module Main where

import Control.DeepSeq
import Control.Monad
import Data.Either
import Data.Functor.Identity
import Data.Fuzzi
import Data.Fuzzi.Examples
import Data.Fuzzi.Logging
import Data.Fuzzi.Rosette
import Data.Time.Clock

main :: IO ()
main = do
  forM_ [1..2000] $ \i -> do
    !start <- getCurrentTime
    let prog = reify $ (reportNoisyMaxOpt @IntExpr) (take i $ repeat 1)
    let r = runIdentity . runNoLoggingT . (runRosetteT dummyState) $ (evalM prog)
    let rr = fromRight undefined (fst r)
    deepseq r $ return ()
    !end <- getCurrentTime
    let dur = diffUTCTime end start
    putStrLn $ "running on inputs of size: " ++ show i ++ " took " ++ show dur
