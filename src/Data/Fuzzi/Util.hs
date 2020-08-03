{-# OPTIONS_HADDOCK hide #-}
module Data.Fuzzi.Util where

import Data.Time.Clock

timed :: IO () -> IO NominalDiffTime
timed f = do
  !start <- getCurrentTime
  f
  !end <- getCurrentTime
  return (end `diffUTCTime` start)
