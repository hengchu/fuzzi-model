module Data.Fuzzi.Logging (
  runStdoutColoredLoggingAboveLevelT
  , runStdoutColoredLoggingWarnT
  , runStdoutColoredLoggingT
  , runStderrColoredLoggingWarnT
  , runStderrColoredLoggingT
  , module Control.Monad.Logger
  ) where

import Control.Monad.IO.Class
import Control.Monad.Logger
import GHC.IO.Handle
import GHC.IO.Handle.FD
import System.Log.FastLogger
import qualified Data.ByteString.Char8 as S8

runStdoutColoredLoggingWarnT :: MonadIO m => LoggingT m a -> m a
runStdoutColoredLoggingWarnT = runStdoutColoredLoggingAboveLevelT LevelWarn

runStdoutColoredLoggingAboveLevelT :: MonadIO m => LogLevel -> LoggingT m a -> m a
runStdoutColoredLoggingAboveLevelT lvl m = runStdoutColoredLoggingT $ filterLogger (const (>= lvl)) m

runStderrColoredLoggingWarnT :: MonadIO m => LoggingT m a -> m a
runStderrColoredLoggingWarnT m = runStderrColoredLoggingT $ filterLogger (const (>= LevelWarn)) m

coloredOutput :: Handle
              -> Loc
              -> LogSource
              -> LogLevel
              -> LogStr
              -> IO ()
coloredOutput h loc src level msg = do
  case level of
    LevelDebug   -> S8.hPutStr h "\ESC[37m"
    LevelInfo    -> S8.hPutStr h "\ESC[32m"
    LevelWarn    -> S8.hPutStr h "\ESC[33m"
    LevelError   -> S8.hPutStr h "\ESC[31m"
    LevelOther _ -> S8.hPutStr h "\ESC[36m"
  S8.hPutStr h ls
  S8.hPutStr h "\ESC[0m"
  where
    ls = fromLogStr $ defaultLogStr loc src level msg

runStdoutColoredLoggingT :: MonadIO m => LoggingT m a -> m a
runStdoutColoredLoggingT = (`runLoggingT` coloredOutput stdout)

runStderrColoredLoggingT :: MonadIO m => LoggingT m a -> m a
runStderrColoredLoggingT = (`runLoggingT` coloredOutput stderr)
