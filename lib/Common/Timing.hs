module Common.Timing where

import Control.Monad.IO.Class
import System.Clock
import Text.Printf

diff :: TimeSpec -> TimeSpec -> Double
diff (TimeSpec s1 n1) (TimeSpec s2 n2) = (a2 - a1) / (fromIntegral (10 ^ (9 :: Integer) :: Integer) :: Double)
  where
    a1 = (fromIntegral s1 * 10 ^ (9 :: Integer)) + fromIntegral n1
    a2 = (fromIntegral s2 * 10 ^ (9 :: Integer)) + fromIntegral n2

timeItAll :: (MonadIO m) => String -> m a -> m a
timeItAll str x = do
  startMono <- liftIO $ getTime Monotonic
  startProcessCPU <- liftIO $ getTime ProcessCPUTime
  r <- x
  endMono <- liftIO $ getTime Monotonic
  endProcessCPU <- liftIO $ getTime ProcessCPUTime
  liftIO $ printf "%s -- Mono clock: %.6fs\n" str (diff startMono endMono)
  liftIO $ printf "%s -- CPU clock:  %.6fs\n" str (diff startProcessCPU endProcessCPU)
  return r
