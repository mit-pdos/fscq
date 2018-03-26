module Benchmarking where

import Control.Concurrent (forkIO)
import Control.Concurrent.MVar
import Control.Monad.IO.Class
import System.Clock

-- mini benchmarking library

elapsedMicros :: TimeSpec -> IO Double
elapsedMicros start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsed = (fromIntegral elapsedNanos)/1e3 :: Double in
    return elapsed

timed :: MonadIO m => m a -> m (a, Double)
timed act = do
  start <- liftIO $ getTime Monotonic
  r <- act
  totalTime <- liftIO $ elapsedMicros start
  return (r, totalTime)

timeIt :: MonadIO m => m a -> m Double
timeIt act = snd <$> timed act

runInThread :: IO a -> IO (MVar a)
runInThread act = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    -- TODO: if act throws an exception, takeMVar blocks indefinitely
    -- should probably switch to IO () -> IO (MVar ()) and close the channel
    v <- act
    putMVar m v
  return m

runInParallel :: Int -> (Int -> IO a) -> IO ()
runInParallel par act = do
  mvs <- mapM (runInThread . act) [0..par-1]
  mapM_ takeMVar mvs
  return ()

timeAsync :: IO a -> IO (MVar Double)
timeAsync act = do
  start <- getTime Monotonic
  m <- newEmptyMVar
  _ <- forkIO $ do
    _ <- act
    totalTime <- elapsedMicros start
    putMVar m totalTime
  return m
