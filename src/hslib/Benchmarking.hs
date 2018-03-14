module Benchmarking where

import System.Clock
import Control.Concurrent.MVar
import Control.Concurrent (forkIO)

-- mini benchmarking library

elapsedMicros :: TimeSpec -> IO Double
elapsedMicros start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsed = (fromIntegral elapsedNanos)/1e3 :: Double in
    return elapsed

timed :: IO a -> IO (a, Double)
timed act = do
  start <- getTime Monotonic
  r <- act
  totalTime <- elapsedMicros start
  return (r, totalTime)

timeIt :: IO a -> IO Double
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

timeAsync :: IO a -> IO (MVar Double)
timeAsync act = do
  start <- getTime Monotonic
  m <- newEmptyMVar
  _ <- forkIO $ do
    _ <- act
    totalTime <- elapsedMicros start
    putMVar m totalTime
  return m
