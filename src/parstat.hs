{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}

module Main where

import System.Clock
import Control.Monad
import Options
import System.Exit
import Control.Concurrent

import Fuse
import FscqFs
import CfscqFs
import GenericFs
import System.Posix.IO (defaultFileFlags)

elapsedMicros :: TimeSpec -> IO Float
elapsedMicros start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsed = (fromIntegral elapsedNanos)/1e3 :: Float in
    return elapsed

data StatOptions = StatOptions
  { optFscq :: Bool
  , optDiskImg :: FilePath
  , optIters :: Int
  , optN :: Int
  , optMeasureSpeedup :: Bool
  , optReadMem :: Bool
  }

instance Options StatOptions where
  defineOptions = pure StatOptions
    <*> simpleOption "fscq" False
        "run sequential FSCQ"
    <*> simpleOption "img" "disk.img"
         "path to FSCQ disk image"
    <*> simpleOption "iters" 100
         "number of iterations of stat to run"
    <*> simpleOption "n" 1
         "number of parallel threads to issue stats from"
    <*> simpleOption "speedup" False
         "run with n=1 and compare performance"
    <*> simpleOption "readmem" False
         "rather than stat, just read memory"

runInThread :: IO a -> IO (MVar a)
runInThread act = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    v <- act
    putMVar m v
  return m

-- replicateInParallelIterate par iters op runs (op iters times) in n parallel
-- copies
replicateInParallelIterate :: Int -> Int -> IO () -> IO ()
replicateInParallelIterate par iters act = do
  ms <- replicateM par . runInThread . replicateM_ iters $ act
  forM_ ms takeMVar

statOp :: StatOptions -> FuseOperations fh -> IO ()
statOp opts fs =
  if optReadMem opts then fuseGetFileSystemStats fs "/" >> return ()
    else do
      _ <- fuseOpen fs "/" ReadOnly defaultFileFlags
      _ <- fuseGetFileStat fs "/"
      _ <- fuseOpen fs "/dir1" ReadOnly defaultFileFlags
      _ <- fuseGetFileStat fs "/dir1"
      _ <- fuseGetFileStat fs "/dir1/file1"
      return ()

timeParallel :: Int -> Int -> IO () -> IO Float
timeParallel par iters op = do
  start <- getTime Monotonic
  replicateInParallelIterate par iters op
  totalTime <- elapsedMicros start
  return totalTime

parallelIters :: StatOptions -> Int
parallelIters opts = optIters opts * optN opts

seqIters :: StatOptions -> Int
seqIters opts = optIters opts

parstat_main :: StatOptions -> FuseOperations fh -> IO ()
parstat_main opts fs = do
  op <- return $ statOp opts fs
  _ <- timeParallel 1 10 op
  parTime <- timeParallel (optN opts) (optIters opts) op
  timePerOp <- return $ parTime/(fromIntegral $ parallelIters opts)
  putStrLn $ show timePerOp ++ " us/op"
  when (optMeasureSpeedup opts) $ do
    seqTime <- timeParallel 1 (optIters opts) op
    seqTimePerOp <- return $ seqTime/(fromIntegral $ seqIters opts)
    putStrLn $ "seq time " ++ show seqTimePerOp ++ " us/op"
    putStrLn $ "speedup of " ++ show (seqTimePerOp / timePerOp)
  return ()

main :: IO ()
main = runCommand $ \opts args -> do
  if length args > 0 then do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)
  else if optFscq opts
    then initFscq (optDiskImg opts) getProcessIds >>= parstat_main opts
    else initCfscq (optDiskImg opts) getProcessIds >>= parstat_main opts
