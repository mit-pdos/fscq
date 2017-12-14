{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}

module Main where

import System.Clock
import Control.Monad
import Options
import System.Exit
import Control.Concurrent
import Control.Monad (void)

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

timeIt :: IO a -> IO Float
timeIt act = do
  start <- getTime Monotonic
  _ <- act
  totalTime <- elapsedMicros start
  return totalTime

statOp :: FuseOperations fh -> IO ()
statOp fs = do
    _ <- fuseOpen fs "/" ReadOnly defaultFileFlags
    _ <- fuseGetFileStat fs "/"
    _ <- fuseOpen fs "/dir1" ReadOnly defaultFileFlags
    _ <- fuseGetFileStat fs "/dir1"
    _ <- fuseGetFileStat fs "/dir1/file1"
    return ()

statfsOp :: FuseOperations fh -> IO ()
statfsOp fs = void $ fuseGetFileSystemStats fs "/"

data ParOptions = ParOptions
  { optFscq :: Bool
  , optDiskImg :: FilePath
  , optIters :: Int
  , optN :: Int }

instance Options ParOptions where
  defineOptions = pure ParOptions
    <*> simpleOption "fscq" False
        "run sequential FSCQ"
    <*> simpleOption "img" "disk.img"
         "path to FSCQ disk image"
    <*> simpleOption "iters" 100
         "number of iterations of stat to run"
    <*> simpleOption "n" 1
         "number of parallel threads to issue stats from"

runInThread :: IO a -> IO (MVar a)
runInThread act = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    v <- act
    putMVar m v
  return m

-- replicateInParallel par iters act runs act in n parallel copies, passing
-- 0..n-1 to each copy
replicateInParallel :: Int -> (Int -> IO a) -> IO [a]
replicateInParallel par act = do
  ms <- mapM (runInThread . act) [0..par-1]
  mapM takeMVar ms

data RtsInfo =
  RtsInfo { rtsN :: Int }

data DataPoint =
  DataPoint { pRts :: RtsInfo
            , pIters :: Int
            , pPar :: Int
            , pElapsedMicros :: Float }

reportRtsInfo :: RtsInfo -> String
reportRtsInfo RtsInfo{..} = show rtsN

rtsHeader :: String
rtsHeader = "RTS N"

reportPoint :: DataPoint -> String
reportPoint DataPoint{..} = reportRtsInfo pRts ++ "\t" ++
  show pIters ++ "\t" ++
  show pPar ++ "\t" ++
  show pElapsedMicros

pointHeader :: String
pointHeader = rtsHeader ++ "\t" ++ "iters\tthreads\ttotal us"

getRtsInfo :: IO RtsInfo
getRtsInfo = RtsInfo <$> getNumCapabilities

parallelBench :: ParOptions -> (Int -> IO a) -> IO DataPoint
parallelBench opts act = do
  totalMicros <- timeIt $ replicateInParallel
    (optN opts)
    (replicateM_ (optIters opts) . act)
  rts <- getRtsInfo
  return $ DataPoint rts (optIters opts) (optN opts) totalMicros

withFs :: ParOptions -> (forall fh. FuseOperations fh -> IO a) -> IO a
withFs opts act =
  if optFscq opts then
    initFscq (optDiskImg opts) True getProcessIds >>= act
  else
    initCfscq (optDiskImg opts) True getProcessIds >>= act

main :: IO ()
main = runCommand $ \opts args -> do
  if length args > 0 then do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)
  else do
    p <- withFs opts $ \fs -> parallelBench opts (\_ -> statOp fs)
    putStrLn $ reportPoint p
