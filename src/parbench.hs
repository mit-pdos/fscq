{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Concurrent
import Control.Monad
import Control.Monad (void)
import Data.List (intercalate)
import Options
import System.Clock
import System.Exit

import Fuse
import FscqFs
import CfscqFs
import GenericFs
import System.Posix.IO (defaultFileFlags)

data NoOptions = NoOptions {}
instance Options NoOptions where
  defineOptions = pure NoOptions

statOp :: NoOptions -> Filesystem -> IO ()
statOp _ fs = do
    _ <- fuseOpen fs "/" ReadOnly defaultFileFlags
    _ <- fuseGetFileStat fs "/"
    _ <- fuseOpen fs "/dir1" ReadOnly defaultFileFlags
    _ <- fuseGetFileStat fs "/dir1"
    _ <- fuseGetFileStat fs "/dir1/file1"
    return ()

statfsOp :: NoOptions -> Filesystem -> IO ()
statfsOp _ fs = void $ fuseGetFileSystemStats fs "/"

-- mini benchmarking library

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
            , pName :: String
            , pIters :: Int
            , pPar :: Int
            , pElapsedMicros :: Float }

reportRtsInfo :: RtsInfo -> String
reportRtsInfo RtsInfo{..} = show rtsN

rtsHeader :: String
rtsHeader = "RTS N"

reportPoint :: DataPoint -> String
reportPoint DataPoint{..} = intercalate "\t"
  [ reportRtsInfo pRts
  , pName
  , show pIters
  , show pPar
  , show pElapsedMicros ]

pointHeader :: String
pointHeader = intercalate "\t"
  [ rtsHeader
  , "name"
  , "iters"
  , "threads"
  , "total us" ]

getRtsInfo :: IO RtsInfo
getRtsInfo = RtsInfo <$> getNumCapabilities

data ParOptions = ParOptions
  { optFscq :: Bool
  , optDiskImg :: FilePath
  , optIters :: Int
  , optN :: Int
  , optWarmup :: Bool }

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
    <*> simpleOption "warmup" True
         "warmup by running 10 untimed iterations"

type Parcommand a = Subcommand ParOptions (IO a)

checkArgs :: [String] -> IO ()
checkArgs args = when (length args > 0) $ do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)

parcommand :: Options subcmdOpts =>
              String -> (ParOptions -> subcmdOpts -> IO a) ->
              Parcommand a
parcommand name action = subcommand name $ \opts cmdOpts args -> do
  checkArgs args
  action opts cmdOpts

parallelBench :: ParOptions -> String -> (Int -> IO a) -> IO DataPoint
parallelBench opts name act = do
  when (optWarmup opts) $ forM_ [1..(optN opts)-1] $ replicateM_ 10 . act
  totalMicros <- timeIt $ replicateInParallel
    (optN opts)
    (replicateM_ (optIters opts) . act)
  rts <- getRtsInfo
  return $ DataPoint rts name (optIters opts) (optN opts) totalMicros

withFs :: ParOptions -> (Filesystem -> IO a) -> IO a
withFs opts act =
  if optFscq opts then
    initFscq (optDiskImg opts) True getProcessIds >>= act
  else
    initCfscq (optDiskImg opts) True getProcessIds >>= act

simpleBenchmark :: Options subcmdOpts =>
                   String -> (subcmdOpts -> Filesystem -> IO a) ->
                   Parcommand ()
simpleBenchmark name act = parcommand name $ \opts cmdOpts -> do
  p <- withFs opts $ \fs -> parallelBench opts name (\_ -> act cmdOpts fs)
  putStrLn $ reportPoint p

headerCommand :: Parcommand ()
headerCommand = parcommand "print-header" $ \_ (_::NoOptions) -> do
  putStrLn pointHeader

main :: IO ()
main = runSubcommand [ simpleBenchmark "stat" statOp
                     , simpleBenchmark "statfs" statfsOp
                     , headerCommand ]
