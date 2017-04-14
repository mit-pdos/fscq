{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}

module Main where

import System.FilePath.Posix
import System.Clock
import Control.Monad
import Options
import System.Exit
import Control.Concurrent
import Control.Monad (when)
import Data.IORef

-- FFI
import Foreign.C.Types (CInt(..))
import Foreign.Ptr (FunPtr, freeHaskellFunPtr)

import Disk
import Interpreter as SeqI
import ConcurInterp as I

-- FSCQ extracted code
import qualified Errno
import qualified AsyncFS
import qualified ConcurrentFS as CFS
import qualified Rec
import FSProtocol
import FSLayout
import CCLProg

type FSprog a = Coq_cprog a
type FSrunner = forall a. FSprog (CFS.SyscallResult a) -> IO a

cachesize :: Integer
cachesize = 100000

doFScall :: I.ConcurState -> FSrunner
doFScall s p = do
  r <- I.run s p
  case r of
    CFS.Done v -> return v
    CFS.TryAgain -> error $ "system call loop failed?"
    CFS.SyscallFailed -> error $ "system call failed"

init_fs :: String -> IO (I.ConcurState, FsParams)
init_fs disk_fn = do
  ds <- init_disk disk_fn
  (mscs0, fsxp_val) <- do
      res <- SeqI.run ds $ AsyncFS._AFS__recover cachesize
      case res of
        Errno.Err _ -> error $ "recovery failed; not an fscq fs?"
        Errno.OK (mscs0, fsxp_val) -> do
          return (mscs0, fsxp_val)
  s <- I.newState ds
  fsP <- I.run s (CFS.init fsxp_val mscs0)
  return (s, fsP)

fscqGetFileStat :: I.ConcurState -> FsParams -> FilePath -> IO (Maybe Rec.Rec__Coq_data)
fscqGetFileStat s fsP (_:path) = do
  nameparts <- return $ splitDirectories path
  (r, ()) <- doFScall s $ CFS.lookup fsP nameparts
  case r of
    Errno.Err _ -> return $ Nothing
    Errno.OK (inum, isdir)
      | isdir -> return $ Nothing
      | otherwise -> do
        (attr, ()) <- doFScall s $ CFS.file_get_attr fsP inum
        return $ Just attr
fscqGetFileStat _ _ _ = return $ Nothing

readMem :: I.ConcurState -> IO Heap
readMem s = do
  readIORef (I.memory s)

foreign import ccall safe "wrapper"
  mkAction :: IO () -> IO (FunPtr (IO ()))

type CAction = IO ()
foreign import ccall "parallelize.h parallel"
  parallel :: CInt -> FunPtr CAction -> IO ()

elapsedMicros :: TimeSpec -> IO Float
elapsedMicros start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsed = (fromIntegral elapsedNanos)/1e3 :: Float in
    return elapsed

data StatOptions = StatOptions
  { optDiskImg :: String
  , optFileToStat :: String
  , optIters :: Int
  , optN :: Int
  , optMeasureSpeedup :: Bool
  , optReadMem :: Bool
  , optPthreads :: Bool
  }

instance Options StatOptions where
  defineOptions = pure StatOptions
    <*> simpleOption "img" "disk.img"
         "path to FSCQ disk image"
    <*> simpleOption "file" "/dir1/file1"
         "path to stat repeatedly"
    <*> simpleOption "iters" 100
         "number of iterations of stat to run"
    <*> simpleOption "n" 1
         "number of parallel threads to issue stats from"
    <*> simpleOption "speedup" False
         "run with n=1 and compare performance"
    <*> simpleOption "readmem" False
         "rather than stat, just read memory"
    <*> simpleOption "pthreads" False
         "use pthreads for parallelism rather than Concurrent Haskell"

evalAndDiscard :: IO a -> IO ()
evalAndDiscard act = do
  v <- act
  _ <- return $! v
  return ()

runInThread :: IO a -> IO (MVar a)
runInThread act = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    v <- act
    putMVar m v
  return m

replicateInParallel :: Int -> IO () -> IO ()
replicateInParallel n act = do
  ms <- replicateM n . runInThread $ act
  forM_ ms takeMVar

replicateInParallelC :: Int -> IO () -> IO ()
replicateInParallelC n act = do
  cAct <- mkAction act
  parallel (fromIntegral n) cAct
  freeHaskellFunPtr cAct

statOp :: StatOptions -> (ConcurState, FsParams) -> IO ()
statOp opts (s, fsP) = do
  if optReadMem opts then evalAndDiscard $ readMem s
    else evalAndDiscard $ fscqGetFileStat s fsP (optFileToStat opts)

timeParallel :: StatOptions -> Int -> IO () -> IO Float
timeParallel opts par op = do
  start <- getTime Monotonic
  replicatePar <- return $ if optPthreads opts then replicateInParallelC else replicateInParallel
  replicatePar par . replicateM_ (optIters opts) $ op
  totalTime <- elapsedMicros start
  return totalTime

parallelIters :: StatOptions -> Int
parallelIters opts = optIters opts * optN opts

seqIters :: StatOptions -> Int
seqIters opts = optIters opts

main :: IO ()
main = runCommand $ \opts args -> do
  if length args > 0 then do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)
  else do
    fs <- init_fs $ optDiskImg opts
    op <- return $ statOp opts fs
    _ <- replicateM_ 10 op
    parTime <- timeParallel opts (optN opts) op
    timePerOp <- return $ parTime/(fromIntegral $ parallelIters opts)
    putStrLn $ show timePerOp ++ " us/op"
    when (optMeasureSpeedup opts) $ do
      seqTime <- timeParallel opts 1 op
      seqTimePerOp <- return $ seqTime/(fromIntegral $ seqIters opts)
      putStrLn $ "seq time " ++ show seqTimePerOp ++ " us/op"
      putStrLn $ "speedup of " ++ show (seqTimePerOp / timePerOp)
    return ()
