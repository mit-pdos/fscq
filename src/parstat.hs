{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}

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
import qualified Prog
import qualified BFile
import qualified AsyncFS
import qualified FSLayout
import qualified ConcurrentFS as CFS
import qualified Rec
import FSProtocol hiding (fsxp)
import CCLProg

type FSprog a = Coq_cprog a
type FSrunner = forall a. FSprog (CFS.SyscallResult a) -> IO a

type MSCS = BFile.BFILE__Coq_memstate
type FSCQprog a = (MSCS -> Prog.Coq_prog (MSCS, a))
type FSCQrunner = forall a. FSCQprog a -> IO a
doSeqCall :: DiskState -> MVar MSCS -> FSCQrunner
doSeqCall ds ref f = do
  s <- takeMVar ref
  (s', r) <- SeqI.run ds $ f s
  putMVar ref s'
  return r

cachesize :: Integer
cachesize = 100000

doFScall :: I.ConcurState -> FSrunner
doFScall s p = do
  r <- I.run s p
  case r of
    CFS.Done v -> return v
    CFS.TryAgain -> error $ "system call loop failed?"
    CFS.SyscallFailed -> error $ "system call failed"

class Filesystem a where
  getFileStat :: a -> FilePath -> IO (Maybe Rec.Rec__Coq_data)
  openFile :: a -> FilePath -> IO (Maybe Integer)
  readMem :: a -> IO ()

data Anyfs = forall a. Filesystem a => Anyfs a

instance Filesystem Anyfs where
  getFileStat (Anyfs fs) = getFileStat fs
  openFile (Anyfs fs) = openFile fs
  readMem (Anyfs fs) = readMem fs

data CfscqFs = CfscqFs I.ConcurState FsParams

init_cfscq :: String -> IO CfscqFs
init_cfscq disk_fn = do
  ds <- init_disk disk_fn
  (mscs0, fsxp_val) <- do
      res <- SeqI.run ds $ AsyncFS._AFS__recover cachesize
      case res of
        Errno.Err _ -> error $ "recovery failed; not an fscq fs?"
        Errno.OK (mscs0, fsxp_val) -> do
          return (mscs0, fsxp_val)
  s <- I.newState ds
  fsP <- I.run s (CFS.init fsxp_val mscs0)
  return $ CfscqFs s fsP

instance Filesystem CfscqFs where
  getFileStat (CfscqFs s fsP) (_:path) = do
    nameparts <- return $ splitDirectories path
    (r, ()) <- doFScall s $ CFS.lookup fsP nameparts
    case r of
      Errno.Err _ -> return $ Nothing
      Errno.OK (inum, isdir)
        | isdir -> return $ Nothing
        | otherwise -> do
          (attr, ()) <- doFScall s $ CFS.file_get_attr fsP inum
          return $ Just attr
  getFileStat _ _ = return $ Nothing

  openFile (CfscqFs s fsP) (_:path) = do
    nameparts <- return $ splitDirectories path
    (r, ()) <- doFScall s $ CFS.lookup fsP nameparts
    case r of
      Errno.Err _ -> return $ Nothing
      Errno.OK (inum, isdir)
        | isdir -> return $ Nothing
        | otherwise -> return $ Just inum
  openFile _ _  = return $ Nothing

  readMem (CfscqFs s _) = readIORef (I.memory s) >> return ()

data FscqFs = FscqFs FSCQrunner (MVar FSLayout.Coq_fs_xparams)

init_fscq :: String -> IO FscqFs
init_fscq disk_fn = do
  ds <- init_disk disk_fn
  (mscs0, fsxp_val) <- do
      res <- SeqI.run ds $ AsyncFS._AFS__recover cachesize
      case res of
        Errno.Err _ -> error $ "recovery failed; not an fscq fs?"
        Errno.OK (mscs0, fsxp_val) -> do
          return (mscs0, fsxp_val)
  m_mscs <- newMVar mscs0
  m_fsxp <- newMVar fsxp_val
  return $ FscqFs (doSeqCall ds m_mscs) m_fsxp

instance Filesystem FscqFs where

  getFileStat (FscqFs fr m_fsxp) (_:path) = withMVar m_fsxp $ \fsxp -> do
    nameparts <- return $ splitDirectories path
    (r, ()) <- fr $ AsyncFS._AFS__lookup fsxp (FSLayout.coq_FSXPRootInum fsxp) nameparts
    case r of
      Errno.Err _ -> return $ Nothing
      Errno.OK (inum, isdir)
        | isdir -> return $ Nothing
        | otherwise -> do
          (attr, ()) <- fr $ AsyncFS._AFS__file_get_attr fsxp inum
          return $ Just attr
  getFileStat _ _ = return $ Nothing

  openFile (FscqFs fr m_fsxp) (_:path) = withMVar m_fsxp $ \fsxp -> do
    nameparts <- return $ splitDirectories path
    (r, ()) <- fr $ AsyncFS._AFS__lookup fsxp (FSLayout.coq_FSXPRootInum fsxp) nameparts
    case r of
      Errno.Err _ -> return $ Nothing
      Errno.OK (inum, isdir)
        | isdir -> return $ Nothing
        | otherwise -> return $ Just inum
  openFile _ _ = return $ Nothing

  readMem (FscqFs _ m_fsxp) = withMVar m_fsxp $ \_ -> return ()

foreign import ccall safe "wrapper"
  mkAction :: IO () -> IO (FunPtr (IO ()))

type CAction = IO ()
foreign import ccall "parallelize.h parallel"
  parallel :: CInt -> CInt -> FunPtr CAction -> IO ()

elapsedMicros :: TimeSpec -> IO Float
elapsedMicros start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsed = (fromIntegral elapsedNanos)/1e3 :: Float in
    return elapsed

data StatOptions = StatOptions
  { optFscq :: Bool
  , optDiskImg :: String
  , optIters :: Int
  , optN :: Int
  , optMeasureSpeedup :: Bool
  , optReadMem :: Bool
  , optPthreads :: Bool
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
    <*> simpleOption "pthreads" False
         "use pthreads for parallelism rather than Concurrent Haskell"

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

replicateInParallelIterateFFI :: Int -> Int -> IO () -> IO ()
replicateInParallelIterateFFI n iters act = do
  cAct <- mkAction act
  parallel (fromIntegral n) (fromIntegral iters) cAct
  freeHaskellFunPtr cAct

statOp :: Filesystem a => StatOptions -> a -> IO ()
statOp opts fs =
  if optReadMem opts then readMem fs
    else do
      _ <- openFile fs "/"
      _ <- getFileStat fs "/"
      _ <- openFile fs "/dir1"
      _ <- getFileStat fs "/dir1"
      _ <- getFileStat fs "/dir1/file1"
      return ()

timeParallel :: StatOptions -> Int -> Int -> IO () -> IO Float
timeParallel opts par iters op = do
  replicatePar <- return $ if optPthreads opts then replicateInParallelIterateFFI
                           else replicateInParallelIterate
  start <- getTime Monotonic
  replicatePar par iters op
  totalTime <- elapsedMicros start
  return totalTime

parallelIters :: StatOptions -> Int
parallelIters opts = optIters opts * optN opts

seqIters :: StatOptions -> Int
seqIters opts = optIters opts

init_fs :: StatOptions -> IO Anyfs
init_fs opts = let disk_fn = optDiskImg opts in
                 if optFscq opts
                 then Anyfs <$> init_fscq disk_fn
                 else Anyfs <$> init_cfscq disk_fn

main :: IO ()
main = runCommand $ \opts args -> do
  if length args > 0 then do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)
  else do
    fs <- init_fs opts
    op <- return $ statOp opts fs
    _ <- timeParallel opts 1 10 op
    parTime <- timeParallel opts (optN opts) (optIters opts) op
    timePerOp <- return $ parTime/(fromIntegral $ parallelIters opts)
    putStrLn $ show timePerOp ++ " us/op"
    when (optMeasureSpeedup opts) $ do
      seqTime <- timeParallel opts 1 (optIters opts) op
      seqTimePerOp <- return $ seqTime/(fromIntegral $ seqIters opts)
      putStrLn $ "seq time " ++ show seqTimePerOp ++ " us/op"
      putStrLn $ "speedup of " ++ show (seqTimePerOp / timePerOp)
    return ()
