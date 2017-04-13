{-# LANGUAGE RankNTypes #-}

module Main where

import System.FilePath.Posix
import System.Clock
import Control.Monad
import Options
import System.Exit
import Control.Concurrent

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
      putStrLn $ "Recovering file system"
      res <- SeqI.run ds $ AsyncFS._AFS__recover cachesize
      case res of
        Errno.Err _ -> error $ "recovery failed; not an fscq fs?"
        Errno.OK (mscs0, fsxp_val) -> do
          return (mscs0, fsxp_val)
  putStrLn $ "Starting file system, " ++ (show $ coq_FSXPMaxBlock fsxp_val) ++ " blocks " ++ "magic " ++ (show $ coq_FSXPMagic fsxp_val)
  s <- I.newState ds
  fsP <- I.run s (CFS.init fsxp_val mscs0)
  return (s, fsP)

fscqGetFileStat :: I.ConcurState -> FsParams -> FilePath -> IO (Maybe Rec.Rec__Coq_data)
fscqGetFileStat s fsP (_:path)
  | otherwise = do
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
  }

instance Options StatOptions where
  defineOptions = pure StatOptions
    <*> simpleOption "img" "disk.img"
         "path to FSCQ disk image"
    <*> simpleOption "file" "/tmp/fscq/dir1/file1"
         "path to stat repeatedly"
    <*> simpleOption "iters" 100
         "number of iterations of stat to run"
    <*> simpleOption "n" 1
         "number of parallel threads to issue stats from"

repeatOp :: Int -> IO a -> IO ()
repeatOp n act = do
  replicateM_ n $ do
    v <- act
    return $! v
  return ()

runInThread :: IO a -> IO (MVar a)
runInThread act = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    v <- act
    putMVar m v
  return m

main :: IO ()
main = runCommand $ \opts args -> do
  if length args > 0 then do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)
  else do
    (s, fsP) <- init_fs $ optDiskImg opts
    iters <- return $ optIters opts
    par <- return $ optN opts
    start <- getTime Monotonic
    ms <- replicateM par . runInThread . repeatOp iters $ fscqGetFileStat s fsP (optFileToStat opts)
    forM_ ms takeMVar
    totalTime <- elapsedMicros start
    timePerOp <- return $ totalTime/(fromIntegral $ iters * par)
    putStrLn $ "took " ++ show timePerOp ++ " us/op"
    return ()
