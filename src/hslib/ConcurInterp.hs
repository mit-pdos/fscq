{-# OPTIONS_GHC -fno-warn-orphans #-}

module ConcurInterp where

import CCLProg
import qualified Disk
import Word
import qualified Crypto.Hash.SHA256 as SHA256
import Control.Monad (when)
-- import Control.Concurrent.MVar
import Data.IORef
import ReadWriteLock as RWL

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s = when verbose $ putStrLn s

type TID = Int

data ConcurState = ConcurState
  { disk :: Disk.DiskState
  , memory :: IORef Any
  , lock :: RWLock
  , shouldUpdateMem :: IORef Bool }

instance Show LockState where
  show Free = "Free"
  show ReadLock = "ReadLock"
  show WriteLock = "WriteLock"

run_dcode :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run_dcode _ (Ret r) = do
  return r
run_dcode s (Assgn m) = do
  writeIORef (memory s) m
  return $ unsafeCoerce ()
run_dcode s (Get) = do
  m <- readIORef (memory s)
  return $ unsafeCoerce m
run_dcode _ (GhostUpdate _) = do
  return $ unsafeCoerce ()
run_dcode s (Write a v) = do
  Disk.write_disk (disk s) a v
  return $ unsafeCoerce ()
run_dcode ds (Hash sz (W64 w)) = run_dcode ds (Hash sz (W $ fromIntegral w))
run_dcode ds (Hash sz (W w)) = do
  debugmsg $ "Hash " ++ (show sz) ++ " W " ++ (show w)
  bs <- Word.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  run_dcode ds $ Hash sz (WBS bs)
run_dcode _ (Hash sz (WBS bs)) = do
  debugmsg $ "Hash " ++ (show sz) ++ " BS " ++ (show bs)
  return $ unsafeCoerce $ WBS $ SHA256.hash bs
run_dcode s (SetLock l l') = do
  debugmsg $ "SetLock " ++ show l ++ " " ++ show l'
  l'' <- case (l, l') of
    (Free, ReadLock) -> do
      -- RWL.acquireRead (lock s)
      return l'
    (Free, WriteLock) -> do
      RWL.acquireWrite (lock s)
      return l'
    (ReadLock, Free) -> do
      -- RWL.releaseRead (lock s)
      return l'
    (WriteLock, Free) -> do
      RWL.releaseWrite (lock s)
      return l'
    (ReadLock, WriteLock) -> do
      doUpdate <- readIORef (shouldUpdateMem s)
      if doUpdate then do
        RWL.acquireWrite (lock s)
        return WriteLock
      else return ReadLock
    (_, _) -> error $ "SetLock used incorrectly: " ++ show l ++ " " ++ show l'
  return $ unsafeCoerce l''
run_dcode _ (BeginRead _) = do
  -- TODO: implement efficiently
  debugmsg $ "BeginRead"
  return $ unsafeCoerce ()
run_dcode s (WaitForRead a) = do
  val <- Disk.read_disk (disk s) a
  return $ unsafeCoerce val
run_dcode ds (Bind p1 p2) = do
  r1 <- run_dcode ds p1
  r2 <- run_dcode ds (p2 r1)
  return r2

newState :: Disk.DiskState -> IO ConcurState
newState ds =
  pure ConcurState
  <*> return ds
  <*> newIORef (unsafeCoerce ())
  <*> RWL.new
  <*> newIORef True

run :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run s p = run_dcode s p
