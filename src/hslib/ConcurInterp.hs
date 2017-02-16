module ConcurInterp where

import CCLProg
import qualified Disk
import Word
import qualified Crypto.Hash.SHA256 as SHA256
import Control.Monad (when)
import Control.Concurrent.ReadWriteLock as RWL
import Data.IORef

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s = when verbose $ putStrLn s

type TID = Int

data ConcurState = ConcurState
  { disk :: Disk.DiskState
  , memory :: IORef Any
  , lock :: RWLock
  , has_writer :: IORef Bool }

run_dcode :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run_dcode _ (Ret r) = do
  debugmsg $ "Done"
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
run_dcode s (Hash sz (W64 w)) =
  run_dcode s (Hash sz (W $ fromIntegral w))
run_dcode _ (Hash sz (W w)) = do
  debugmsg $ "Hash " ++ (show sz) ++ " " ++ (show w)
  wbs <- Disk.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  h <- return $ SHA256.hash wbs
  ih <- Disk.bs2i h
  return $ unsafeCoerce $ W ih
run_dcode s (SetLock l) = do
  case l of
    Free -> do
      writing <- readIORef (has_writer s)
      if writing
        then RWL.releaseWrite (lock s)
        else RWL.releaseRead (lock s)
      writeIORef (has_writer s) False
    ReadLock -> RWL.acquireRead (lock s)
    WriteLock -> do
      RWL.acquireWrite (lock s)
  writeIORef (has_writer s) True
  return $ unsafeCoerce ()
run_dcode _ (BeginRead _) = do
  -- TODO: implement efficiently
  return $ unsafeCoerce ()
run_dcode s (WaitForRead a) = do
  val <- Disk.read_disk (disk s) a
  return $ unsafeCoerce val
run_dcode ds (Bind p1 p2) = do
  debugmsg $ "Bind"
  r1 <- run_dcode ds p1
  r2 <- run_dcode ds (p2 r1)
  return r2

newState :: Disk.DiskState -> IO ConcurState
newState ds =
  pure ConcurState
  <*> return ds
  <*> unsafeCoerce (newIORef ())
  <*> RWL.new
  <*> newIORef False

run :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run s p = run_dcode s p
