{-# OPTIONS_GHC -fno-warn-orphans #-}

module ConcurInterp where

import CCLProg
import qualified Disk
import Word
import qualified Crypto.Hash.SHA256 as SHA256
import Control.Monad (when)
import Control.Monad.STM
import Control.Concurrent.STM.TVar
import Control.Concurrent.MVar
import Data.IORef
import qualified Data.Map.Strict as Map

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s = when verbose $ putStrLn s

type TID = Int

type Heap = Map.Map Coq_ident (TVar Any)

data ConcurState = ConcurState
  { disk :: Disk.DiskState
  , memory :: IORef Heap
  , lock :: MVar () }

instance Show LockState where
  show Free = "Free"
  show WriteLock = "WriteLock"

interp_rtxn :: Coq_read_transaction a -> Heap -> STM a
interp_rtxn RDone _ = return . unsafeCoerce $ ()
interp_rtxn (RCons i txn) h =
  case Map.lookup i h of
    Nothing -> error $ "missing variable " ++ show i
    Just var -> do
      v <- readTVar var
      rest <- interp_rtxn txn h
      return . unsafeCoerce $ (v, rest)

interp_wtxn :: Coq_write_transaction a -> Heap -> STM ()
interp_wtxn WDone _ = return ()
interp_wtxn (WCons (NewVal i v) txn) h =
  case Map.lookup i h of
    Nothing -> error $ "write to unallocated variable " ++ show i
    Just var -> do
      writeTVar var v
      interp_wtxn txn h
  -- skip ghost updates
interp_wtxn (WCons (AbsUpd _ _) txn) h = interp_wtxn txn h
interp_wtxn (WCons (AbsMemUpd _ _ _) txn) h = interp_wtxn txn h

run_dcode :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run_dcode _ (Ret r) = do
  return r
run_dcode s (Alloc v) = do
  var <- atomically $ newTVar (unsafeCoerce v)
  atomicModifyIORef (memory s) $ \h ->
    let (i,_) = Map.findMax h
        h' = Map.insert (i+1) var h in
        (h', ())
  return $ unsafeCoerce ()
run_dcode s (ReadTxn txn) = do
  h <- readIORef (memory s)
  r <- atomically $ interp_rtxn txn h
  return $ unsafeCoerce r
run_dcode s (AssgnTxn txn) = do
  h <- readIORef (memory s)
  atomically $ interp_wtxn txn h
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
  case (l, l') of
    (Free, WriteLock) -> takeMVar (lock s)
    (WriteLock, Free) -> putMVar (lock s) ()
    (_, _) -> error $ "SetLock used incorrectly: " ++ show l ++ " " ++ show l'
  return $ unsafeCoerce l'
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
newState ds = do
  dummyVar <- atomically $ newTVar (unsafeCoerce ())
  pure ConcurState
    <*> return ds
    <*> newIORef (Map.fromList [(0, dummyVar)])
    <*> newMVar ()

run :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run s p = run_dcode s p
