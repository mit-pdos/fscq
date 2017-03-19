{-# OPTIONS_GHC -fno-warn-orphans #-}

module ConcurInterp where

import CCLProg
import qualified Disk
import Word
import qualified Crypto.Hash.SHA256 as SHA256
import Control.Monad (when)
import Control.Concurrent.MVar
import Data.IORef
import qualified Data.Map.Strict as Map

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s = when verbose $ putStrLn s

type TID = Int

type Heap = Map.Map Coq_ident Any

data ConcurState = ConcurState
  { disk :: Disk.DiskState
  , memory :: IORef Heap
  , lock :: MVar () }

instance Show LockState where
  show Free = "Free"
  show WriteLock = "WriteLock"

interp_rtxn :: Coq_read_transaction a -> Heap -> a
interp_rtxn RDone _ = unsafeCoerce ()
interp_rtxn (RCons i txn) h =
  case Map.lookup i h of
    Nothing -> error $ "missing variable " ++ show i
    Just v -> unsafeCoerce $ (v, interp_rtxn txn h)

interp_wtxn :: Coq_write_transaction -> Heap -> Heap
interp_wtxn WDone h = h
interp_wtxn (WCons (NewVal i v) txn) h =
  Map.insert i v (interp_wtxn txn h)
  -- skip ghost updates
interp_wtxn (WCons (AbsUpd _ _) txn) h = interp_wtxn txn h
interp_wtxn (WCons (AbsMemUpd _ _ _) txn) h = interp_wtxn txn h

run_dcode :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run_dcode _ (Ret r) = do
  return r
run_dcode s (Alloc v) = do
  i <- atomicModifyIORef (memory s) $ \h ->
    let (maxIdent,_) = Map.findMax h
        i = maxIdent+1
        h' = Map.insert i v h in
        (h', i)
  debugmsg $ "Alloc -> " ++ show i
  return $ unsafeCoerce i
run_dcode s (ReadTxn txn) = do
  debugmsg $ "ReadTxn"
  h <- readIORef (memory s)
  r <- return $ interp_rtxn txn h
  return $ unsafeCoerce r
run_dcode s (AssgnTxn txn) = do
  debugmsg $ "AssgnTxn"
  atomicModifyIORef (memory s) $ \h ->
    let h' = interp_wtxn txn h in
      (h', ())
  return $ unsafeCoerce ()
run_dcode s (Write a v) = do
  debugmsg $ "Write " ++ show a ++ " " ++ show v
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
  debugmsg $ "WaitForRead " ++ show a
  val <- Disk.read_disk (disk s) a
  return $ unsafeCoerce val
run_dcode ds (Bind p1 p2) = do
  r1 <- run_dcode ds p1
  r2 <- run_dcode ds (p2 r1)
  return r2

newState :: Disk.DiskState -> IO ConcurState
newState ds = pure ConcurState
    <*> return ds
    <*> newIORef (Map.fromList [(0, unsafeCoerce ())])
    <*> newMVar ()

run :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run s p = run_dcode s p
