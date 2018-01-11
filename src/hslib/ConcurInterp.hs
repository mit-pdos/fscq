{-# OPTIONS_GHC -fno-warn-orphans #-}

module ConcurInterp where

import           CCLProg
import           Data.Word
import qualified Disk
import           Timings
import           Word
-- import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.Digest.CRC32 as CRC32
import           Control.Monad (when)
import           Control.Concurrent (forkIO)
import           Control.Concurrent.MVar
import           Data.IORef
import           System.CPUTime.Rdtsc
import           System.IO (hPutStrLn, stderr)
import qualified Data.Map.Strict as Map

verbose :: Bool
verbose = False

timing :: Bool
timing = True

debugmsg :: String -> IO ()
debugmsg s = when verbose $ hPutStrLn stderr s

type TID = Int

type Heap = Map.Map Coq_ident Any

data ConcurState = ConcurState
  { disk :: Disk.DiskState
  , memory :: IORef Heap
  , pendingReads :: IORef (Map.Map Integer (MVar Coq_word))
  , timings :: IORef Timings
  , lock :: MVar () }

instance Show LocalLock where
  show Unacquired = "Unacquired"
  show Locked = "Locked"

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

crc32_word_update :: Word32 -> Integer -> Coq_word -> IO Word32
crc32_word_update c sz (W w) = do
  bs <- Word.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  crc32_word_update c sz (WBS bs)
crc32_word_update c sz (W64 w) = crc32_word_update c sz $ W $ fromIntegral w
crc32_word_update c _ (WBS bs) = return $ CRC32.crc32Update c bs

schedule_read :: ConcurState -> Integer -> IO ()
schedule_read s a = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    val <- Disk.read_disk (disk s) a
    putMVar m val
  modifyIORef (pendingReads s) (Map.insert a m)
  return ()

get_read :: ConcurState -> Integer -> IO Coq_word
get_read s a = do
  rds <- readIORef (pendingReads s)
  case Map.lookup a rds of
    Nothing -> error $ "did not start read for " ++ show a
    Just m -> do
      val <- readMVar m
      modifyIORef (pendingReads s) (Map.delete a)
      return val

wait_for_read :: ConcurState -> Integer -> IO ()
wait_for_read s a = do
  rds <- readIORef (pendingReads s)
  case Map.lookup a rds of
    -- should be safe regardless of pending reads
    Nothing -> return ()
    Just m -> do
      _ <- readMVar m
      return ()

run_dcode :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run_dcode _ (Ret r) = {-# SCC "dcode-ret" #-} do
  return r
run_dcode cs (Debug s n) = {-# SCC "dcode-debug" #-} do
  modifyIORef' (timings cs) (insertTime s n)
  return $ unsafeCoerce ()
run_dcode _ (Rdtsc) = {-# SCC "dcode-rdtsc" #-} do
  if timing then do
    r <- rdtsc
    return $ unsafeCoerce (fromIntegral r :: Integer)
  else
    return $ unsafeCoerce (0::Integer)
run_dcode s (Alloc v) = do
  i <- atomicModifyIORef (memory s) $ \h ->
    let (maxIdent,_) = Map.findMax h
        i = maxIdent+1
        h' = Map.insert i v h in
        (h', i)
  debugmsg $ "Alloc -> " ++ show i
  return $ unsafeCoerce i
run_dcode s (ReadTxn txn) = do
  debugmsg "ReadTxn"
  h <- readIORef (memory s)
  r <- return $ interp_rtxn txn h
  return $ unsafeCoerce r
run_dcode s (AssgnTxn txn) = {-# SCC "dcode-assgn" #-} do
  debugmsg $ "AssgnTxn"
  atomicModifyIORef (memory s) $ \h ->
    let h' = interp_wtxn txn h in
      (h', ())
  return $ unsafeCoerce ()
run_dcode s (Write a v) = do
  debugmsg $ "Write " ++ show a ++ " " ++ show v
  Disk.write_disk (disk s) a v
  return $ unsafeCoerce ()
run_dcode _ (Hash sz w) = do
  debugmsg $ "Hash " ++ (show sz)
  c <- crc32_word_update 0 sz w
  return $ unsafeCoerce $ W $ fromIntegral c
run_dcode s (SetLock l l') = do
  debugmsg $ "SetLock " ++ show l ++ " " ++ show l'
  case (l, l') of
    (Unacquired, Locked) -> takeMVar (lock s)
    (Locked, Unacquired) -> putMVar (lock s) ()
    (_, _) -> error $ "SetLock used incorrectly: " ++ show l ++ " " ++ show l'
  return $ unsafeCoerce l'
run_dcode s (BeginRead a) = do
  debugmsg $ "BeginRead"
  schedule_read s a
  return $ unsafeCoerce ()
run_dcode s (WaitForRead a) = do
  debugmsg $ "WaitForRead " ++ show a
  val <- get_read s a
  return $ unsafeCoerce val
run_dcode s (YieldTillReady a) = do
  debugmsg $ "YieldTillReady " ++ show a
  wait_for_read s a
  return $ unsafeCoerce ()
run_dcode ds (Bind p1 p2) = {-# SCC "dcode-bind" #-} do
  r1 <- run_dcode ds p1
  r2 <- run_dcode ds (p2 r1)
  return r2

newState :: Disk.DiskState -> IO ConcurState
newState ds = pure ConcurState
    <*> return ds
    <*> newIORef (Map.fromList [(0, unsafeCoerce ())])
    <*> newIORef Map.empty
    <*> newIORef Map.empty
    <*> newMVar ()

run :: ConcurState -> CCLProg.Coq_cprog a -> IO a
run s p = run_dcode s p
