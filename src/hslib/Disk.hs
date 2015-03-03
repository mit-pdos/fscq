{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Disk where

import System.IO
import System.Posix.Types
import System.Posix.IO
import System.Posix.Unistd
import System.Posix.Files
import Word
import qualified Data.ByteString.Internal as BSI
import qualified GHC.Integer.GMP.Internals as GMPI
import GHC.Exts
import Foreign.Marshal.Alloc
import Data.Word
import Data.IORef

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

-- DiskStats counts the number of reads, writes, and syncs
data DiskStats =
  Stats !Word !Word !Word

data DiskState =
  S !Fd !(IORef DiskStats) !(IORef Bool)

bumpRead :: IORef DiskStats -> IO ()
bumpRead sr = do
  Stats r w s <- readIORef sr
  writeIORef sr $ Stats (r+1) w s

bumpWrite :: IORef DiskStats -> IO ()
bumpWrite sr = do
  Stats r w s <- readIORef sr
  writeIORef sr $ Stats r (w+1) s

bumpSync :: IORef DiskStats -> IO ()
bumpSync sr = do
  Stats r w s <- readIORef sr
  writeIORef sr $ Stats r w (s+1)

-- For a more efficient array implementation, perhaps worth checking out:
-- http://www.macs.hw.ac.uk/~hwloidl/hackspace/ghc-6.12-eden-gumsmp-MSA-IFL13/libraries/dph/dph-base/Data/Array/Parallel/Arr/BUArr.hs

-- Some notes on memory-efficient file IO in Haskell:
-- http://stackoverflow.com/questions/26333815/why-do-hgetbuf-hputbuf-etc-allocate-memory

-- Snippets of ByteArray# manipulation code from GHC's
-- testsuite/tests/lib/integer/integerGmpInternals.hs

buf2i :: Ptr Word8 -> IO Integer
buf2i (GHC.Exts.Ptr a) = do
  GMPI.importIntegerFromAddr a 4096## 0#

i2buf :: Integer -> Ptr Word8 -> IO ()
i2buf i (GHC.Exts.Ptr a) = do
  _ <- BSI.memset (GHC.Exts.Ptr a) 0 4096
  _ <- GMPI.exportIntegerToAddr i a 0#
  return ()

read_disk :: DiskState -> Coq_word -> IO Coq_word
read_disk ds (W a) = read_disk ds (W64 $ fromIntegral a)
read_disk (S fd sr _) (W64 a) = do
  debugmsg $ "read(" ++ (show a) ++ ")"
  bumpRead sr
  allocaBytes 4096 $ \buf -> do
    _ <- fdSeek fd AbsoluteSeek $ fromIntegral $ 4096*a
    cc <- fdReadBuf fd buf 4096
    if cc == 4096 then
      do
        i <- buf2i buf
        return $ W i
    else
      do
        error $ "read_disk: short read: " ++ (show cc) ++ " @ " ++ (show a)

write_disk :: DiskState -> Coq_word -> Coq_word -> IO ()
write_disk ds (W a) v = write_disk ds (W64 $ fromIntegral a) v
write_disk _ (W64 _) (W64 _) = error "write_disk: short value"
write_disk (S fd sr dirty) (W64 a) (W v) = do
  -- maybeCrash
  debugmsg $ "write(" ++ (show a) ++ ")"
  bumpWrite sr
  writeIORef dirty True
  allocaBytes 4096 $ \buf -> do
    _ <- fdSeek fd AbsoluteSeek $ fromIntegral $ 4096*a
    i2buf v buf
    cc <- fdWriteBuf fd buf 4096
    if cc == 4096 then
      return ()
    else
      do
        error $ "write_disk: short write: " ++ (show cc) ++ " @ " ++ (show a)

sync_disk :: DiskState -> IO ()
sync_disk (S fd sr dirty) = do
  debugmsg $ "sync()"
  isdirty <- readIORef dirty
  if isdirty then do
    bumpSync sr
    -- fileSynchroniseDataOnly fd
    writeIORef dirty False
  else
    return ()

clear_stats :: DiskState -> IO ()
clear_stats (S _ sr _) = do
  writeIORef sr $ Stats 0 0 0

get_stats :: DiskState -> IO DiskStats
get_stats (S _ sr _) = do
  s <- readIORef sr
  return s

init_disk :: FilePath -> IO DiskState
init_disk disk_fn = do
  fd <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  sr <- newIORef $ Stats 0 0 0
  dirty <- newIORef False
  return $ S fd sr dirty

set_nblocks_disk :: DiskState -> Int -> IO ()
set_nblocks_disk (S fd _ _) nblocks = do
  setFdSize fd $ fromIntegral $ nblocks * 4096
  return ()

close_disk :: DiskState -> IO DiskStats
close_disk (S fd sr _) = do
  closeFd fd
  s <- readIORef sr
  return s

print_stats :: DiskStats -> IO ()
print_stats (Stats r w s) = do
  putStrLn $ "Disk I/O stats:"
  putStrLn $ "Reads:  " ++ (show r)
  putStrLn $ "Writes: " ++ (show w)
  putStrLn $ "Syncs:  " ++ (show s)
