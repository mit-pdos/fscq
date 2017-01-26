{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Disk where

import System.IO
import System.Posix.Types
import System.Posix.IO
import System.Posix.Unistd
import System.Posix.Files
import Word
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BSI
import qualified GHC.Integer.GMP.Internals as GMPI
import qualified Foreign.C.Types
import GHC.Exts
import Foreign.ForeignPtr
import Foreign.Marshal.Alloc
import Data.Word
import Data.IORef

verbose :: Bool
verbose = True

reallySync :: Bool
reallySync = True

debugSyncs :: Bool
debugSyncs = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

-- DiskStats counts the number of reads, writes, and syncs
data DiskStats =
  Stats !Word !Word !Word

-- FlushLog is used to track writes for empirical crash recovery testing
data FlushLog =
  FL ![(Integer, Coq_word)] ![[(Integer, Coq_word)]]
  -- The first list is the list of writes since the last flush
  -- The second list is the list of previous flushed write groups

data DiskState =
  S !Fd !(IORef DiskStats) !(Maybe (IORef FlushLog))

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

logWrite :: Maybe (IORef FlushLog) -> Integer -> Coq_word -> IO ()
logWrite Nothing _ _ = return ()
logWrite (Just fl) a v = do
  FL writes flushed <- readIORef fl
  writeIORef fl $ FL ((a, v) : writes) flushed

logFlush :: Maybe (IORef FlushLog) -> IO ()
logFlush Nothing = return ()
logFlush (Just fl) = do
  FL writes flushed <- readIORef fl
  writeIORef fl $ FL [] (writes : flushed)

-- For a more efficient array implementation, perhaps worth checking out:
-- http://www.macs.hw.ac.uk/~hwloidl/hackspace/ghc-6.12-eden-gumsmp-MSA-IFL13/libraries/dph/dph-base/Data/Array/Parallel/Arr/BUArr.hs

-- Some notes on memory-efficient file IO in Haskell:
-- http://stackoverflow.com/questions/26333815/why-do-hgetbuf-hputbuf-etc-allocate-memory

-- Snippets of ByteArray# manipulation code from GHC's
-- testsuite/tests/lib/integer/integerGmpInternals.hs

buf2i :: Int -> Word -> Ptr Word8 -> IO Integer
buf2i (I# offset) (W# nbytes) (GHC.Exts.Ptr a) = do
  GMPI.importIntegerFromAddr (plusAddr# a offset) nbytes 0#

i2buf :: Integer -> Foreign.C.Types.CSize -> Ptr Word8 -> IO ()
i2buf i nbytes (GHC.Exts.Ptr a) = do
  _ <- BSI.memset (GHC.Exts.Ptr a) 0 nbytes
  _ <- GMPI.exportIntegerToAddr i a 0#
  return ()

bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp offset len) = withForeignPtr fp $ buf2i offset $ fromIntegral len

i2bs :: Integer -> Int -> IO BS.ByteString
i2bs i nbytes = BSI.create nbytes $ i2buf i $ fromIntegral nbytes

read_disk :: DiskState -> Integer -> IO Coq_word
read_disk (S fd sr _) a = do
  debugmsg $ "read(" ++ (show a) ++ ")"
  bumpRead sr
  allocaBytes 4096 $ \buf -> do
    _ <- fdSeek fd AbsoluteSeek $ fromIntegral $ 4096*a
    cc <- fdReadBuf fd buf 4096
    if cc == 4096 then
      do
        i <- buf2i 0 4096 buf
        return $ W i
    else
      do
        error $ "read_disk: short read: " ++ (show cc) ++ " @ " ++ (show a)

write_disk :: DiskState -> Integer -> Coq_word -> IO ()
write_disk _ _ (W64 _) = error "write_disk: short value"
write_disk (S fd sr fl) a (W v) = do
  -- maybeCrash
  debugmsg $ "write(" ++ (show a) ++ ")"
  bumpWrite sr
  logWrite fl a (W v)
  allocaBytes 4096 $ \buf -> do
    _ <- fdSeek fd AbsoluteSeek $ fromIntegral $ 4096*a
    i2buf v 4096 buf
    cc <- fdWriteBuf fd buf 4096
    if cc == 4096 then
      return ()
    else
      do
        error $ "write_disk: short write: " ++ (show cc) ++ " @ " ++ (show a)

sync_disk :: DiskState -> IO ()
sync_disk (S fd sr fl) = do
  debugmsg $ "sync()"

  if debugSyncs then do
    callstack <- currentCallStack
    putStrLn $ "Sync call stack:"
    _ <- mapM (\loc -> putStrLn $ "  " ++ loc) callstack
    return ()
  else
    return ()

  bumpSync sr
  logFlush fl
  if reallySync then
    fileSynchroniseDataOnly fd
  else
    return ()

trim_disk :: DiskState -> Integer -> IO ()
trim_disk _ a = do
  debugmsg $ "trim(" ++ (show a) ++ ")"
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
  return $ S fd sr Nothing

init_disk_crashlog :: FilePath -> IO DiskState
init_disk_crashlog disk_fn = do
  fd <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  sr <- newIORef $ Stats 0 0 0
  fl <- newIORef $ FL [] []
  return $ S fd sr $ Just fl

set_nblocks_disk :: DiskState -> Int -> IO ()
set_nblocks_disk (S fd _ _) nblocks = do
  setFdSize fd $ fromIntegral $ nblocks * 4096
  return ()

close_disk :: DiskState -> IO DiskStats
close_disk (S fd sr _) = do
  closeFd fd
  s <- readIORef sr
  return s

get_flush_log :: DiskState -> IO [[(Integer, Coq_word)]]
get_flush_log (S _ _ Nothing) = return []
get_flush_log (S _ _ (Just fl)) = do
  FL writes flushes <- readIORef fl
  return (writes : flushes)

clear_flush_log :: DiskState -> IO [[(Integer, Coq_word)]]
clear_flush_log (S _ _ Nothing) = return []
clear_flush_log (S _ _ (Just fl)) = do
  FL writes flushes <- readIORef fl
  writeIORef fl $ FL [] []
  return (writes : flushes)

print_stats :: DiskStats -> IO ()
print_stats (Stats r w s) = do
  putStrLn $ "Disk I/O stats:"
  putStrLn $ "Reads:  " ++ (show r)
  putStrLn $ "Writes: " ++ (show w)
  putStrLn $ "Syncs:  " ++ (show s)
