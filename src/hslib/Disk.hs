{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Disk where

import System.IO
import System.Posix.Types
import System.Posix.IO
import System.Posix.Unistd
import Word
import qualified Data.ByteString.Internal as BSI
import qualified GHC.Integer.GMP.Internals as GMPI
import GHC.Exts
import Foreign.Marshal.Alloc
import Data.Word

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

-- For a more efficient array implementation, perhaps worth checking out:
-- http://www.macs.hw.ac.uk/~hwloidl/hackspace/ghc-6.12-eden-gumsmp-MSA-IFL13/libraries/dph/dph-base/Data/Array/Parallel/Arr/BUArr.hs

-- Some notes on memory-efficient file IO in Haskell:
-- http://stackoverflow.com/questions/26333815/why-do-hgetbuf-hputbuf-etc-allocate-memory

-- Snippets of ByteArray# manipulation code from GHC's
-- testsuite/tests/lib/integer/integerGmpInternals.hs

buf2i :: Ptr Word8 -> IO Integer
buf2i (GHC.Exts.Ptr a) = do
  GMPI.importIntegerFromAddr a 512## 0#

i2buf :: Integer -> Ptr Word8 -> IO ()
i2buf i (GHC.Exts.Ptr a) = do
  _ <- BSI.memset (GHC.Exts.Ptr a) 0 512
  _ <- GMPI.exportIntegerToAddr i a 0#
  return ()

read_disk :: Fd -> Coq_word -> IO Coq_word
read_disk fd (W a) = do
  debugmsg $ "read(" ++ (show a) ++ ")"
  allocaBytes 512 $ \buf -> do
    _ <- fdSeek fd AbsoluteSeek $ fromIntegral $ 512*a
    cc <- fdReadBuf fd buf 512
    if cc == 512 then
      do
        i <- buf2i buf
        return $ W i
    else
      do
        error "read_disk: short read"

write_disk :: Fd -> Coq_word -> Coq_word -> IO ()
write_disk fd (W a) (W v) = do
  -- maybeCrash
  debugmsg $ "write(" ++ (show a) ++ ")"
  allocaBytes 512 $ \buf -> do
    _ <- fdSeek fd AbsoluteSeek $ fromIntegral $ 512*a
    i2buf v buf
    cc <- fdWriteBuf fd buf 512
    if cc == 512 then
      return ()
    else
      do
        error "write_disk: short write"

sync_disk :: Fd -> IO ()
sync_disk fd = do
  debugmsg $ "sync()"
  -- fileSynchroniseDataOnly fd
  return ()
