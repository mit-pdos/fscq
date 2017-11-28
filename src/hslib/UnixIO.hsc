module UnixIO(writev, pwrite, pread) where

#define _XOPEN_SOURCE 500
#include <unistd.h>
#include <sys/uio.h>

import Foreign
import Foreign.C
import Control.Monad
import System.Posix.Types

foreign import ccall safe "writev" cwritev :: Fd -> Ptr () -> CInt -> IO ByteCount

writev :: Fd -> [(Ptr a, Int)] -> IO ByteCount
writev fd lst = do
  let len = length lst
  allocaBytes ((#size struct iovec) * len) $ \iovs -> do
  let w i (p,pl) = do let iov = plusPtr iovs ((#size struct iovec) * i)
                      (#poke struct iovec, iov_base) iov p
                      (#poke struct iovec, iov_len)  iov pl
  zipWithM_ w [0..] lst
  throwErrnoIfMinus1Retry "writev" $ cwritev fd iovs $ fromIntegral len

foreign import ccall safe "pwrite" cpwrite :: Fd -> Ptr a -> CSize -> COff -> IO ByteCount
foreign import ccall safe "pread" cpread  :: Fd -> Ptr a -> CSize -> COff -> IO ByteCount

pwrite :: Fd -> Ptr a -> Int -> COff -> IO ByteCount
pwrite fd ptr len off = throwErrnoIfMinus1Retry "pwrite" $ cpwrite fd ptr (fromIntegral len) off

pread :: Fd -> Ptr a -> Int -> COff -> IO ByteCount
pread fd ptr len off = throwErrnoIfMinus1Retry "pread" $ cpread fd ptr (fromIntegral len) off
