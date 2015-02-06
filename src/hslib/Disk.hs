{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Disk where

import System.IO
import Word
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BSI
import qualified GHC.Integer.GMP.Internals as GMPI
import GHC.Base
import GHC.Exts
import Foreign.ForeignPtr

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

-- Snippets of ByteArray# manipulation code from GHC's
-- testsuite/tests/lib/integer/integerGmpInternals.hs

bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp _ _) = do
  withForeignPtr fp $ \p -> case p of
    (GHC.Exts.Ptr a) -> IO $ \s -> case GMPI.importIntegerFromAddr a 512## -1# s of
      (# s', i #) -> (# s', i #)

i2bs :: Integer -> IO BS.ByteString
i2bs i = BSI.create 512 f
  where
    f = \p -> do
      _ <- BSI.memset p 0 512
      case p of
        (GHC.Exts.Ptr a) -> IO $ \s -> case GMPI.exportIntegerToAddr i a -1# s of
          (# s', _ #) -> (# s', () #)

read_disk :: Handle -> Coq_word -> IO Coq_word
read_disk f (W a) = do
  debugmsg $ "read(" ++ (show a) ++ ")"
  hSeek f AbsoluteSeek $ 512*a
  bs <- BS.hGet f 512
  i <- bs2i bs
  return $ W i

write_disk :: Handle -> Coq_word -> Coq_word -> IO ()
write_disk f (W a) (W v) = do
  -- maybeCrash
  debugmsg $ "write(" ++ (show a) ++ ")"
  bs <- i2bs v
  hSeek f AbsoluteSeek $ 512*a
  BS.hPut f bs
  return ()
