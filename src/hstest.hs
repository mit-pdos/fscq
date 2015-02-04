{-# LANGUAGE MagicHash, UnboxedTuples #-}

module Main where

import System.IO
import MemLog
import Balloc
import Inode
import Prog
import Word
import qualified System.Directory
-- import qualified System.Exit
-- import qualified System.Random
import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BSI
import qualified Data.Bits
import qualified Testprog
import qualified GHC.Integer.GMP.Internals as GMPI
import GHC.Word
import GHC.Base
import GHC.Exts
import Foreign.ForeignPtr

disk_fn :: String
disk_fn = "disk.img"

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

-- crashRandom :: IO Int
-- crashRandom = System.Random.getStdRandom (System.Random.randomR (1, 20))

-- maybeCrash :: IO ()
-- maybeCrash = do
--   x <- crashRandom
--   -- if x == 1
--   if x == 0
--   then
--     do
--       putStrLn "CRASH!"
--       System.Exit.exitFailure
--   else
--     return ()

-- For a more efficient array implementation, perhaps worth checking out:
-- http://www.macs.hw.ac.uk/~hwloidl/hackspace/ghc-6.12-eden-gumsmp-MSA-IFL13/libraries/dph/dph-base/Data/Array/Parallel/Arr/BUArr.hs

-- Snippets of ByteArray# manipulation code from GHC's
-- testsuite/tests/lib/integer/integerGmpInternals.hs

data MBA = MBA { unMBA :: !(MutableByteArray# RealWorld) }
data BA  = BA  { unBA  :: !ByteArray# }

newByteArray :: Word# -> IO MBA
newByteArray sz = IO $ \s -> case newPinnedByteArray# (word2Int# sz) s of (# s', arr #) -> (# s', MBA arr #)

writeByteArray :: MutableByteArray# RealWorld -> Int# -> Word8 -> IO ()
writeByteArray arr i (W8# w) = IO $ \s -> case writeWord8Array# arr i w s of s' -> (# s', () #)

freezeByteArray :: MutableByteArray# RealWorld -> IO BA
freezeByteArray arr = IO $ \s -> case unsafeFreezeByteArray# arr s of (# s', arr' #) -> (# s', BA arr' #)

bs2ba :: BS.ByteString -> IO BA
bs2ba (BSI.PS fp _ _) = do
  MBA mba <- newByteArray 512##
  _ <- withForeignPtr fp $ \p -> case p of
    (GHC.Exts.Ptr a) -> IO $ \s -> case copyAddrToByteArray# a mba 0# 512# s of
      s' -> (# s', () #)
  freezeByteArray mba

ba2i :: BA -> Integer
ba2i (BA ba) = GMPI.importIntegerFromByteArray ba 0## 512## 1#

bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp _ _) = do
  withForeignPtr fp $ \p -> case p of
    (GHC.Exts.Ptr a) -> IO $ \s -> case GMPI.importIntegerFromAddr a 512## 1# s of
      (# s', i #) -> (# s', i #)

i2bs :: Integer -> BS.ByteString
i2bs i = BS.append (BS.replicate (512 - BS.length bs) 0) (BS.reverse bs)
  where
    bs = BS.unfoldr shifter i
    shifter = \x -> if x == 0
                    then Nothing
                    else Just (fromIntegral x, x `Data.Bits.shiftR` 8)

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
  hSeek f AbsoluteSeek $ 512*a
  BS.hPut f $ i2bs v
  return ()

run_dcode :: Handle -> Prog.Coq_prog a -> IO a
run_dcode _ (Done r) = return r
run_dcode f (Read a rx) = do val <- read_disk f a; run_dcode f $ rx val
run_dcode f (Write a v rx) = do write_disk f a v; run_dcode f $ rx ()

-- the_prog :: Log.Coq_xparams -> Prog.Coq_prog ()
-- the_prog xp =
--   _LOG__init xp $ \_ ->
--   _LOG__begin xp $ \_ ->
--   _LOG__read xp (W64 5) $ \v ->
--   _LOG__write xp (W64 6) v $ \_ ->
--   _LOG__commit xp $ \_ ->
--   Prog.Done ()

lxp :: MemLog.Coq_xparams
lxp = MemLog.Build_xparams
  (W 0x2000)  -- log header sector
  (W 0x2001)  -- commit flag sector
  (W 0x2010)  -- log start sector
  (W 0x1000)  -- log length, and MemLog uses one more for a block of addrs

bxp :: Balloc.Coq_xparams
bxp = Balloc.Build_xparams
  (W 0x1100)  -- bitmap start sector
  (W 0x1)     -- bitmap length

ixp :: Inode.Coq_xparams
ixp = Inode.Build_xparams
  (W 0x1000)   -- inode start sector
  (W 0x100)    -- number of inode sectors

repf :: Integer -> t -> (t -> IO t) -> IO t
repf 0 x _ = return x
repf n x f = do
  y <- f x
  z <- repf (n-1) y f
  return z

main :: IO ()
main = do
  -- This is racy (stat'ing the file first and opening it later)
  fileExists <- System.Directory.doesFileExist disk_fn
  f <- openFile disk_fn ReadWriteMode
  if fileExists
  then
    do
      putStrLn "Recovering disk.."
      run_dcode f $ _MEMLOG__recover lxp $ \_ -> Prog.Done ()
  else
    do
      putStrLn "Initializing disk.."
      run_dcode f $ _MEMLOG__init lxp $ \_ -> Prog.Done ()
  putStrLn "Running program.."
  -- r <- run_dcode f $ the_prog lxp
  -- r <- run_dcode f $ Testprog.testcopy lxp $ Prog.Done ()
  -- r <- run_dcode f $ Testprog.testalloc lxp bxp $ \x -> Prog.Done x
  r <- repf 1000 (Just (W 123))
       (\x -> case x of
              Nothing -> return Nothing
              Just xv -> run_dcode f $ Testprog.test_bfile lxp bxp ixp xv Prog.Done)
  hClose f
  putStrLn $ "Done: " ++ (show r)

