module Interpreter where

import PermProg
import qualified Disk
import Word
import Data.Word
-- import qualified Crypto.Hash.SHA256 as SHA256
import qualified Data.Digest.CRC32 as CRC32
-- import System.CPUTime.Rdtsc
import PermAsyncDisk

-- import qualified System.Exit
-- import qualified System.Random

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

verbose :: Bool
verbose = False

output :: Bool
output = False

timing :: Bool
timing = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

crc32_word_update :: Word32 -> Integer -> Coq_word -> IO Word32
crc32_word_update c sz (W w) = do
  bs <- Word.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  crc32_word_update c sz (WBS bs)
crc32_word_update c sz (W64 w) = crc32_word_update c sz $ W $ fromIntegral w
crc32_word_update c _ (WBS bs) = return $ CRC32.crc32Update c bs

run_dcode :: Disk.DiskState -> PermProg.Coq_prog a -> IO a
run_dcode _ (Ret r) = do
  debugmsg $ "Done"
  return r
run_dcode ds (Read a) = do
  debugmsg $ "Read " ++ (show a)
  val <- Disk.read_disk ds a
  return $ unsafeCoerce val
run_dcode ds (Write a v) = do
  debugmsg $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  return $ unsafeCoerce ()
run_dcode ds Sync = do
  debugmsg $ "Sync"
  Disk.sync_disk ds
  return $ unsafeCoerce ()
-- run_dcode ds (Trim a) = do
--   debugmsg $ "Trim " ++ (show a)
--   Disk.trim_disk ds a
--   return $ unsafeCoerce ()
-- run_dcode ds (VarAlloc v) = do
--   debugmsg $ "VarAlloc"
--   i <- Disk.var_alloc ds v
--   return $ unsafeCoerce i
-- run_dcode ds (VarGet i) = do
--   debugmsg $ "VarGet " ++ (show i)
--   val <- Disk.var_get ds i
--   return $ unsafeCoerce val
-- run_dcode ds (VarSet i v) = do
--   debugmsg $ "VarSet " ++ (show i)
--   Disk.var_set ds i v
--   return $ unsafeCoerce ()
-- run_dcode ds (VarDelete i) = do
--   debugmsg $ "VarDelete " ++ (show i)
--   Disk.var_delete ds i
--   return $ unsafeCoerce ()
-- run_dcode _ AlertModified = do
--   debugmsg $ "AlertModified"
--   return $ unsafeCoerce ()
-- run_dcode _ (Debug s n) = do
--   if output then do
--     putStrLn $ s ++ " " ++ (show n)
--     return $ unsafeCoerce ()
--   else
--     return $ unsafeCoerce ()
-- run_dcode _ (Rdtsc) = do
--   if timing then do
--     r <- rdtsc
--     return $ unsafeCoerce r
--   else
--     return $ unsafeCoerce ()
run_dcode _ (Hash sz w) = do
  debugmsg $ "Hash " ++ (show sz)
  c <- crc32_word_update 0 sz w
  return $ unsafeCoerce $ W $ fromIntegral c
run_dcode _ (Hash2 sz1 sz2 w1 w2) = do
  debugmsg $ "Hash2 " ++ (show sz1) ++ " " ++ (show sz2)
  c1 <- crc32_word_update 0 sz1 w1
  c2 <- crc32_word_update c1 sz2 w2
  return $ unsafeCoerce $ W $ fromIntegral c2
run_dcode ds (Bind p1 p2) = do
  debugmsg $ "Bind"
  r1 <- run_dcode ds p1
  r2 <- run_dcode ds (p2 r1)
  return r2
run_dcode _ (Seal _ b) = do
  return $ unsafeCoerce b
run_dcode _ (Unseal h) = do
  return $ unsafeCoerce h
run_dcode _ (Auth t) = do
  case t of
    Public ->
      return $ unsafeCoerce True
    Private uid ->
      if uid == 123 then
        return $ unsafeCoerce True
      else
        return $ unsafeCoerce False

run :: Disk.DiskState -> PermProg.Coq_prog a -> IO a
run ds p = run_dcode ds p
