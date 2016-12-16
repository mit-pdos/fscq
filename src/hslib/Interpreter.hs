module Interpreter where

import Prog
import qualified Disk
import Word
import qualified Crypto.Hash.SHA256 as SHA256
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

data Options = Options
  { verboseInterpret :: Bool }

debugmsg :: Options -> String -> IO ()
debugmsg opts s =
  if verboseInterpret opts then
    putStrLn s
  else
    return ()

run_dcode :: Options -> Disk.DiskState -> Prog.Coq_prog a -> IO a
run_dcode opts _ (Ret r) = do
  debugmsg opts $ "Done"
  return r
run_dcode opts ds (Read a) = do
  debugmsg opts $ "Read " ++ (show a)
  val <- Disk.read_disk ds a
  return $ unsafeCoerce val
run_dcode opts ds (Write a v) = do
  debugmsg opts $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  return $ unsafeCoerce ()
run_dcode opts ds Sync = do
  debugmsg opts $ "Sync"
  Disk.sync_disk ds
  return $ unsafeCoerce ()
run_dcode opts ds (Trim a) = do
  debugmsg opts $ "Trim " ++ (show a)
  Disk.trim_disk ds a
  return $ unsafeCoerce ()
run_dcode opts ds (Hash sz (W64 w)) = run_dcode opts ds (Hash sz (W $ fromIntegral w))
run_dcode opts _ (Hash sz (W w)) = do
  debugmsg opts $ "Hash " ++ (show sz) ++ " " ++ (show w)
  wbs <- Disk.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  h <- return $ SHA256.hash wbs
  ih <- Disk.bs2i h
  return $ unsafeCoerce $ W ih
run_dcode opts ds (Bind p1 p2) = do
  debugmsg opts $ "Bind"
  r1 <- run_dcode opts ds p1
  r2 <- run_dcode opts ds (p2 r1)
  return r2

run :: Options -> Disk.DiskState -> Prog.Coq_prog a -> IO a
run = run_dcode
