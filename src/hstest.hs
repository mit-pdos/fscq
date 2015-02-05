module Main where

import System.IO
import MemLog
import Balloc
import Inode
import Prog
import Word
import qualified Disk
import qualified System.Directory
-- import qualified System.Exit
-- import qualified System.Random
import qualified Testprog

disk_fn :: String
disk_fn = "disk.img"

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

run_dcode :: Handle -> Prog.Coq_prog a -> IO a
run_dcode _ (Done r) = return r
run_dcode f (Read a rx) = do val <- Disk.read_disk f a; run_dcode f $ rx val
run_dcode f (Write a v rx) = do Disk.write_disk f a v; run_dcode f $ rx ()

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
  r <- repf 10000 (Just (W 123))
       (\x -> case x of
              Nothing -> return Nothing
              Just xv -> run_dcode f $ Testprog.test_bfile lxp bxp ixp xv Prog.Done)
  hClose f
  putStrLn $ "Done: " ++ (show r)

