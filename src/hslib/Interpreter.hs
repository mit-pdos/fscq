module Interpreter where

import System.Posix.Types
import Prog
import qualified Disk
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

run_dcode :: Fd -> Prog.Coq_prog a -> IO a
run_dcode _ (Done r) = return r
run_dcode fd (Read a rx) = do val <- Disk.read_disk fd a; run_dcode fd $ rx val
run_dcode fd (Write a v rx) = do Disk.write_disk fd a v; run_dcode fd $ rx ()
run_dcode fd (Sync _ rx) = do Disk.sync_disk fd; run_dcode fd $ rx ()

run :: Fd -> ((a -> Prog.Coq_prog a) -> Prog.Coq_prog a) -> IO a
run fd p = run_dcode fd $ p (\x -> Prog.Done x)
