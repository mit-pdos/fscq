module Interpreter where

import Prog
import Disk
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

run_dcode :: DiskState -> Prog.Coq_prog a -> IO a
run_dcode _ (Done r) = return r
run_dcode ds (Read a rx) = do val <- Disk.read_disk ds a; run_dcode ds $ rx val
run_dcode ds (Write a v rx) = do Disk.write_disk ds a v; run_dcode ds $ rx ()
run_dcode ds (Sync _ rx) = do Disk.sync_disk ds; run_dcode ds $ rx ()

run :: DiskState -> ((a -> Prog.Coq_prog a) -> Prog.Coq_prog a) -> IO a
run ds p = run_dcode ds $ p (\x -> Prog.Done x)
