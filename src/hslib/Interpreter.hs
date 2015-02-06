module Interpreter where

import System.IO
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

run_dcode :: Handle -> Prog.Coq_prog a -> IO a
run_dcode _ (Done r) = return r
run_dcode f (Read a rx) = do val <- Disk.read_disk f a; run_dcode f $ rx val
run_dcode f (Write a v rx) = do Disk.write_disk f a v; run_dcode f $ rx ()

run :: Handle -> ((a -> Prog.Coq_prog a) -> Prog.Coq_prog a) -> IO a
run h p = run_dcode h $ p (\x -> Prog.Done x)
