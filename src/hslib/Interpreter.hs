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

run :: Handle -> Prog.Coq_prog a -> IO a
run _ (Done r) = return r
run f (Read a rx) = do val <- Disk.read_disk f a; run f $ rx val
run f (Write a v rx) = do Disk.write_disk f a v; run f $ rx ()
