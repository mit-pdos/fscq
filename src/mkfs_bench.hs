module Main where

import qualified Interpreter as I
import qualified AsyncFS
import FSLayout
import Disk
import System.Environment
import Control.Monad
import qualified Errno
import System.CPUTime.Rdtsc

itercount = 10000

cachesize :: Integer
cachesize = 100000

main :: IO ()
main = do
  args <- getArgs

  case args of
    [fn] -> do
      ds <- init_disk fn
      putStrLn $ "Initializing file system"
      res <- I.run ds $ AsyncFS._AFS__mkfs cachesize 1 1 256
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (ms, fsxp) -> do
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
          r1 <- rdtsc
          _ <- foldM (\ms _ -> do
            (ms, res) <- I.run ds $ AsyncFS._AFS__file_get_sz fsxp 2 ms
            return ms
            ) ms (replicate itercount ())
          r2 <- rdtsc
          putStrLn $ "file_get_sz: " ++ (show (fromIntegral (r2 - r1) / fromIntegral itercount)) ++ " cycles"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
