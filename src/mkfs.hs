module Main where

import Word
import qualified Interpreter as I
import qualified FS
import FSLayout
import Disk
import System.Environment

cachesize :: Int
cachesize = 1000

main :: IO ()
main = do
  args <- getArgs

  case args of
    [fn] -> do
      ds <- init_disk fn
      putStrLn $ "Initializing file system"
      (_, (fsxp, (ok, ()))) <- I.run ds $ FS.mkfs (W 1) (W 1) cachesize
      if ok == False then
        error $ "mkfs failed"
      else
        putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
