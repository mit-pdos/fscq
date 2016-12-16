module Main where

import qualified Interpreter as I
import qualified AsyncFS
import FSLayout
import Disk
import System.Environment
import qualified Errno

cachesize :: Integer
cachesize = 100000

interpOptions :: I.Options
interpOptions = I.Options False

main :: IO ()
main = do
  args <- getArgs

  case args of
    [fn] -> do
      ds <- init_disk fn
      putStrLn $ "Initializing file system"
      res <- I.run interpOptions ds $ AsyncFS._AFS__mkfs cachesize 1 1 256
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (_, fsxp) ->
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
