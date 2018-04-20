module Main where

import qualified Interpreter as I
import qualified AsyncFS
import FSLayout
import Disk
import System.Environment
import System.Posix.User
import qualified Errno

cachesize :: Integer
cachesize = 100000

main :: IO ()
main = do
  args <- getArgs

  case args of
    [fn] -> do
      ds <- init_disk fn
      putStrLn $ "Initializing file system"
      uid <- getEffectiveUserID
      res <- I.run (fromEnum uid) ds $ AsyncFS._AFS__mkfs cachesize 4 1 256
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (_, fsxp) ->
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
