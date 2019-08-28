module Main where

import qualified Interpreter as I
import qualified AsyncFS
import FSLayout
import Disk
import System.Environment
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
      res <- I.run ds $ AsyncFS._AFS__mkfs cachesize 4 1 256
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (_, fsxp) -> do
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
          putStrLn $ "  === disk layout addresses ==="
          putStrLn $ "  superblock: 0"
          putStrLn $ "  data blocks start: 1"
          putStrLn $ "  inode blocks start: " ++ (show . (+1) . coq_IXStart . coq_FSXPInode $ fsxp)
          putStrLn $ "  log header: " ++ (show . coq_LogHeader . coq_FSXPLog $ fsxp)
          putStrLn $ "  log data start: " ++ (show . coq_LogData . coq_FSXPLog $ fsxp)

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
