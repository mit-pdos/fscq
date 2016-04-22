module Main where

import Word
import qualified Interpreter as I
import qualified AsyncFS
import FSLayout
import Disk
import System.Environment

main :: IO ()
main = do
  args <- getArgs

  case args of
    [fn] -> do
      ds <- init_disk fn
      putStrLn $ "Initializing file system"
      res <- I.run ds $ AsyncFS.mkfs (W 1) (W 1)
      case res of
        Err _ -> error $ "mkfs failed"
        OK (_, (fsxp, ())) ->
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
