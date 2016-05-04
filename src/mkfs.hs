module Main where

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
      res <- I.run ds $ AsyncFS._AFS__mkfs 1 1 256
      case res of
        Nothing -> error $ "mkfs failed"
        Just (_, fsxp) ->
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs diskpath"
