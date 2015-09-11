module Main where

import Word
import qualified Interpreter as I
import qualified FS
import FSLayout
import Disk
import Errno
import System.Environment

do_mkfs :: String -> Integer -> Integer -> IO ()
do_mkfs fn data_bitmaps inode_bitmaps = do
  ds <- init_disk fn
  putStrLn $ "Initializing file system"
  res <- I.run ds $ FS.mkfs (W data_bitmaps) (W inode_bitmaps)
  case res of
    Err _ -> error $ "mkfs failed"
    OK (_, (fsxp, ())) ->
      putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
  stats <- close_disk ds
  print_stats stats

main :: IO ()
main = do
  args <- getArgs

  case args of
    [fn] -> do_mkfs fn 1 1
    [fn, data_bitmaps_s, inode_bitmaps_s] -> do_mkfs fn (read data_bitmaps_s) (read inode_bitmaps_s)
    _ -> do
      putStrLn $ "Usage:"
      putStrLn $ "  mkfs diskpath"
      putStrLn $ "  mkfs diskpath n_data_bitmaps n_inode_bitmaps"
