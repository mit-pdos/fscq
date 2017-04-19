module Main where

import qualified Interpreter as I
import qualified AsyncFS
import FSLayout
import Disk
import qualified Errno
import Options

data MkfsOptions = MkfsOptions
  { optCachesize ::  Integer
  , optDataBitmaps :: Integer
  , optInodeBitmaps :: Integer
  , optLogDescBlocks :: Integer }

instance Options MkfsOptions where
  defineOptions = pure MkfsOptions
    <*> simpleOption "cachesize" 100000
          "maximum cached blocks"
    <*> simpleOption "data-bitmaps" 1
          "number of bitmaps (each 32768 bits) for data blocks"
    <*> simpleOption "inode-bitmaps" 1
          "number of bitmaps (each 32768 bits) for inodes"
    <*> simpleOption "log-desc-blocks" 256
          "size of log in descriptor blocks"

main :: IO ()
main = runCommand $ \opts args -> do
  case args of
    [fn] -> do
      ds <- init_disk fn
      putStrLn $ "Initializing file system"
      res <- I.run ds $ AsyncFS._AFS__mkfs (optCachesize opts) (optDataBitmaps opts) (optInodeBitmaps opts) (optLogDescBlocks opts)
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (_, fsxp) ->
          putStrLn $ "Initialization OK, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"

      stats <- close_disk ds
      print_stats stats
    _ -> do
      putStrLn $ "Usage: mkfs [options] diskpath"
