{-# LANGUAGE RankNTypes, MagicHash #-}

module Main where

import Fuse
import CfscqFs
import Options

data CfscqOptions = CfscqOptions
  { 
    -- This controls whether HFuse will use upcalls (FUSE threads entering GHC runtime)
    -- or downcalls (separate FUSE threads using a queue, and GHC accessing this queue
    -- using its own threads).
    optUseDowncalls :: Bool }

instance Options CfscqOptions where
  defineOptions = pure CfscqOptions
    <*> simpleOption "use-downcalls" True
         "use downcalls (opqueue) rather than C->HS upcalls"

main :: IO ()
main = runCommand $ \opts args -> case args of
  disk_fn:fuse_args -> do
    fs <- initCfscq disk_fn getFuseContext
    fuseRun "fscq" fuse_args fs defaultExceptionHandler (optUseDowncalls opts)
  _ -> putStrLn $ "Usage: cfscq disk -f /tmp/ft"
