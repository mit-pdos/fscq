{-# LANGUAGE RankNTypes, MagicHash #-}

module Main where

import FscqFs
import Fuse
import Options
import GenericFs

data FscqOptions = FscqOptions
  {
    -- This controls whether HFuse will use upcalls (FUSE threads entering GHC runtime)
    -- or downcalls (separate FUSE threads using a queue, and GHC accessing this queue
    -- using its own threads).
    optUseDowncalls :: Bool }

instance Options FscqOptions where
  defineOptions = pure FscqOptions
    <*> simpleOption "use-downcalls" True
         "use downcalls (opqueue) rather than C->HS upcalls"

main :: IO ()
main = runCommand $ \opts args -> case args of
  disk_fn:fuse_args -> do
    fs <- initFscq disk_fn False getFuseIds
    fuseRun "fscq" fuse_args (fuseOps fs) defaultExceptionHandler (optUseDowncalls opts)
  _ -> putStrLn $ "Usage: fscq disk -f /tmp/ft"
