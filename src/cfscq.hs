{-# LANGUAGE RankNTypes, MagicHash #-}

module Main where

import CfscqFs
import Fuse
import Options
import System.Posix.Types (UserID, GroupID)

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

getFuseIds :: IO (UserID, GroupID)
getFuseIds = do
  ctx <- getFuseContext
  return (fuseCtxUserID ctx, fuseCtxGroupID ctx)

main :: IO ()
main = runCommand $ \opts args -> case args of
  disk_fn:fuse_args -> do
    fs <- initCfscq disk_fn getFuseIds
    fuseRun "fscq" fuse_args fs defaultExceptionHandler (optUseDowncalls opts)
  _ -> putStrLn $ "Usage: cfscq disk -f /tmp/ft"
