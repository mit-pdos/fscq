module GenericFs where

import Data.IORef
import Fuse
import System.Posix.Types
import System.Posix.User
import Timings

getFuseIds :: IO (UserID, GroupID)
getFuseIds = do
  ctx <- getFuseContext
  return (fuseCtxUserID ctx, fuseCtxGroupID ctx)

getProcessIds :: IO (UserID, GroupID)
getProcessIds = do
  (,) <$> getRealUserID <*> getRealGroupID

data Filesystem =
  Filesystem { fuseOps :: FuseOperations Integer
             , timings :: IORef Timings }
