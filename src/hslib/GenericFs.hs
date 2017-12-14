module GenericFs where

import Fuse
import System.Posix.User
import System.Posix.Types
import Data.ByteString as BS

getFuseIds :: IO (UserID, GroupID)
getFuseIds = do
  ctx <- getFuseContext
  return (fuseCtxUserID ctx, fuseCtxGroupID ctx)

getProcessIds :: IO (UserID, GroupID)
getProcessIds = do
  (,) <$> getRealUserID <*> getRealGroupID

type Filesystem = FuseOperations Integer
