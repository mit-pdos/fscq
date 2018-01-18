module GenericFs where

import Data.IORef
import Data.List (dropWhileEnd)
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

getResult :: String -> Either Errno a -> IO a
getResult fname (Left e) = ioError (errnoToIOError "" e Nothing (Just fname))
getResult _ (Right a) = return a

isDot :: FilePath -> Bool
isDot p = p == "." || p == ".."

filterDots :: [(FilePath, a)] -> [(FilePath, a)]
filterDots = filter (not . isDot . fst)

isFile :: FileStat -> Bool
isFile s =
  case statEntryType s of
  RegularFile -> True
  _ -> False

isDirectory :: FileStat -> Bool
isDirectory s = case statEntryType s of
  Directory -> True
  _ -> False

onlyFiles :: [(FilePath, FileStat)] -> [FilePath]
onlyFiles = map fst . filter (isFile . snd)

onlyDirectories :: [(FilePath, FileStat)] -> [FilePath]
onlyDirectories = map fst . filter (isDirectory . snd)

pathJoin :: FilePath -> FilePath -> FilePath
pathJoin p1 p2 = dropWhileEnd (== '/') p1 ++ "/" ++ p2
