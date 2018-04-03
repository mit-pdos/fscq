module NativeFs
  ( createNativeFs
  , withExt4
  ) where

import           Control.Monad.Catch (bracket)
import           Data.IORef (newIORef)
import           Data.Word (Word8)
import           Foreign.ForeignPtr
import           Foreign.Ptr (Ptr)
import           System.IO (hPutStrLn, stderr)
import           System.IO.Error (catchIOError,
                                  isDoesNotExistError,
                                  isAlreadyExistsError)
import           System.Process

import           Fuse
import           System.FilePath.Posix (makeRelative, joinPath)
import           System.Posix
import           UnixIO

import           GenericFs (Filesystem(..))

import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Internal as B
--import qualified Data.ByteString.Unsafe   as B

verbose :: Bool
verbose = False

debug :: String -> FilePath -> FilePath -> IO ()
debug s root p = if verbose
  then hPutStrLn stderr (s ++ " " ++ root `join` p)
  else return ()

join :: FilePath -> FilePath -> FilePath
join p1 p2 = joinPath [p1, makeRelative "/" p2]

-- TODO: catch exceptions and return them as errors
toEither :: IO a -> IO (Either Errno a)
toEither act = catchIOError (Right <$> act) handle
  where handle e
          | isDoesNotExistError e = return $ Left eNOENT
          | isAlreadyExistsError e = return $ Left eALREADY
          | otherwise = ioError e

toErrno :: IO () -> IO Errno
toErrno act = do
  r <- toEither act
  return $ case r of
             Left e -> e
             Right _ -> eOK

nativeOpen :: FilePath -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno Fd)
nativeOpen root p mode flags = toEither $ do
  debug "open" root p
  openFd (root `join` p) mode Nothing flags

nativeOpenDir :: FilePath -> FilePath -> IO (Either Errno Fd)
nativeOpenDir root p = toEither $ do
  debug "open" root p
  openFd (root `join` p) ReadOnly Nothing defaultFileFlags

-- called exactly once per Fd (unlike flush)
nativeRelease :: FilePath -> FilePath -> Fd -> IO ()
nativeRelease _root _p fd = do
  debug "release (close)" _root _p
  closeFd fd

nativeRead :: FilePath -> FilePath -> Fd -> ByteCount -> FileOffset ->
              IO (Either Errno B.ByteString)
nativeRead _root _p fd count off = toEither $ do
  debug "read" _root _p
  B.createAndTrim (fromIntegral count) $ \ptr ->
    fromIntegral <$> pread fd ptr (fromIntegral count) off

withByteString :: B.ByteString -> (Ptr Word8 -> Int -> IO a) -> IO a
withByteString s act = do
  let (fptr, off, len) = B.toForeignPtr s
  withForeignPtr (plusForeignPtr fptr off) $ \ptr ->
    act ptr len

nativeWrite :: FilePath -> FilePath -> Fd -> B.ByteString -> FileOffset
          -> IO (Either Errno ByteCount)
nativeWrite _root _p fd dat off = toEither $ do
  debug "write" _root _p
  withByteString dat $ \ptr len ->
    pwrite fd ptr len off

entryTypeOfStatus :: FileStatus -> EntryType
entryTypeOfStatus s
  | isRegularFile s = RegularFile
  | isDirectory s = Directory
  | isBlockDevice s = BlockSpecial
  | isSymbolicLink s = SymbolicLink
  | otherwise = Unknown

fileStatusToFileStat :: FileStatus -> FileStat
fileStatusToFileStat s =
  FileStat { statEntryType=entryTypeOfStatus s
           , statFileMode=fileMode s
           , statLinkCount=linkCount s
           , statFileOwner=fileOwner s
           , statFileGroup=fileGroup s
           , statSpecialDeviceID=specialDeviceID s
           , statFileSize=fileSize s
           , statBlocks=0
           , statAccessTime=accessTime s
           , statModificationTime=modificationTime s
           , statStatusChangeTime=statusChangeTime s }

nativeReadDirectory :: FilePath -> FilePath -> Fd -> IO (Either Errno [(FilePath, FileStat)])
nativeReadDirectory root p _fd = toEither $ do
  debug "readdir" root p
  st <- openDirStream (root `join` p)
  paths <- loop st
  closeDirStream st
  mapM getStat paths
  where loop st = do
          ent <- readDirStream st
          if ent == ""
            then return []
            else (ent:) <$> loop st
        getStat ent = do
          s <- getFileStatus $ joinPath [root, makeRelative "/" p, ent]
          return (ent, fileStatusToFileStat s)

nativeGetFileStat :: FilePath -> FilePath -> IO (Either Errno FileStat)
nativeGetFileStat root p = toEither $ do
  debug "stat" root p
  fileStatusToFileStat <$> getFileStatus (root `join` p)

nativeCreateFile :: FilePath -> FilePath -> FileMode -> OpenMode -> OpenFileFlags -> IO (Either Errno Fd)
nativeCreateFile root p perm mode flags = toEither $ do
  debug "createFile" root p
  openFd (root `join` p) mode (Just perm) flags

nativeCreateDirectory :: FilePath -> FilePath -> FileMode -> IO Errno
nativeCreateDirectory root p mode = toErrno $ do
  debug "createDir" root p
  createDirectory (root `join` p) mode

nativeUnlink :: FilePath -> FilePath -> IO Errno
nativeUnlink root p = toErrno $ do
  debug "unlink" root p
  removeLink (root `join` p)

nativeRemoveDirectory :: FilePath -> FilePath -> IO Errno
nativeRemoveDirectory root p = toErrno $ do
  debug "removeDir" root p
  removeDirectory (root `join` p)

nativeSync :: FilePath -> FilePath -> Fd -> SyncType -> IO Errno
nativeSync _root _p fd syncType  = toErrno $ do
  debug "sync" _root _p
  case syncType of
    FullSync -> fileSynchronise fd
    DataSync -> fileSynchroniseDataOnly fd

nativeFuseOps :: FilePath -> FuseOperations Fd
nativeFuseOps d = defaultFuseOps
  { fuseOpen=nativeOpen d
  , fuseOpenDirectory=nativeOpenDir d
  , fuseRelease=nativeRelease d
  , fuseRead=nativeRead d
  , fuseWrite=nativeWrite d
  , fuseReadDirectory=nativeReadDirectory d
  , fuseGetFileStat=nativeGetFileStat d
  , fuseCreateFile=nativeCreateFile d
  , fuseCreateDirectory=nativeCreateDirectory d
  , fuseRemoveLink=nativeUnlink d
  , fuseRemoveDirectory=nativeRemoveDirectory d
  , fuseSynchronizeFile=nativeSync d
  , fuseSynchronizeDirectory=nativeSync d }

createNativeFs :: FilePath -> IO (Filesystem Fd)
createNativeFs d = Filesystem (nativeFuseOps d) <$> newIORef mempty

initExt4 :: IO (Filesystem Fd)
initExt4 = let mntPath = "/tmp/fscq" in do
  callProcess "sudo" $ ["dangerously", "mount-ext4.sh", mntPath]
  createNativeFs mntPath

closeExt4 :: IO ()
closeExt4 = do
  callProcess "sudo" $ ["dangerously", "umount", "/tmp/fscq"]
  return ()

withExt4 :: (Filesystem Fd -> IO a) -> IO a
withExt4 act = bracket initExt4 (\_ -> closeExt4) act
