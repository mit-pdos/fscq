module NativeFs where

import           Data.Word (Word8)
import           Foreign.ForeignPtr
import           Foreign.Ptr (Ptr)
import           System.Posix
import           UnixIO

import           Fuse
import           System.FilePath.Posix (joinPath)

import qualified Data.ByteString.Char8 as B
import qualified Data.ByteString.Internal as B
--import qualified Data.ByteString.Unsafe   as B

join :: FilePath -> FilePath -> FilePath
join p1 p2 = joinPath [p1, p2]

-- TODO: catch exceptions and return them as errors
toEither :: IO a -> IO (Either Errno a)
toEither act = Right <$> act

toErrno :: IO () -> IO Errno
toErrno act = do
  r <- toEither act
  return $ case r of
             Left e -> e
             Right _ -> eOK

nativeOpen :: FilePath -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno Fd)
nativeOpen root p mode flags = toEither $
  openFd (root `join` p) mode Nothing flags

nativeRead :: FilePath -> FilePath -> Fd -> ByteCount -> FileOffset ->
              IO (Either Errno B.ByteString)
nativeRead _root _p fd count off = toEither $
  B.createAndTrim (fromIntegral count) $ \ptr ->
    fromIntegral <$> pread fd ptr (fromIntegral count) off

withByteString :: B.ByteString -> (Ptr Word8 -> Int -> IO a) -> IO a
withByteString s act = do
  let (fptr, off, len) = B.toForeignPtr s
  withForeignPtr (plusForeignPtr fptr off) $ \ptr ->
    act ptr len

nativeWrite :: FilePath -> FilePath -> Fd -> B.ByteString -> FileOffset
          -> IO (Either Errno ByteCount)
nativeWrite _root _p fd dat off = toEither $
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
  st <- openDirStream (root `join` p)
  paths <- loop st
  closeDirStream st
  mapM getStat paths
  where loop st = do
          p <- readDirStream st
          if p == ""
            then return []
            else (p:) <$> loop st
        getStat p = do
          s <- getFileStatus p
          return (p, fileStatusToFileStat s)

nativeGetFileStat :: FilePath -> FilePath -> IO (Either Errno FileStat)
nativeGetFileStat root p = toEither $
  fileStatusToFileStat <$> getFileStatus (root `join` p)

nativeCreateFile :: FilePath -> FilePath -> FileMode -> OpenMode -> OpenFileFlags -> IO (Either Errno Fd)
nativeCreateFile root p perm mode flags = toEither $ do
  openFd (root `join` p) mode (Just perm) flags

nativeCreateDirectory :: FilePath -> FilePath -> FileMode -> IO Errno
nativeCreateDirectory root p mode = toErrno $ do
  createDirectory (root `join` p) mode

nativeFuseOps :: FilePath -> FuseOperations Fd
nativeFuseOps d = defaultFuseOps
  { fuseOpen=nativeOpen d
  , fuseRead=nativeRead d
  , fuseWrite=nativeWrite d
  , fuseReadDirectory=nativeReadDirectory d
  , fuseGetFileStat=nativeGetFileStat d
  , fuseCreateFile=nativeCreateFile d
  , fuseCreateDirectory=nativeCreateDirectory d }
