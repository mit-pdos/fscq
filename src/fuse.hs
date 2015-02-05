module Main where

import qualified Data.ByteString as B
import qualified Data.ByteString.Char8
import Foreign.C.Error
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
import Word

import System.Fuse

-- Handle type for open files; we will use the inode number
type HT = Coq_word

main :: IO ()
main = fuseMain fscqFSOps defaultExceptionHandler

fscqFSOps :: FuseOperations HT
fscqFSOps = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat
  , fuseOpen = fscqOpen
  , fuseRead = fscqRead
  , fuseOpenDirectory = fscqOpenDirectory
  , fuseReadDirectory = fscqReadDirectory
  , fuseGetFileSystemStats = fscqGetFileSystemStats
  }

fscqString :: B.ByteString
fscqString = Data.ByteString.Char8.pack "Hello World, HFuse!\n"

fscqPath :: FilePath
fscqPath = "/hello"

dirStat :: FuseContext -> FileStat
dirStat ctx = FileStat
  { statEntryType = Directory
  , statFileMode = foldr1 unionFileModes
                     [ ownerReadMode
                     , ownerExecuteMode
                     , groupReadMode
                     , groupExecuteMode
                     , otherReadMode
                     , otherExecuteMode
                     ]
  , statLinkCount = 2
  , statFileOwner = fuseCtxUserID ctx
  , statFileGroup = fuseCtxGroupID ctx
  , statSpecialDeviceID = 0
  , statFileSize = 4096
  , statBlocks = 1
  , statAccessTime = 0
  , statModificationTime = 0
  , statStatusChangeTime = 0
  }

fileStat :: FuseContext -> FileStat
fileStat ctx = FileStat
  { statEntryType = RegularFile
  , statFileMode = foldr1 unionFileModes
                     [ ownerReadMode
                     , groupReadMode
                     , otherReadMode
                     ]
  , statLinkCount = 1
  , statFileOwner = fuseCtxUserID ctx
  , statFileGroup = fuseCtxGroupID ctx
  , statSpecialDeviceID = 0
  , statFileSize = fromIntegral $ B.length fscqString
  , statBlocks = 1
  , statAccessTime = 0
  , statModificationTime = 0
  , statStatusChangeTime = 0
  }

fscqGetFileStat :: FilePath -> IO (Either Errno FileStat)
fscqGetFileStat "/" = do
  ctx <- getFuseContext
  return $ Right $ dirStat ctx
fscqGetFileStat path | path == fscqPath = do
  ctx <- getFuseContext
  return $ Right $ fileStat ctx
fscqGetFileStat _ =
  return $ Left eNOENT

fscqOpenDirectory :: FilePath -> IO Errno
fscqOpenDirectory "/" = return eOK
fscqOpenDirectory _   = return eNOENT

fscqReadDirectory :: FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory "/" = do
  ctx <- getFuseContext
  return $ Right [(".",          dirStat  ctx)
                 ,("..",         dirStat  ctx)
                 ,(fscqName,    fileStat ctx)
                 ]
  where (_:fscqName) = fscqPath
fscqReadDirectory _ = return (Left (eNOENT))

fscqOpen :: FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen path mode _
  | path == fscqPath = case mode of
                         ReadOnly -> return (Right $ W 0)
                         _        -> return (Left eACCES)
  | otherwise        = return (Left eNOENT)

fscqRead :: FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno B.ByteString)
fscqRead path _ byteCount offset
  | path == fscqPath =
      return $ Right $ B.take (fromIntegral byteCount) $ B.drop (fromIntegral offset) fscqString
  | otherwise        = return $ Left eNOENT

fscqGetFileSystemStats :: String -> IO (Either Errno FileSystemStats)
fscqGetFileSystemStats _ =
  return $ Right $ FileSystemStats
    { fsStatBlockSize = 512
    , fsStatBlockCount = 1
    , fsStatBlocksFree = 1
    , fsStatBlocksAvailable = 1
    , fsStatFileCount = 5
    , fsStatFilesFree = 10
    , fsStatMaxNameLength = 255
    }
