module Main where

import qualified Data.ByteString as BS
import qualified System.Directory
import Foreign.C.Error
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
import System.IO
import System.Fuse
import Word
import Disk
import Interpreter as I
import qualified FS
import qualified MemLog
import qualified Balloc
import qualified Inode

-- Handle type for open files; we will use the inode number
type HT = Coq_word

disk_fn :: String
disk_fn = "disk.img"

lxp :: MemLog.Coq_xparams
lxp = MemLog.Build_xparams
  (W 0x2000)  -- log header sector
  (W 0x2001)  -- commit flag sector
  (W 0x2010)  -- log start sector
  (W 0x1000)  -- log length, and MemLog uses one more for a block of addrs

bxp :: Balloc.Coq_xparams
bxp = Balloc.Build_xparams
  (W 0x1100)  -- bitmap start sector
  (W 0x1)     -- bitmap length

ixp :: Inode.Coq_xparams
ixp = Inode.Build_xparams
  (W 0x1000)   -- inode start sector
  (W 0x100)    -- number of inode sectors

main :: IO ()
main = do
  fileExists <- System.Directory.doesFileExist disk_fn
  f <- openFile disk_fn ReadWriteMode
  if fileExists
  then
    do
      putStrLn "Recovering disk.."
      I.run f $ MemLog._MEMLOG__recover lxp
  else
    do
      putStrLn "Initializing disk.."
      I.run f $ MemLog._MEMLOG__init lxp
  putStrLn "Starting file system.."
  fuseMain (fscqFSOps f) defaultExceptionHandler
  hClose f

fscqFSOps :: Handle -> FuseOperations HT
fscqFSOps f = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat f
  , fuseOpen = fscqOpen
  , fuseRead = fscqRead f
  , fuseWrite = fscqWrite f
  , fuseSetFileSize = fscqSetFileSize f
  , fuseOpenDirectory = fscqOpenDirectory
  , fuseReadDirectory = fscqReadDirectory f
  , fuseGetFileSystemStats = fscqGetFileSystemStats
  }

fscqPath :: FilePath
fscqPath = "/hello"

dirStat :: FuseContext -> FileStat
dirStat ctx = FileStat
  { statEntryType = Directory
  , statFileMode = foldr1 unionFileModes
                     [ ownerReadMode, ownerExecuteMode
                     , groupReadMode, groupExecuteMode
                     , otherReadMode, otherExecuteMode
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

fileStat :: FuseContext -> FileOffset -> FileStat
fileStat ctx len = FileStat
  { statEntryType = RegularFile
  , statFileMode = foldr1 unionFileModes
                     [ ownerReadMode, ownerWriteMode
                     , groupReadMode, groupWriteMode
                     , otherReadMode, otherWriteMode
                     ]
  , statLinkCount = 1
  , statFileOwner = fuseCtxUserID ctx
  , statFileGroup = fuseCtxGroupID ctx
  , statSpecialDeviceID = 0
  , statFileSize = len
  , statBlocks = 1
  , statAccessTime = 0
  , statModificationTime = 0
  , statStatusChangeTime = 0
  }

fscqGetFileStat :: Handle -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat _ "/" = do
  ctx <- getFuseContext
  return $ Right $ dirStat ctx
fscqGetFileStat f path | path == fscqPath = do
  ctx <- getFuseContext
  (W len) <- I.run f $ FS.file_len lxp ixp (W 0)
  return $ Right $ fileStat ctx $ fromIntegral len
fscqGetFileStat _ _ =
  return $ Left eNOENT

fscqOpenDirectory :: FilePath -> IO Errno
fscqOpenDirectory "/" = return eOK
fscqOpenDirectory _   = return eNOENT

fscqReadDirectory :: Handle -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory f "/" = do
  ctx <- getFuseContext
  (W len) <- I.run f $ FS.file_len lxp ixp (W 0)
  return $ Right [(".",          dirStat ctx)
                 ,("..",         dirStat ctx)
                 ,(fscqName,    fileStat ctx $ fromIntegral len)
                 ]
  where (_:fscqName) = fscqPath
fscqReadDirectory _ _ = return (Left (eNOENT))

fscqOpen :: FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen path mode _
  | path == fscqPath = return $ Right $ W 0
  | otherwise        = return (Left eNOENT)

fscqRead :: Handle -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead f _ inum byteCount offset = do
  -- Ignore the count and offset for now..
  (W w) <- I.run f $ FS.read_block lxp ixp inum (W 0)
  bs <- i2bs w
  return $ Right $ BS.take (fromIntegral byteCount) $ BS.drop (fromIntegral offset) bs

fscqWrite :: Handle -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite f _ inum bs offset = do
  -- Ignore the offset for now..
  w <- bs2i bs_pad
  ok <- I.run f $ FS.write_block lxp bxp ixp inum (W 0) (W w)
  if ok then
    return $ Right $ fromIntegral bs_len
  else
    return $ Left eIO
  where
    bs_pad = BS.append bs (BS.replicate (512 - bs_len) 0)
    bs_len = BS.length bs

fscqSetFileSize :: Handle -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize f path size =
  return eOK

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
