module Main where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Internal as BSI
import qualified System.Directory
import Foreign.C.Error
import Foreign.ForeignPtr
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
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

-- Special inode numbers
rootDir :: Coq_word
rootDir = W 1
theOneFile :: Coq_word
theOneFile = W 2

lxp :: MemLog.Coq_xparams
lxp = MemLog.Build_xparams
  (W 0x2000)  -- log header sector
  (W 0x2001)  -- commit flag sector
  (W 0x2002)  -- log descriptor sector
  (W 0x2010)  -- log start sector
  (W 0x40)    -- log length (at most addr_per_block)

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
  fd <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  if fileExists
  then
    do
      putStrLn "Recovering disk.."
      I.run fd $ MemLog._MEMLOG__recover lxp
  else
    do
      putStrLn "Initializing disk.."
      I.run fd $ MemLog._MEMLOG__init lxp
  putStrLn "Starting file system.."
  fuseMain (fscqFSOps fd) defaultExceptionHandler
  closeFd fd

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: Fd -> FuseOperations HT
fscqFSOps fd = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fd
  , fuseOpen = fscqOpen fd
  , fuseCreateDevice = fscqCreate fd
  , fuseRead = fscqRead fd
  , fuseWrite = fscqWrite fd
  , fuseSetFileSize = fscqSetFileSize fd
  , fuseOpenDirectory = fscqOpenDirectory
  , fuseReadDirectory = fscqReadDirectory fd
  , fuseGetFileSystemStats = fscqGetFileSystemStats
  }

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

fscqGetFileStat :: Fd -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat _ "/" = do
  ctx <- getFuseContext
  return $ Right $ dirStat ctx
fscqGetFileStat fd (_:path) = do
  r <- I.run fd $ FS.lookup lxp bxp ixp rootDir path
  case r of
    Nothing -> return $ Left eNOENT
    Just inum -> do
      (W len) <- I.run fd $ FS.file_len lxp ixp inum
      ctx <- getFuseContext
      return $ Right $ fileStat ctx $ fromIntegral len
fscqGetFileStat _ _ = return $ Left eNOENT

fscqOpenDirectory :: FilePath -> IO Errno
fscqOpenDirectory "/" = return eOK
fscqOpenDirectory _   = return eNOENT

fscqReadDirectory :: Fd -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fd "/" = do
  ctx <- getFuseContext
  files <- I.run fd $ FS.readdir lxp ixp rootDir
  (W len) <- I.run fd $ FS.file_len lxp ixp theOneFile
  return $ Right $ [(".",          dirStat ctx)
                   ,("..",         dirStat ctx)
                   ] ++ map (\(fn, inum) -> (fn, fileStat ctx $ fromIntegral len)) files
fscqReadDirectory _ _ = return (Left (eNOENT))

fscqOpen :: Fd -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fd (_:path) mode flags = do
  r <- I.run fd $ FS.lookup lxp bxp ixp rootDir path
  case r of
    Nothing -> return $ Left eNOENT
    Just inum -> return $ Right $ inum
fscqOpen _ _ _ _ = return $ Left eIO

fscqCreate :: Fd -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fd (_:path) RegularFile _ _ = do
  -- All created files point to the same file inode..
  r <- I.run fd $ FS.link lxp bxp ixp rootDir path theOneFile
  case r of
    True -> return eOK
    False -> return eIO
fscqCreate _ _ _ _ _ = return eOPNOTSUPP

-- Wrappers for converting Coq_word to/from ByteString, with
-- the help of i2buf and buf2i from hslib/Disk.
bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp _ _) = withForeignPtr fp buf2i

i2bs :: Integer -> IO BS.ByteString
i2bs i = BSI.create 512 $ i2buf i

fscqRead :: Fd -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead fd _ inum byteCount offset = do
  -- Ignore the count and offset for now..
  (W w) <- I.run fd $ FS.read_block lxp ixp inum (W 0)
  bs <- i2bs w
  return $ Right $ BS.take (fromIntegral byteCount) $ BS.drop (fromIntegral offset) bs

fscqWrite :: Fd -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite fd _ inum bs offset = do
  -- Ignore the offset for now..
  w <- bs2i bs_pad
  ok <- I.run fd $ FS.write_block lxp bxp ixp inum (W 0) (W w)
  if ok then
    return $ Right $ fromIntegral bs_len
  else
    return $ Left eIO
  where
    bs_pad = BS.append bs (BS.replicate (512 - bs_len) 0)
    bs_len = BS.length bs

fscqSetFileSize :: Fd -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fd (_:path) size =
  return eOK
fscqSetFileSize _ _ _ = return eIO

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
