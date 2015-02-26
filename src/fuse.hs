{-# LANGUAGE RankNTypes #-}

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
import Cache
import Prog
import Data.IORef
import Interpreter as I
import qualified FS
import qualified MemLog
import FSLayout

-- Handle type for open files; we will use the inode number
type HT = Coq_word

disk_fn :: String
disk_fn = "disk.img"

-- Special inode numbers
rootDir :: Coq_word
rootDir = W 4090
-- we stick the root directory towards the end because we don't currently
-- have a way of marking it as in-use by the allocator, so we just hope the
-- allocator never picks this number for now..

-- File system configuration
nCache :: Coq_word
nCache = W 1000
nDataBitmaps :: Coq_word
nDataBitmaps = W 1
nInodeBitmaps :: Coq_word
nInodeBitmaps = W 1

fsxp :: Coq_fs_xparams
fsxp = FS.compute_xparams nCache nDataBitmaps nInodeBitmaps

type MSCS = (MemLog.Coq_memstate, Cache.Coq_cachestate)
type FSprog a = (MSCS -> ((MSCS, a) -> Prog.Coq_prog (MSCS, a)) -> Prog.Coq_prog (MSCS, a))
type FSrunner = forall a. FSprog a -> IO a
doFScall :: Fd -> IORef MSCS -> FSrunner
doFScall fd ref f = do
  s <- readIORef ref
  (s', r) <- I.run fd $ f s
  writeIORef ref s'
  return r

main :: IO ()
main = do
  fileExists <- System.Directory.doesFileExist disk_fn
  fd <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  s <- if fileExists
  then
    do
      putStrLn $ "Recovering file system, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
      I.run fd $ MemLog._MEMLOG__recover (coq_FSXPMemLog fsxp)
  else
    do
      putStrLn $ "Initializing file system, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
      I.run fd $ MemLog._MEMLOG__init (coq_FSXPMemLog fsxp)
  putStrLn "Starting file system.."
  ref <- newIORef s
  fuseMain (fscqFSOps (doFScall fd ref)) defaultExceptionHandler
  closeFd fd

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: FSrunner -> FuseOperations HT
fscqFSOps fr = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fr
  , fuseOpen = fscqOpen fr
  , fuseCreateDevice = fscqCreate fr
  , fuseRemoveLink = fscqUnlink fr
  , fuseRead = fscqRead fr
  , fuseWrite = fscqWrite fr
  , fuseSetFileSize = fscqSetFileSize fr
  , fuseOpenDirectory = fscqOpenDirectory
  , fuseReadDirectory = fscqReadDirectory fr
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

fscqGetFileStat :: FSrunner -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat _ "/" = do
  ctx <- getFuseContext
  return $ Right $ dirStat ctx
fscqGetFileStat fr (_:path) = do
  r <- fr $ FS.lookup fsxp rootDir path
  case r of
    Nothing -> return $ Left eNOENT
    Just inum -> do
      len <- fr $ FS.file_len fsxp inum
      ctx <- getFuseContext
      return $ Right $ fileStat ctx $ fromIntegral $ wordToNat 64 len
fscqGetFileStat _ _ = return $ Left eNOENT

fscqOpenDirectory :: FilePath -> IO Errno
fscqOpenDirectory "/" = return eOK
fscqOpenDirectory _   = return eNOENT

fscqReadDirectory :: FSrunner -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fr "/" = do
  ctx <- getFuseContext
  files <- fr $ FS.readdir fsxp rootDir
  len <- fr $ FS.file_len fsxp rootDir -- should actually stat the right file
  return $ Right $ [(".",          dirStat ctx)
                   ,("..",         dirStat ctx)
                   ] ++ map (\(fn, inum) -> (fn, fileStat ctx 0)) files
fscqReadDirectory _ _ = return (Left (eNOENT))

fscqOpen :: FSrunner -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fr (_:path) mode flags = do
  r <- fr $ FS.lookup fsxp rootDir path
  case r of
    Nothing -> return $ Left eNOENT
    Just inum -> return $ Right $ inum
fscqOpen _ _ _ _ = return $ Left eIO

fscqCreate :: FSrunner -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fr (_:path) RegularFile _ _ = do
  r <- fr $ FS.create fsxp rootDir path
  putStrLn $ "create: " ++ (show r)
  case r of
    Nothing -> return eNOSPC
    Just _ -> return eOK
fscqCreate _ _ _ _ _ = return eOPNOTSUPP

fscqUnlink :: FSrunner -> FilePath -> IO Errno
fscqUnlink fr (_:path) = do
  r <- fr $ FS.delete fsxp rootDir path
  case r of
    True -> return eOK
    False -> return eIO
fscqUnlink _ _ = return eOPNOTSUPP

-- Wrappers for converting Coq_word to/from ByteString, with
-- the help of i2buf and buf2i from hslib/Disk.
bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp _ _) = withForeignPtr fp buf2i

i2bs :: Integer -> IO BS.ByteString
i2bs i = BSI.create 512 $ i2buf i

fscqRead :: FSrunner -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead fr _ inum byteCount offset = do
  wlen <- fr $ FS.file_len fsxp inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  byteCount <- return $ max 0 (min (fromIntegral byteCount) (len - (fromIntegral offset)))
  (W w) <- fr $ FS.read_block fsxp inum (W64 $ fromIntegral $ offset `div` 512)
  bs <- i2bs w
  return $ Right $ BS.take (fromIntegral byteCount) $ BS.drop (fromIntegral $ offset `mod` 512) bs

fscqWrite :: FSrunner -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite fr _ inum bs offset = do
  -- Ignore the offset for now..
  w <- bs2i bs_pad
  ok <- fr $ FS.write_block fsxp inum (W 0) (W w)
  if ok then
    return $ Right $ fromIntegral bs_len
  else
    return $ Left eIO
  where
    bs_pad = BS.append bs (BS.replicate (512 - bs_len) 0)
    bs_len = BS.length bs

fscqSetFileSize :: FSrunner -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fr (_:path) size =
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
