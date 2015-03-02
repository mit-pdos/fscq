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
import Control.Monad

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
cachesize :: Coq_word
cachesize = W64 1000
nDataBitmaps :: Coq_word
nDataBitmaps = W64 1
nInodeBitmaps :: Coq_word
nInodeBitmaps = W64 1

type MSCS = (MemLog.Coq_memstate, Cache.Coq_cachestate)
type FSprog a = (MSCS -> ((MSCS, a) -> Prog.Coq_prog (MSCS, a)) -> Prog.Coq_prog (MSCS, a))
type FSrunner = forall a. FSprog a -> IO a
doFScall :: DiskState -> IORef MSCS -> FSrunner
doFScall ds ref f = do
  s <- readIORef ref
  (s', r) <- I.run ds $ f s
  writeIORef ref s'
  return r

main :: IO ()
main = do
  fileExists <- System.Directory.doesFileExist disk_fn
  ds <- init_disk disk_fn
  (s, fsxp) <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      I.run ds $ MemLog._MEMLOG__recover cachesize
  else
    do
      putStrLn $ "Initializing file system"
      (s, fsxp) <- I.run ds $ FS.mkfs nDataBitmaps nInodeBitmaps cachesize
      set_nblocks_disk ds $ wordToNat 64 $ coq_FSXPMaxBlock fsxp
      return (s, fsxp)
  putStrLn $ "Starting file system, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
  ref <- newIORef s
  fuseMain (fscqFSOps (doFScall ds ref) fsxp) defaultExceptionHandler
  stats <- close_disk ds
  print_stats stats

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: FSrunner -> Coq_fs_xparams -> FuseOperations HT
fscqFSOps fr fsxp = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fr fsxp
  , fuseOpen = fscqOpen fr fsxp
  , fuseCreateDevice = fscqCreate fr fsxp
  , fuseRemoveLink = fscqUnlink fr fsxp
  , fuseRead = fscqRead fr fsxp
  , fuseWrite = fscqWrite fr fsxp
  , fuseSetFileSize = fscqSetFileSize fr fsxp
  , fuseOpenDirectory = fscqOpenDirectory
  , fuseReadDirectory = fscqReadDirectory fr fsxp
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

fscqGetFileStat :: FSrunner -> Coq_fs_xparams -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat _ _ "/" = do
  ctx <- getFuseContext
  return $ Right $ dirStat ctx
fscqGetFileStat fr fsxp (_:path) = do
  r <- fr $ FS.lookup fsxp rootDir path
  case r of
    Nothing -> return $ Left eNOENT
    Just inum -> do
      len <- fr $ FS.file_get_sz fsxp inum
      ctx <- getFuseContext
      return $ Right $ fileStat ctx $ fromIntegral $ wordToNat 64 len
fscqGetFileStat _ _ _ = return $ Left eNOENT

fscqOpenDirectory :: FilePath -> IO Errno
fscqOpenDirectory "/" = return eOK
fscqOpenDirectory _   = return eNOENT

fscqReadDirectory :: FSrunner -> Coq_fs_xparams -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fr fsxp "/" = do
  ctx <- getFuseContext
  files <- fr $ FS.readdir fsxp rootDir
  files_stat <- mapM (\(fn, inum) -> do
    len <- fr $ FS.file_get_sz fsxp inum
    return $ (fn, fileStat ctx $ fromIntegral $ wordToNat 64 len)) files
  return $ Right $ [(".",          dirStat ctx)
                   ,("..",         dirStat ctx)
                   ] ++ files_stat
fscqReadDirectory _ _ _ = return (Left (eNOENT))

fscqOpen :: FSrunner -> Coq_fs_xparams -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fr fsxp (_:path) mode flags = do
  r <- fr $ FS.lookup fsxp rootDir path
  case r of
    Nothing -> return $ Left eNOENT
    Just inum -> return $ Right $ inum
fscqOpen _ _ _ _ _ = return $ Left eIO

fscqCreate :: FSrunner -> Coq_fs_xparams -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fr fsxp (_:path) RegularFile _ _ = do
  r <- fr $ FS.create fsxp rootDir path
  putStrLn $ "create: " ++ (show r)
  case r of
    Nothing -> return eNOSPC
    Just _ -> return eOK
fscqCreate _ _ _ _ _ _ = return eOPNOTSUPP

fscqUnlink :: FSrunner -> Coq_fs_xparams -> FilePath -> IO Errno
fscqUnlink fr fsxp (_:path) = do
  r <- fr $ FS.delete fsxp rootDir path
  case r of
    True -> return eOK
    False -> return eIO
fscqUnlink _ _ _ = return eOPNOTSUPP

-- Wrappers for converting Coq_word to/from ByteString, with
-- the help of i2buf and buf2i from hslib/Disk.
blocksize :: Int
blocksize = _Valulen__valulen `div` 8

bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp _ _) = withForeignPtr fp buf2i

i2bs :: Integer -> IO BS.ByteString
i2bs i = BSI.create blocksize $ i2buf i

data BlockRange =
  BR !Int !Int !Int   -- blocknumber, offset-in-block, count-from-offset

compute_ranges_int :: Int -> Int -> [BlockRange]
compute_ranges_int off count = map mkrange $ zip3 blocknums startoffs endoffs
  where
    mkrange (blk, startoff, endoff) = BR blk startoff (endoff-startoff)
    blocknums = [off `div` blocksize .. (off + count) `div` blocksize]
    startoffs = [off `mod` blocksize] ++ replicate (length blocknums - 1) 0
    endoffs = replicate (length blocknums - 1) blocksize ++ [count `mod` blocksize]

compute_ranges :: FileOffset -> ByteCount -> [BlockRange]
compute_ranges off count =
  compute_ranges_int (fromIntegral off) (fromIntegral count)

fscqRead :: FSrunner -> Coq_fs_xparams -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead fr fsxp _ inum byteCount offset = do
  wlen <- fr $ FS.file_get_sz fsxp inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  offset <- return $ min offset len
  byteCount <- return $ min byteCount $ (fromIntegral len) - (fromIntegral offset)
  pieces <- mapM read_piece $ compute_ranges offset byteCount
  return $ Right $ BS.concat pieces

  where
    read_piece (BR blk off count) = do
      W w <- fr $ FS.read_block fsxp inum (W64 $ fromIntegral blk)
      bs <- i2bs w
      return $ BS.take count $ BS.drop off bs

compute_range_pieces :: FileOffset -> BS.ByteString -> [(BlockRange, BS.ByteString)]
compute_range_pieces off buf = zip ranges pieces
  where
    ranges = compute_ranges_int (fromIntegral off) (BS.length buf)
    pieces = map getpiece ranges
    getpiece (BR blk boff bcount) = BS.take bcount $ BS.drop bufoff buf
      where bufoff = (blk * blocksize) + boff - (fromIntegral off)

data WriteState =
   WriteOK !ByteCount
 | WriteErr !ByteCount

fscqWrite :: FSrunner -> Coq_fs_xparams -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite fr fsxp _ inum bs offset = do
  wlen <- fr $ FS.file_get_sz fsxp inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  r <- foldM (write_piece len) (WriteOK 0) (compute_range_pieces offset bs)
  case r of
    WriteOK c -> return $ Right c
    WriteErr c ->
      if c == 0 then
        return $ Left eIO 
      else
        return $ Right c

  where
    write_piece _ (WriteErr c) _ = return $ WriteErr c
    write_piece init_len (WriteOK c) (BR blk off cnt, piece_bs) = do
      W w <- fr $ FS.read_block fsxp inum (W64 $ fromIntegral blk)
      old_bs <- i2bs w
      new_bs <- return $ BS.append (BS.take off old_bs)
                       $ BS.append piece_bs
                       $ BS.drop (off + cnt) old_bs
      wnew <- bs2i new_bs
      ok <- fr $ FS.write_block fsxp inum (W64 $ fromIntegral blk) (W wnew)
      ok <-
        if ok then
          if blk*blocksize + off + cnt <= init_len then
            return True
          else
            fr $ FS.file_set_sz fsxp inum (W64 $ fromIntegral $ blk*blocksize + off + cnt)
        else
          return False
      if ok then
        return $ WriteOK (c + (fromIntegral cnt))
      else
        return $ WriteErr c

fscqSetFileSize :: FSrunner -> Coq_fs_xparams -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fr fsxp (_:path) size = do
  r <- fr $ FS.lookup fsxp rootDir path
  case r of
    Nothing -> return eNOENT
    Just inum -> do
      ok <- fr $ FS.file_set_sz fsxp inum (W64 $ fromIntegral size)
      if ok then
        return eOK
      else
        return eIO
fscqSetFileSize _ _ _ _ = return eIO

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
