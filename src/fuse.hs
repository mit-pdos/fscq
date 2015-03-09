{-# LANGUAGE RankNTypes #-}

module Main where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import qualified Data.ByteString.Internal as BSI
import qualified System.Directory
import Foreign.C.Error
import Foreign.ForeignPtr
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
import System.Fuse
import System.FilePath.Posix
import Word
import Disk
import Prog
import Data.IORef
import Interpreter as I
import qualified FS
import qualified MemLog
import FSLayout
import Control.Monad
import qualified DirName

-- Handle type for open files; we will use the inode number
type HT = Coq_word

disk_fn :: String
disk_fn = "disk.img"

-- File system configuration
cachesize :: Int
cachesize = 10000
nDataBitmaps :: Coq_word
nDataBitmaps = W64 1
nInodeBitmaps :: Coq_word
nInodeBitmaps = W64 1

type MSCS = MemLog.Coq_memstate_cachestate
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
      (s, (fsxp, ())) <- I.run ds $ MemLog._MEMLOG__recover cachesize
      return (s, fsxp)
  else
    do
      putStrLn $ "Initializing file system"
      (s, (fsxp, (ok, ()))) <- I.run ds $ FS.mkfs nDataBitmaps nInodeBitmaps cachesize
      if ok == False then error $ "mkfs failed" else return ()
      set_nblocks_disk ds $ wordToNat 64 $ coq_FSXPMaxBlock fsxp
      return (s, fsxp)
  putStrLn $ "Starting file system, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
  ref <- newIORef s
  fuseMain (fscqFSOps ds (doFScall ds ref) fsxp) defaultExceptionHandler

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: DiskState -> FSrunner -> Coq_fs_xparams -> FuseOperations HT
fscqFSOps ds fr fsxp = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fr fsxp
  , fuseOpen = fscqOpen fr fsxp
  , fuseCreateDevice = fscqCreate fr fsxp
  , fuseCreateDirectory = fscqCreateDir fr fsxp
  , fuseRemoveLink = fscqUnlink fr fsxp
  , fuseRemoveDirectory = fscqUnlink fr fsxp
  , fuseRead = fscqRead ds fr fsxp
  , fuseWrite = fscqWrite fr fsxp
  , fuseSetFileSize = fscqSetFileSize fr fsxp
  , fuseOpenDirectory = fscqOpenDirectory fr fsxp
  , fuseReadDirectory = fscqReadDirectory fr fsxp
  , fuseGetFileSystemStats = fscqGetFileSystemStats
  , fuseDestroy = fscqDestroy ds
  , fuseSetFileTimes = fscqSetFileTimes
  , fuseRename = fscqRename fr fsxp
  , fuseSetFileMode = fscqChmod
  }

fscqDestroy :: DiskState -> IO ()
fscqDestroy ds = do
  stats <- close_disk ds
  print_stats stats

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
                     [ ownerReadMode, ownerWriteMode, ownerExecuteMode
                     , groupReadMode, groupWriteMode, groupExecuteMode
                     , otherReadMode, otherWriteMode, otherExecuteMode
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
fscqGetFileStat fr fsxp (_:path)
  | path == "stats" = do
    ctx <- getFuseContext
    return $ Right $ fileStat ctx 1024
  | otherwise = do
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  case r of
    Nothing -> return $ Left eNOENT
    Just (inum, isdir)
      | wordToNat 64 isdir == 0 -> do
        (len, ()) <- fr $ FS.file_get_sz fsxp inum
        ctx <- getFuseContext
        return $ Right $ fileStat ctx $ fromIntegral $ wordToNat 64 len
      | otherwise -> do
        ctx <- getFuseContext
        return $ Right $ dirStat ctx
fscqGetFileStat _ _ _ = return $ Left eNOENT

fscqOpenDirectory :: FSrunner -> Coq_fs_xparams -> FilePath -> IO Errno
fscqOpenDirectory fr fsxp (_:path) = do
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  case r of
    Nothing -> return eNOENT
    Just (_, isdir)
      | wordToNat 64 isdir == 0 -> return eNOTDIR
      | otherwise -> return eOK
fscqOpenDirectory _ _ "" = return eNOENT

fscqReadDirectory :: FSrunner -> Coq_fs_xparams -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fr fsxp (_:path) = do
  ctx <- getFuseContext
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  case r of
    Nothing -> return $ Left $ eNOENT
    Just (dnum, isdir)
      | wordToNat 64 isdir == 0 -> return $ Left $ eNOTDIR
      | otherwise -> do
        (files, ()) <- fr $ FS.readdir fsxp dnum
        files_stat <- mapM (mkstat ctx) files
        return $ Right $ [(".",          dirStat ctx)
                         ,("..",         dirStat ctx)
                         ] ++ files_stat
  where
    mkstat ctx (fn, (inum, isdir))
      | wordToNat 64 isdir == 0 = do
        (len, ()) <- fr $ FS.file_get_sz fsxp inum
        return $ (fn, fileStat ctx $ fromIntegral $ wordToNat 64 len)
      | otherwise = return $ (fn, dirStat ctx)

fscqReadDirectory _ _ _ = return (Left (eNOENT))

fscqOpen :: FSrunner -> Coq_fs_xparams -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fr fsxp (_:path) _ _
  | path == "stats" = return $ Right $ W 0
  | otherwise = do
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  case r of
    Nothing -> return $ Left eNOENT
    Just (inum, isdir)
      | wordToNat 64 isdir == 0 -> return $ Right $ inum
      | otherwise -> return $ Left eISDIR
fscqOpen _ _ _ _ _ = return $ Left eIO

splitDirsFile :: String -> ([String], String)
splitDirsFile path = (init parts, last parts)
  where parts = splitDirectories path

fscqCreate :: FSrunner -> Coq_fs_xparams -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fr fsxp (_:path) RegularFile _ _ = do
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dirparts
  case rd of
    Nothing -> return eNOENT
    Just (dnum, isdir)
      | wordToNat 64 isdir == 0 -> return eNOTDIR
      | otherwise -> do
        (r, ()) <- fr $ FS.create fsxp dnum filename
        case r of
          Nothing -> return eNOSPC
          Just _ -> return eOK
fscqCreate _ _ _ _ _ _ = return eOPNOTSUPP

fscqCreateDir :: FSrunner -> Coq_fs_xparams -> FilePath -> FileMode -> IO Errno
fscqCreateDir fr fsxp (_:path) _ = do
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dirparts
  case rd of
    Nothing -> return eNOENT
    Just (dnum, isdir)
      | wordToNat 64 isdir == 0 -> return eNOTDIR
      | otherwise -> do
        (r, ()) <- fr $ FS.mkdir fsxp dnum filename
        case r of
          Nothing -> return eNOSPC
          Just _ -> return eOK
fscqCreateDir _ _ _ _ = return eOPNOTSUPP

fscqUnlink :: FSrunner -> Coq_fs_xparams -> FilePath -> IO Errno
fscqUnlink fr fsxp (_:path) = do
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dirparts
  case rd of
    Nothing -> return eNOENT
    Just (dnum, isdir)
      | wordToNat 64 isdir == 0 -> return eNOTDIR
      | otherwise -> do
        (r, ()) <- fr $ FS.delete fsxp dnum filename
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
    blocknums = [off `div` blocksize .. (off + count - 1) `div` blocksize]
    startoffs = [off `mod` blocksize] ++ replicate (length blocknums - 1) 0
    endoffs = replicate (length blocknums - 1) blocksize ++ [(off + count - 1) `mod` blocksize + 1]

compute_ranges :: FileOffset -> ByteCount -> [BlockRange]
compute_ranges off count =
  compute_ranges_int (fromIntegral off) (fromIntegral count)

fscqRead :: DiskState -> FSrunner -> Coq_fs_xparams -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead ds fr fsxp (_:path) inum byteCount offset
  | path == "stats" = do
    Stats r w s <- get_stats ds
    clear_stats ds
    statbuf <- return $ BSC8.pack $
      "Reads:  " ++ (show r) ++ "\n" ++
      "Writes: " ++ (show w) ++ "\n" ++
      "Syncs:  " ++ (show s) ++ "\n"
    return $ Right statbuf
  | otherwise = do
  (wlen, ()) <- fr $ FS.file_get_sz fsxp inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  offset' <- return $ min offset len
  byteCount' <- return $ min byteCount $ (fromIntegral len) - (fromIntegral offset')
  pieces <- mapM read_piece $ compute_ranges offset' byteCount'
  return $ Right $ BS.concat pieces

  where
    read_piece (BR blk off count) = do
      (W w, ()) <- fr $ FS.read_block fsxp inum (W64 $ fromIntegral blk)
      bs <- i2bs w
      return $ BS.take count $ BS.drop off bs

fscqRead _ _ _ [] _ _ _ = do
  return $ Left $ eIO

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
  (wlen, ()) <- fr $ FS.file_get_sz fsxp inum
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
      (W w, ()) <- if blk*blocksize < init_len then
          fr $ FS.read_block fsxp inum (W64 $ fromIntegral blk)
        else
          return $ (W 0, ())
      old_bs <- i2bs w
      new_bs <- return $ BS.append (BS.take off old_bs)
                       $ BS.append piece_bs
                       $ BS.drop (off + cnt) old_bs
      wnew <- bs2i new_bs
      (ok, ()) <- fr $ FS.write_block fsxp inum (W64 $ fromIntegral blk) (W wnew) (W64 $ fromIntegral $ blk*blocksize + off + cnt)
      if ok then
        return $ WriteOK (c + (fromIntegral cnt))
      else
        return $ WriteErr c

fscqSetFileSize :: FSrunner -> Coq_fs_xparams -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fr fsxp (_:path) size = do
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  case r of
    Nothing -> return eNOENT
    Just (inum, isdir)
      | wordToNat 64 isdir == 0 -> do
        (ok, ()) <- fr $ FS.file_set_sz fsxp inum (W64 $ fromIntegral size)
        if ok then
          return eOK
        else
          return eIO
      | otherwise -> return eISDIR
fscqSetFileSize _ _ _ _ = return eIO

fscqGetFileSystemStats :: String -> IO (Either Errno FileSystemStats)
fscqGetFileSystemStats _ =
  return $ Right $ FileSystemStats
    { fsStatBlockSize = 4096
    , fsStatBlockCount = 1
    , fsStatBlocksFree = 1
    , fsStatBlocksAvailable = 1
    , fsStatFileCount = 5
    , fsStatFilesFree = 10
    , fsStatMaxNameLength = fromIntegral DirName._SDIR__namelen
    }

fscqSetFileTimes :: FilePath -> EpochTime -> EpochTime -> IO Errno
fscqSetFileTimes _ _ _ = do
  return eOK

fscqRename :: FSrunner -> Coq_fs_xparams -> FilePath -> FilePath -> IO Errno
fscqRename fr fsxp (_:src) (_:dst) = do
  (srcparts, srcname) <- return $ splitDirsFile src
  (dstparts, dstname) <- return $ splitDirsFile dst
  (rsrc, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) srcparts
  (rdst, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dstparts
  case (rsrc, rdst) of
    (Just (dsrc, isdirsrc), Just (ddst, isdirdst))
      | wordToNat 64 isdirsrc == 0 || wordToNat 64 isdirdst == 0 ->
        return eNOTDIR
      | otherwise -> do
        (r, ()) <- fr $ FS.rename fsxp dsrc srcname ddst dstname
        case r of
          True -> return eOK
          False -> return eIO
    _ -> return eNOENT
fscqRename _ _ _ _ = return eIO

fscqChmod :: FilePath -> FileMode -> IO Errno
fscqChmod _ _ = do
  return eOK
