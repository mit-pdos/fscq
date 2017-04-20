{-# LANGUAGE RankNTypes, MagicHash #-}

module Main where

import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import qualified System.Directory
import Foreign.C.Error
import System.Posix.Types
import System.Posix.Files
import System.Posix.IO
import System.FilePath.Posix
import Word
import Disk
import CCLProg
import Fuse
import Data.IORef
import Interpreter as SeqI
import ConcurInterp as I
import qualified AsyncFS
import qualified ConcurrentFS as CFS
import FSProtocol
import FSLayout
import qualified DirName
import Inode
import Text.Printf
import qualified System.Process
import qualified Data.List
import AsyncDisk
import Control.Monad
import qualified Errno
import ShowErrno
import System.Clock
import Options

-- Handle type for open files; we will use the inode number
type HT = Integer

verboseFuse :: Bool
verboseFuse = False

verboseTiming :: Bool
verboseTiming = True

cachesize :: Integer
cachesize = 100000

data CfscqOptions = CfscqOptions
  { 
    -- This controls whether HFuse will use upcalls (FUSE threads entering GHC runtime)
    -- or downcalls (separate FUSE threads using a queue, and GHC accessing this queue
    -- using its own threads).
    optUseDowncalls :: Bool }

instance Options CfscqOptions where
  defineOptions = pure CfscqOptions
    <*> simpleOption "use-downcalls" True
         "use downcalls (opqueue) rather than C->HS upcalls"

debug :: String -> IO ()
debug msg =
  if verboseFuse then
    putStrLn msg
  else
    return ()

debugStart :: Show a => String -> a -> IO ()
debugStart op msg = debug $ op ++ ": " ++ (show msg)

debugMore :: Show a => a -> IO ()
debugMore msg = debug $ " .. " ++ (show msg)

-- File system configuration
nDataBitmaps :: Integer
nDataBitmaps = 1
nInodeBitmaps :: Integer
nInodeBitmaps = 1
nDescrBlocks :: Integer
nDescrBlocks = 64

type FSprog a = Coq_cprog a
type FSrunner = forall a. FSprog (CFS.SyscallResult a) -> IO a

elapsedTime :: TimeSpec -> IO ()
elapsedTime start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsedMicros = (fromIntegral elapsedNanos)/1e3 :: Float in
    putStrLn $ "took " ++ show elapsedMicros ++ "us"

timeAction :: IO a -> IO a
timeAction io = if verboseTiming then
  do
    start <- getTime Monotonic
    r <- io
    elapsedTime start
    return r
  else io

doFScall :: I.ConcurState -> FSrunner
doFScall s p = do
  r <- I.run s p
  case r of
    CFS.Done v -> return v
    CFS.TryAgain -> error $ "system call loop failed?"
    CFS.SyscallFailed -> error $ "system call failed"

main :: IO ()
main = runCommand $ \opts args -> do
  case args of
    fn:rest -> run_fuse (optUseDowncalls opts) fn rest
    _ -> putStrLn $ "Usage: fscq disk -f /tmp/ft"

run_fuse :: Bool -> String -> [String] -> IO()
run_fuse useDowncalls disk_fn fuse_args = do
  fileExists <- System.Directory.doesFileExist disk_fn
  ds <- case disk_fn of
    "/tmp/crashlog.img" -> init_disk_crashlog disk_fn
    _ -> init_disk disk_fn
  (mscs0, fsxp_val) <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      res <- SeqI.run ds $ AsyncFS._AFS__recover cachesize
      case res of
        Errno.Err _ -> error $ "recovery failed; not an fscq fs?"
        Errno.OK (mscs0, fsxp_val) -> do
          return (mscs0, fsxp_val)
  else
    do
      putStrLn $ "Initializing file system"
      res <- SeqI.run ds $ AsyncFS._AFS__mkfs cachesize nDataBitmaps nInodeBitmaps nDescrBlocks
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (mscs0, fsxp_val) -> do
          set_nblocks_disk ds $ fromIntegral $ coq_FSXPMaxBlock fsxp_val
          return (mscs0, fsxp_val)
  putStrLn $ "Starting file system, " ++ (show $ coq_FSXPMaxBlock fsxp_val) ++ " blocks " ++ "magic " ++ (show $ coq_FSXPMagic fsxp_val)
  s <- I.newState ds
  fsP <- I.run s (CFS.init fsxp_val mscs0)
  fuseRun "cfscq" fuse_args (fscqFSOps disk_fn ds (doFScall s) s fsP) defaultExceptionHandler useDowncalls

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: String -> DiskState -> FSrunner -> I.ConcurState -> FsParams -> FuseOperations HT
fscqFSOps fn ds fr s fsP = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fr fsP
  , fuseOpen = fscqOpen fr fsP
  , fuseCreateDevice = fscqCreate fr fsP
  , fuseCreateDirectory = fscqCreateDir fr fsP
  , fuseRemoveLink = fscqUnlink fr fsP
  , fuseRemoveDirectory = fscqUnlink fr fsP
  , fuseRead = fscqRead ds fr fsP
  , fuseWrite = fscqWrite fr fsP
  , fuseSetFileSize = fscqSetFileSize fr fsP
  , fuseOpenDirectory = fscqOpenDirectory fr fsP
  , fuseReadDirectory = fscqReadDirectory fr fsP
  , fuseGetFileSystemStats = fscqGetFileSystemStats fr s fsP
  , fuseDestroy = fscqDestroy ds fn fr fsP
  , fuseSetFileTimes = fscqSetFileTimes
  , fuseRename = fscqRename fr fsP
  , fuseSetFileMode = fscqChmod
  , fuseSynchronizeFile = fscqSyncFile fr fsP
  , fuseSynchronizeDirectory = fscqSyncDir fr fsP
  }

applyFlushgroup :: DiskState -> [(Integer, Coq_word)] -> IO ()
applyFlushgroup _ [] = return ()
applyFlushgroup ds ((a, v) : rest) = do
  applyFlushgroup ds rest
  write_disk ds a v

applyFlushgroups :: DiskState -> [[(Integer, Coq_word)]] -> IO ()
applyFlushgroups _ [] = return ()
applyFlushgroups ds (flushgroup : rest) = do
  applyFlushgroups ds rest
  applyFlushgroup ds flushgroup

materializeFlushgroups :: IORef Integer -> [[(Integer, Coq_word)]] -> IO ()
materializeFlushgroups idxref groups = do
  idx <- readIORef idxref
  writeIORef idxref (idx+1)
  _ <- System.Process.system $ printf "cp --sparse=always /tmp/crashlog.img /tmp/crashlog-%06d.img" idx
  ds <- init_disk $ printf "/tmp/crashlog-%06d.img" idx
  applyFlushgroups ds groups
  _ <- close_disk ds
  return ()

writeSubsets' :: [[(Integer, a)]] -> [[(Integer, a)]]
writeSubsets' [] = [[]]
writeSubsets' (heads : tails) =
    tailsubsets ++ (concat $ map (\ts -> map (\hd -> hd : ts) heads) tailsubsets)
  where
    tailsubsets = writeSubsets' tails

writeSubsets :: [(Integer, a)] -> [[(Integer, a)]]
writeSubsets writes = writeSubsets' addrWrites
  where
    addrWrites = Data.List.groupBy sameaddr writes
    sameaddr (x, _) (y, _) = (x == y)

materializeCrashes :: IORef Integer -> [[(Integer, Coq_word)]] -> IO ()
materializeCrashes idxref [] = materializeFlushgroups idxref []
materializeCrashes idxref (lastgroup : othergroups) = do
  materializeCrashes idxref othergroups
  mapM_ (\lastsubset -> materializeFlushgroups idxref (lastsubset : othergroups)) $ writeSubsets lastgroup


fscqDestroy :: DiskState -> String -> FSrunner -> FsParams -> IO ()
fscqDestroy ds disk_fn fr fsP  = do
  _ <- fr $ CFS.umount fsP
  stats <- close_disk ds
  print_stats stats
  case disk_fn of
    "/tmp/crashlog.img" -> do
      flushgroups <- get_flush_log ds
      putStrLn $ "Number of flush groups: " ++ (show (length flushgroups))
      idxref <- newIORef 0
      materializeCrashes idxref flushgroups
    _ -> return ()

dirStat :: FuseContext -> FileStat
dirStat ctx = FileStat
  { statEntryType = Directory
  , statFileMode = foldr1 unionFileModes
                     [ ownerReadMode, ownerWriteMode, ownerExecuteMode
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

attrToType :: INODE__Coq_iattr -> EntryType
attrToType attr =
  if t == 0 then RegularFile else Socket
  where t = wordToNat 32 $ _INODE__coq_AType attr

fileStat :: FuseContext -> INODE__Coq_iattr -> FileStat
fileStat ctx attr = FileStat
  { statEntryType = attrToType attr
  , statFileMode = foldr1 unionFileModes
                     [ ownerReadMode, ownerWriteMode, ownerExecuteMode
                     , groupReadMode, groupWriteMode, groupExecuteMode
                     , otherReadMode, otherWriteMode, otherExecuteMode
                     ]
  , statLinkCount = 1
  , statFileOwner = fuseCtxUserID ctx
  , statFileGroup = fuseCtxGroupID ctx
  , statSpecialDeviceID = 0
  , statFileSize = fromIntegral $ wordToNat 64 $ _INODE__coq_ABytes attr
  , statBlocks = 1
  , statAccessTime = 0
  , statModificationTime = fromIntegral $ wordToNat 32 $ _INODE__coq_AMTime attr
  , statStatusChangeTime = 0
  }

fscqGetFileStat :: FSrunner -> FsParams -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat fr fsP (_:path)
  | path == "stats" = do
    ctx <- getFuseContext
    return $ Right $ fileStat ctx $ _INODE__iattr_upd _INODE__iattr0 $ INODE__UBytes $ W 4096
  -- | otherwise = timeAction $ do
  | otherwise = do
  debugStart "STAT" path
  -- tid <- myThreadId
  -- (processor, _) <- threadCapability tid
  -- bound <- isCurrentThreadBound
  -- putStrLn $ show tid ++ " capability: " ++ show processor ++
  --   if bound then " (bound)" else ""
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ CFS.lookup fsP nameparts
  debugMore r
  case r of
    Errno.Err e -> return $ Left $ errnoToPosix e
    Errno.OK (inum, isdir)
      | isdir -> do
        ctx <- getFuseContext
        return $ Right $ dirStat ctx
      | otherwise -> do
        (attr, ()) <- fr $ CFS.file_get_attr fsP inum
        ctx <- getFuseContext
        return $ Right $ fileStat ctx attr
fscqGetFileStat _ _ _ = return $ Left eNOENT

fscqOpenDirectory :: FSrunner -> FsParams -> FilePath -> IO (Either Errno HT)
fscqOpenDirectory fr fsP (_:path) = do
  debugStart "OPENDIR" path
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ CFS.lookup fsP nameparts
  debugMore r
  case r of
    Errno.Err e -> return $ Left $ errnoToPosix e
    Errno.OK (inum, isdir)
      | isdir -> return $ Right inum
      | otherwise -> return $ Left eNOTDIR
fscqOpenDirectory _ _ "" = return $ Left eNOENT

fscqReadDirectory :: FSrunner -> FsParams -> FilePath -> HT -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fr fsP _ dnum = do
  debugStart "READDIR" dnum
  ctx <- getFuseContext
  (files, ()) <- fr $ CFS.readdir fsP dnum
  files_stat <- mapM (mkstat ctx) files
  return $ Right $ [(".",          dirStat ctx)
                   ,("..",         dirStat ctx)
                   ] ++ files_stat
  where
    mkstat ctx (fn, (inum, isdir))
      | isdir = return $ (fn, dirStat ctx)
      | otherwise = do
        (attr, ()) <- fr $ CFS.file_get_attr fsP inum
        return $ (fn, fileStat ctx attr)

fscqOpen :: FSrunner -> FsParams -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fr fsP (_:path) _ _
  | path == "stats" = return $ Right 0
  -- | otherwise = timeAction $ do
  | otherwise = do
  debugStart "OPEN" path
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ CFS.lookup fsP nameparts
  debugMore r
  case r of
    Errno.Err e -> return $ Left $ errnoToPosix e
    Errno.OK (inum, isdir)
      | isdir -> return $ Left eISDIR
      | otherwise -> return $ Right $ inum
fscqOpen _ _ _ _ _ = return $ Left eIO

splitDirsFile :: String -> ([String], String)
splitDirsFile path = (init parts, last parts)
  where parts = splitDirectories path

fscqCreate :: FSrunner -> FsParams -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fr fsP (_:path) entrytype _ _ = do
  debugStart "CREATE" path
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ CFS.lookup fsP dirparts
  debugMore rd
  case rd of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        (r, ()) <- case entrytype of
          RegularFile -> fr $ CFS.create fsP dnum filename
          Socket -> fr $ CFS.mksock fsP dnum filename
          _ -> return (Errno.Err Errno.EINVAL, ())
        debugMore r
        case r of
          Errno.Err e -> return $ errnoToPosix e
          Errno.OK _ -> return eOK
      | otherwise -> return eNOTDIR
fscqCreate _ _ _ _ _ _ = return eOPNOTSUPP

fscqCreateDir :: FSrunner -> FsParams -> FilePath -> FileMode -> IO Errno
fscqCreateDir fr fsP (_:path) _ = do
  debugStart "MKDIR" path
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ CFS.lookup fsP dirparts
  debugMore rd
  case rd of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        (r, ()) <- fr $ CFS.mkdir fsP dnum filename
        debugMore r
        case r of
          Errno.Err e -> return $ errnoToPosix e
          Errno.OK _ -> return eOK
      | otherwise -> return eNOTDIR
fscqCreateDir _ _ _ _ = return eOPNOTSUPP

fscqUnlink :: FSrunner -> FsParams -> FilePath -> IO Errno
fscqUnlink fr fsP (_:path) = do
  debugStart "UNLINK" path
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ CFS.lookup fsP dirparts
  debugMore rd
  case rd of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        (r, ()) <- fr $ CFS.delete fsP dnum filename
        debugMore r
        case r of
          Errno.OK _ -> return eOK
          Errno.Err e -> return $ errnoToPosix e
      | otherwise -> return eNOTDIR
fscqUnlink _ _ _ = return eOPNOTSUPP

-- Wrappers for converting Coq_word to/from ByteString, with
-- the help of i2buf and buf2i from hslib/Disk.
blocksize :: Integer
blocksize = _Valulen__valulen `div` 8

data BlockRange =
  BR !Integer !Integer !Integer   -- blocknumber, offset-in-block, count-from-offset

compute_ranges_int :: Integer -> Integer -> [BlockRange]
compute_ranges_int off count = map mkrange $ zip3 blocknums startoffs endoffs
  where
    mkrange (blk, startoff, endoff) = BR blk startoff (endoff-startoff)
    blocknums = [off `div` blocksize .. (off + count - 1) `div` blocksize]
    startoffs = [off `mod` blocksize] ++ replicate (length blocknums - 1) 0
    endoffs = replicate (length blocknums - 1) blocksize ++ [(off + count - 1) `mod` blocksize + 1]

compute_ranges :: FileOffset -> ByteCount -> [BlockRange]
compute_ranges off count =
  compute_ranges_int (fromIntegral off) (fromIntegral count)

fscqRead :: DiskState -> FSrunner -> FsParams -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead ds fr fsP (_:path) inum byteCount offset
  | path == "stats" = do
    Stats r w s <- get_stats ds
    clear_stats ds
    statbuf <- return $ BSC8.pack $
      "Reads:  " ++ (show r) ++ "\n" ++
      "Writes: " ++ (show w) ++ "\n" ++
      "Syncs:  " ++ (show s) ++ "\n"
    return $ Right statbuf
  | otherwise = do
  (wlen, ()) <- fr $ CFS.file_get_sz fsP inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  offset' <- return $ min offset len
  byteCount' <- return $ min byteCount $ (fromIntegral len) - (fromIntegral offset')
  pieces <- mapM read_piece $ compute_ranges offset' byteCount'
  return $ Right $ BS.concat pieces

  where
    read_piece (BR blk off count) = do
      (W w, ()) <- fr $ CFS.read_fblock fsP inum blk
      bs <- i2bs w 4096
      return $ BS.take (fromIntegral count) $ BS.drop (fromIntegral off) bs

fscqRead _ _ _ _ _ _ _ = return $ Left eIO

compute_range_pieces :: FileOffset -> BS.ByteString -> [(BlockRange, BS.ByteString)]
compute_range_pieces off buf = zip ranges pieces
  where
    ranges = compute_ranges_int (fromIntegral off) $ fromIntegral $ BS.length buf
    pieces = map getpiece ranges
    getpiece (BR blk boff bcount) = BS.take (fromIntegral bcount) $ BS.drop (fromIntegral bufoff) buf
      where bufoff = (blk * blocksize) + boff - (fromIntegral off)

data WriteState =
   WriteOK !ByteCount
 | WriteErr !ByteCount

fscqWrite :: FSrunner -> FsParams -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite fr fsP path inum bs offset = do
  debugStart "WRITE" (path, inum)
  (wlen, ()) <- fr $ CFS.file_get_sz fsP inum
  len <- return $ fromIntegral $ wordToNat 64 wlen
  endpos <- return $ (fromIntegral offset) + (fromIntegral (BS.length bs))
  okspc <- if len < endpos then do
    (ok, _) <- fr $ CFS.file_truncate fsP inum ((endpos + 4095) `div` 4096)
    return ok
  else
    return $ Errno.OK ()
  case okspc of
    Errno.OK _ -> do
      r <- foldM (write_piece len) (WriteOK 0) (compute_range_pieces offset bs)
      case r of
        WriteOK c -> do
          okspc2 <- if len < endpos then do
            (ok, _) <- fr $ CFS.file_set_sz fsP inum (W endpos)
            return ok
          else
            return $ (Errno.OK ())
          case okspc2 of
            Errno.OK _ -> return $ Right c
            Errno.Err _ -> return $ Left eNOSPC
        WriteErr c ->
          if c == 0 then
            return $ Left eIO
          else
            return $ Right c
    Errno.Err e -> do
      return $ Left $ errnoToPosix e
  where
    write_piece _ (WriteErr c) _ = return $ WriteErr c
    write_piece init_len (WriteOK c) (BR blk off cnt, piece_bs) = do
      new_bs <- if cnt == blocksize then
          return piece_bs
        else do
          (W w, ()) <- if blk*blocksize < init_len then
              fr $ CFS.read_fblock fsP inum blk
            else
              return $ (W 0, ())
          old_bs <- i2bs w 4096
          return $ BS.append (BS.take (fromIntegral off) old_bs)
                 $ BS.append piece_bs
                 $ BS.drop (fromIntegral $ off + cnt) old_bs
      wnew <- bs2i new_bs
      -- _ <- fr $ CFS.update_fblock_d fsP inum blk (W wnew)
      _ <- fr $ CFS.update_fblock fsP inum blk (W wnew)
      return $ WriteOK (c + (fromIntegral cnt))

fscqSetFileSize :: FSrunner -> FsParams -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fr fsP (_:path) size = do
  debugStart "SETSIZE" (path, size)
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ CFS.lookup fsP nameparts
  debugMore r
  case r of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (inum, isdir)
      | isdir -> return eISDIR
      | otherwise -> do
        (ok, ()) <- fr $ CFS.file_set_sz fsP inum (W64 $ fromIntegral size)
        case ok of
          Errno.OK _ -> return eOK
          Errno.Err e -> return $ errnoToPosix e
fscqSetFileSize _ _ _ _ = return eIO

fscqGetFileSystemStats :: FSrunner -> I.ConcurState -> FsParams -> String -> IO (Either Errno FileSystemStats)
fscqGetFileSystemStats fr _ fsP _ = do
  (freeblocks, (freeinodes, ())) <- fr $ CFS.statfs fsP
  block_bitmaps <- return $ coq_BmapNBlocks $ coq_FSXPBlockAlloc1 (fsxp fsP)
  inode_bitmaps <- return $ coq_BmapNBlocks $ coq_FSXPInodeAlloc (fsxp fsP)
  return $ Right $ FileSystemStats
    { fsStatBlockSize = 4096
    , fsStatBlockCount = 8 * 4096 * (fromIntegral $ block_bitmaps)
    , fsStatBlocksFree = fromIntegral $ freeblocks
    , fsStatBlocksAvailable = fromIntegral $ freeblocks
    , fsStatFileCount = 8 * 4096 * (fromIntegral $ inode_bitmaps)
    , fsStatFilesFree = fromIntegral $ freeinodes
    , fsStatMaxNameLength = fromIntegral DirName._SDIR__namelen
    }

fscqSetFileTimes :: FilePath -> EpochTime -> EpochTime -> IO Errno
fscqSetFileTimes _ _ _ = do
  return eOK

fscqRename :: FSrunner -> FsParams -> FilePath -> FilePath -> IO Errno
fscqRename fr fsP (_:src) (_:dst) = do
  debugStart "RENAME" (src, dst)
  (srcparts, srcname) <- return $ splitDirsFile src
  (dstparts, dstname) <- return $ splitDirsFile dst
  (r, ()) <- fr $ CFS.rename fsP (coq_FSXPRootInum (fsxp fsP)) srcparts srcname dstparts dstname
  debugMore r
  case r of
    Errno.OK _ -> return eOK
    Errno.Err e -> return $ errnoToPosix e
fscqRename _ _ _ _ = return eIO

fscqChmod :: FilePath -> FileMode -> IO Errno
fscqChmod _ _ = do
  return eOK

fscqSyncFile :: FSrunner -> FsParams -> FilePath -> HT -> SyncType -> IO Errno
fscqSyncFile fr fsP _ inum syncType = do
  debugStart "SYNC FILE" inum
  _ <- fr $ CFS.file_sync fsP inum
  case syncType of
    DataSync -> return eOK
    FullSync -> do
      _ <- fr $ CFS.tree_sync fsP
      return eOK

fscqSyncDir :: FSrunner -> FsParams -> FilePath -> HT -> SyncType -> IO Errno
fscqSyncDir fr fsP _ inum _ = do
  debugStart "SYNC DIR" inum
  _ <- fr $ CFS.tree_sync fsP
  return eOK
