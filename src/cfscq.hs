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
import System.IO
import System.CPUTime
import System.Exit
import Word
import Disk
import Fuse
import Interpreter as SeqI
import qualified CoopConcur
import Data.IORef
-- import qualified Interpeter as SeqI
import ConcurInterp as I
import qualified DirectoryIsolatedFS as FS
import qualified AsyncFS
import FSLayout
import qualified DirName
import System.Environment
import Inode
import Text.Printf
import qualified System.Process
import qualified Data.List
import AsyncDisk
import Control.Monad
import Control.Concurrent
import Options
import qualified Errno

-- Handle type for open files; we will use the inode number
type HT = Integer

verboseFuse :: Bool
verboseFuse = False

cachesize :: Integer
cachesize = 100000

debug :: String -> IO ()
debug msg =
  if verboseFuse then
    putStrLn msg
  else
    return ()

debugStart :: Show a => String -> a -> IO ()
debugStart op msg = do
  t <- getCPUTime
  debug $ op ++ " [" ++ show t ++ "]" ++ ": " ++ (show msg)

debugMore :: Show a => a -> IO ()
debugMore msg = debug $ " .. " ++ (show msg)

-- File system configuration
nDataBitmaps :: Integer
nDataBitmaps = 1
nInodeBitmaps :: Integer
nInodeBitmaps = 1
nDescrBlocks :: Integer
nDescrBlocks = 64

type FSprog a = CoopConcur.Coq_prog a
type FSrunner = forall a. CoopConcur.Coq_prog (Maybe a) -> IO a

-- (ps, next tid)
type SystemState = (ProgramState, IORef Int)

interpreter :: FscqOptions -> SystemState -> FSrunner
interpreter opts (ps, m_tid) p = do
  tid <- readIORef m_tid
  modifyIORef m_tid (+1)
  ret <- newEmptyMVar
  _ <- forkIO $ do
    r <- I.run (interpOptions opts) ps tid p
    case r of
      Just v -> putMVar ret v
      Nothing -> error $ "loop timed out in thread " ++ show tid
  takeMVar ret

data FscqOptions = FscqOptions
  { -- additional logging
    optVerboseFuse :: Bool
  , optVerboseInterpret :: Bool
  , optTimeReads :: Bool
    -- enable/disable I/O concurrency
  , optActuallyYield :: Bool
  } deriving (Show)

instance Options FscqOptions where
  defineOptions = pure FscqOptions
    <*> simpleOption "verbose-fuse" False
    "Log each FUSE operation"
    <*> simpleOption "verbose-interpret" False
    "Log each interpreter operation"
    <*> simpleOption "time-reads" False
    "Log timing for each disk red"
    <*> simpleOption "yield" True
    "Enable/disable I/O concurrency: if false, yields do not give up the global lock."

interpOptions :: FscqOptions -> InterpOptions
interpOptions (FscqOptions _ verboseInterpret timeReads actuallyYield) =
  InterpOptions verboseInterpret timeReads actuallyYield

-- Get parsed options and remaining arguments
--
-- Errors out if option parsing fails, and handles --help by printing options
-- and exiting.
getOptions :: IO (FscqOptions, [String])
getOptions = do
  args <- getArgs
  let parsed = parseOptions args
  case parsedOptions parsed of
    Just opts -> return (opts, parsedArguments parsed)
    Nothing -> case parsedError parsed of
      Just err -> do
        hPutStrLn stderr err
        hPutStrLn stderr (parsedHelp parsed)
        exitFailure
      Nothing -> do
        putStrLn (parsedHelp parsed)
        exitSuccess

main :: IO ()
main = do
  (opts, args) <- getOptions
  case args of
    fn:rest -> run_fuse opts fn rest
    _ -> putStrLn $ "Usage: fuse disk -f /tmp/ft"

run_fuse :: FscqOptions -> String -> [String] -> IO()
run_fuse opts disk_fn fuse_args = do
  fileExists <- System.Directory.doesFileExist disk_fn
  ds <- case disk_fn of
    "/tmp/crashlog.img" -> init_disk_crashlog disk_fn
    _ -> init_disk disk_fn
  (s, fsxp) <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      res <- SeqI.run ds $ AsyncFS._AFS__recover cachesize
      case res of
        Errno.Err _ -> error $ "recovery failed"
        Errno.OK (s, fsxp) -> return (s, fsxp)
  else
    do
      putStrLn $ "Initializing file system"
      res <- SeqI.run ds $ AsyncFS._AFS__mkfs cachesize nDataBitmaps nInodeBitmaps nDescrBlocks
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (s, fsxp) -> do
          set_nblocks_disk ds $ fromIntegral $ coq_FSXPMaxBlock fsxp
          return (s, fsxp)
  cs <- init_concurrency
  putStrLn $ "Starting file system, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
  I.run (interpOptions opts) (ds, cs) 0 (FS.init_fs fsxp s)
  m_tid <- newIORef 1
  fuseRun "fscq" fuse_args (fscqFSOps disk_fn (ds, cs) (interpreter opts ((ds, cs), m_tid))) defaultExceptionHandler

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: String -> ProgramState -> FSrunner -> FuseOperations HT
fscqFSOps fn (ds, _) fr = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fr
  , fuseOpen = fscqOpen fr
  , fuseCreateDevice = fscqCreate fr
  , fuseCreateDirectory = fscqCreateDir fr
  , fuseRemoveLink = fscqUnlink fr
  , fuseRemoveDirectory = fscqUnlink fr
  , fuseRead = fscqRead ds fr
  , fuseWrite = fscqWrite fr
  , fuseSetFileSize = fscqSetFileSize fr
  , fuseOpenDirectory = fscqOpenDirectory fr
  , fuseReadDirectory = fscqReadDirectory fr
  , fuseGetFileSystemStats = fscqGetFileSystemStats fr
  , fuseDestroy = fscqDestroy ds fn fr
  , fuseSetFileTimes = fscqSetFileTimes
  , fuseRename = fscqRename fr
  , fuseSetFileMode = fscqChmod
  , fuseSynchronizeFile = fscqSyncFile fr
  , fuseSynchronizeDirectory = fscqSyncDir fr
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

errnoToPosix :: Errno.Errno -> Errno
errnoToPosix Errno.ELOGOVERFLOW = eIO
errnoToPosix Errno.ENOTDIR      = eNOTDIR
errnoToPosix Errno.EISDIR       = eISDIR
errnoToPosix Errno.ENOENT       = eNOENT
errnoToPosix Errno.EFBIG        = eFBIG
errnoToPosix Errno.ENAMETOOLONG = eNAMETOOLONG
errnoToPosix Errno.EEXIST       = eEXIST
errnoToPosix Errno.ENOSPCBLOCK  = eNOSPC
errnoToPosix Errno.ENOSPCINODE  = eNOSPC
errnoToPosix Errno.ENOTEMPTY    = eNOTEMPTY
errnoToPosix Errno.EINVAL       = eINVAL

instance Show Errno.Errno where
  show Errno.ELOGOVERFLOW = "ELOGOVERFLOW"
  show Errno.ENOTDIR      = "ENOTDIR"
  show Errno.EISDIR       = "EISDIR"
  show Errno.ENOENT       = "ENOENT"
  show Errno.EFBIG        = "EFBIG"
  show Errno.ENAMETOOLONG = "ENAMETOOLONG"
  show Errno.EEXIST       = "EEXIST"
  show Errno.ENOSPCBLOCK  = "ENOSPCBLOCK"
  show Errno.ENOSPCINODE  = "ENOSPCINODE"
  show Errno.ENOTEMPTY    = "ENOTEMPTY"
  show Errno.EINVAL       = "EINVAL"

instance Show t => Show (Errno.Coq_res t) where
  show (Errno.OK v) = show v
  show (Errno.Err e) = show e

fscqDestroy :: DiskState -> String -> FSrunner -> IO ()
fscqDestroy ds disk_fn fr = do
  _ <- fr $ FS.umount retries
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

-- should only retry once per read (miss) in a given system call, which shouldn't be too high
retries :: Integer
retries = 100

fscqGetFileStat :: FSrunner -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat fr (_:path)
  | path == "stats" = do
    ctx <- getFuseContext
    return $ Right $ fileStat ctx $ _INODE__iattr_upd _INODE__iattr0 $ INODE__UBytes $ W 4096
  | otherwise = do
    debugStart "STAT" path
    nameparts <- return $ splitDirectories path
    r <- fr $ FS.lookup_root nameparts retries
    debugMore r
    case r of
      Errno.Err e -> return $ Left $ errnoToPosix e
      Errno.OK (inum, isdir)
        | isdir -> do
          ctx <- getFuseContext
          return $ Right $ dirStat ctx
        | otherwise -> do
          attr <- fr $ FS.file_get_attr inum retries
          ctx <- getFuseContext
          return $ Right $ fileStat ctx attr
fscqGetFileStat _ _ = return $ Left eNOENT

fscqOpenDirectory :: FSrunner -> FilePath -> IO Errno
fscqOpenDirectory fr (_:path) = do
  debugStart "OPENDIR" path
  nameparts <- return $ splitDirectories path
  r <- fr $ FS.lookup_root nameparts retries
  debugMore r
  case r of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (_, isdir)
      | isdir -> return eOK
      | otherwise -> return eNOTDIR
fscqOpenDirectory _ "" = return eNOENT

fscqReadDirectory :: FSrunner -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fr (_:path) = do
  debugStart "READDIR" path
  ctx <- getFuseContext
  nameparts <- return $ splitDirectories path
  r <- fr $ FS.lookup_root nameparts retries
  debugMore r
  case r of
    Errno.Err e -> return $ Left $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        files <- fr $ FS.readdir dnum retries
        files_stat <- mapM (mkstat ctx) files
        return $ Right $ [(".",          dirStat ctx)
                         ,("..",         dirStat ctx)
                         ] ++ files_stat
      | otherwise -> return $ Left $ eNOTDIR
  where
    mkstat ctx (fn, (inum, isdir))
      | isdir = return $ (fn, dirStat ctx)
      | otherwise = do
        attr <- fr $ FS.file_get_attr inum retries
        return $ (fn, fileStat ctx attr)

fscqReadDirectory _ _ = return (Left (eNOENT))

fscqOpen :: FSrunner -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fr (_:path) _ _
  | path == "stats" = return $ Right 0
  | otherwise = do
  debugStart "OPEN" path
  nameparts <- return $ splitDirectories path
  r <- fr $ FS.lookup_root nameparts retries
  debugMore r
  case r of
    Errno.Err e -> return $ Left $ errnoToPosix e
    Errno.OK (inum, isdir)
      | isdir -> return $ Left eISDIR
      | otherwise -> return $ Right $ inum
fscqOpen _ _ _ _ = return $ Left eIO

splitDirsFile :: String -> ([String], String)
splitDirsFile path = (init parts, last parts)
  where parts = splitDirectories path

fscqCreate :: FSrunner -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fr (_:path) entrytype _ _ = do
  debugStart "CREATE" path
  (dirparts, filename) <- return $ splitDirsFile path
  rd <- fr $ FS.lookup_root dirparts retries
  debugMore rd
  case rd of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        r <- case entrytype of
          RegularFile -> fr $ FS.create dnum filename retries
          Socket -> fr $ FS.mksock dnum filename retries
          _ -> return $ Errno.Err Errno.EINVAL
        debugMore r
        case r of
          Errno.Err e -> return $ errnoToPosix e
          Errno.OK _ -> return eOK
      | otherwise -> return eNOTDIR
fscqCreate _ _ _ _ _ = return eOPNOTSUPP

fscqCreateDir :: FSrunner -> FilePath -> FileMode -> IO Errno
fscqCreateDir fr (_:path) _ = do
  debugStart "MKDIR" path
  (dirparts, filename) <- return $ splitDirsFile path
  rd <- fr $ FS.lookup_root dirparts retries
  debugMore rd
  case rd of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        r <- fr $ FS.mkdir dnum filename retries
        debugMore r
        case r of
          Errno.Err e -> return $ errnoToPosix e
          Errno.OK _ -> return eOK
      | otherwise -> return eNOTDIR
fscqCreateDir _ _ _ = return eOPNOTSUPP

fscqUnlink :: FSrunner -> FilePath -> IO Errno
fscqUnlink fr (_:path) = do
  debugStart "UNLINK" path
  (dirparts, filename) <- return $ splitDirsFile path
  rd <- fr $ FS.lookup_root dirparts retries
  debugMore rd
  case rd of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (dnum, isdir)
      | isdir -> do
        r <- fr $ FS.delete dnum filename retries
        debugMore r
        case r of
          Errno.OK _ -> return eOK
          Errno.Err e -> return $ errnoToPosix e
      | otherwise -> return eNOTDIR
fscqUnlink _ _ = return eOPNOTSUPP

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

fscqRead :: DiskState -> FSrunner -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead ds fr (_:path) inum byteCount offset
  | path == "stats" = do
    Stats r w s <- get_stats ds
    clear_stats ds
    statbuf <- return $ BSC8.pack $
      "Reads:  " ++ (show r) ++ "\n" ++
      "Writes: " ++ (show w) ++ "\n" ++
      "Syncs:  " ++ (show s) ++ "\n"
    return $ Right statbuf
  | otherwise = do
  debugStart "READ" (path, inum)
  wlen <- fr $ FS.file_get_sz inum retries
  len <- return $ fromIntegral $ wordToNat 64 wlen
  offset' <- return $ min offset len
  byteCount' <- return $ min byteCount $ (fromIntegral len) - (fromIntegral offset')
  pieces <- mapM read_piece $ compute_ranges offset' byteCount'
  r <- return $ BS.concat pieces
  debugMore $ BS.length r
  return $ Right r

  where
    read_piece (BR blk off count) = do
      W w <- fr $ FS.read_fblock inum blk retries
      bs <- i2bs w 4096
      return $ BS.take (fromIntegral count) $ BS.drop (fromIntegral off) bs

fscqRead _ _ [] _ _ _ = do
  return $ Left $ eIO

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

fscqWrite :: FSrunner -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite fr path inum bs offset = do
  debugStart "WRITE" (path, inum, BS.length bs)
  wlen <- fr $ FS.file_get_sz inum retries
  len <- return $ fromIntegral $ wordToNat 64 wlen
  endpos <- return $ (fromIntegral offset) + (fromIntegral (BS.length bs))
  okspc <- if len < endpos then do
    ok <- fr $ FS.file_truncate inum ((endpos + 4095) `div` 4096) retries
    return ok
  else
    return $ Errno.OK ()
  case okspc of
    Errno.OK _ -> do
      r <- foldM (write_piece len) (WriteOK 0) (compute_range_pieces offset bs)
      case r of
        WriteOK c -> do
          okspc2 <- if len < endpos then do
            ok <- fr $ FS.file_set_sz inum (W endpos) retries
            return ok
          else
            return True
          if okspc2 then
              return $ Right c
            else
              return $ Left eNOSPC
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
      W w <- if blk*blocksize < init_len then
          fr $ FS.read_fblock inum blk retries
        else
          return $ W 0
      old_bs <- i2bs w 4096
      new_bs <- return $ BS.append (BS.take (fromIntegral off) old_bs)
                       $ BS.append piece_bs
                       $ BS.drop (fromIntegral $ off + cnt) old_bs
      wnew <- bs2i new_bs
      -- _ <- fr $ FS.update_fblock_d inum blk (W wnew)
      _ <- fr $ FS.update_fblock inum blk (W wnew) retries
      return $ WriteOK (c + (fromIntegral cnt))

fscqSetFileSize :: FSrunner -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fr (_:path) size = do
  debugStart "SETSIZE" (path, size)
  nameparts <- return $ splitDirectories path
  r <- fr $ FS.lookup_root nameparts retries
  debugMore r
  case r of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (inum, isdir)
      | isdir -> return eISDIR
      | otherwise -> do
        ok <- fr $ FS.file_set_sz inum (W64 $ fromIntegral size) retries
        if ok then
          return eOK
        else
          return eIO
fscqSetFileSize _ _ _ = return eIO

fscqGetFileSystemStats :: FSrunner -> String -> IO (Either Errno FileSystemStats)
fscqGetFileSystemStats fr _ = do
  ((freeblocks, freeinodes), fsxp) <- fr $ FS.statfs
  block_bitmaps <- return $ coq_BmapNBlocks $ coq_FSXPBlockAlloc1 fsxp
  inode_bitmaps <- return $ coq_BmapNBlocks $ coq_FSXPInodeAlloc fsxp
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
fscqSetFileTimes _ _ _ = return eOK

fscqRename :: FSrunner -> FilePath -> FilePath -> IO Errno
fscqRename fr (_:src) (_:dst) = do
  debugStart "RENAME" (src, dst)
  (srcparts, srcname) <- return $ splitDirsFile src
  (dstparts, dstname) <- return $ splitDirsFile dst
  r <- fr $ FS.rename_root srcparts srcname dstparts dstname retries
  debugMore r
  case r of
    Errno.OK _ -> return eOK
    Errno.Err e -> return $ errnoToPosix e
fscqRename _ _ _ = return eIO

fscqChmod :: FilePath -> FileMode -> IO Errno
fscqChmod _ _ = do
  return eOK

fscqSyncFile :: FSrunner -> FilePath -> SyncType -> IO Errno
fscqSyncFile fr (_:path) syncType = do
  debugStart "SYNC FILE" path
  nameparts <- return $ splitDirectories path
  r <- fr $ FS.lookup_root nameparts retries
  debugMore r
  case r of
    Errno.Err e -> return $ errnoToPosix e
    Errno.OK (inum, _) -> do
      _ <- fr $ FS.file_sync inum retries
      case syncType of
        DataSync -> return eOK
        FullSync -> do
          _ <- fr $ FS.tree_sync retries
          return eOK
fscqSyncFile _ _ _ = return eIO

fscqSyncDir :: FSrunner -> FilePath -> SyncType -> IO Errno
fscqSyncDir fr (_:path) _ = do
  debugStart "SYNC DIR" path
  _ <- fr $ FS.tree_sync retries
  return eOK
fscqSyncDir _ _ _ = return eIO
