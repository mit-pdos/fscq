{-# LANGUAGE RankNTypes, MagicHash #-}

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
import qualified Errno
import Data.IORef
import Interpreter as I
import qualified FS
import qualified Log
import ByteFile
import FSLayout
import qualified DirName
import System.Environment
import Inode
import Control.Concurrent.MVar
import Data.Word
import Text.Printf
import qualified System.Process
import qualified Data.List

-- Handle type for open files; we will use the inode number
type HT = Coq_word

verboseFuse :: Bool
verboseFuse = False

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
nDataBitmaps :: Coq_word
nDataBitmaps = W64 1
nInodeBitmaps :: Coq_word
nInodeBitmaps = W64 1

type MSCS = Log.Coq_memstate_cachestate
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
  args <- getArgs
  case args of
    fn:rest -> run_fuse fn rest
    _ -> putStrLn $ "Usage: fuse disk -f /tmp/ft"

run_fuse :: String -> [String] -> IO()
run_fuse disk_fn fuse_args = do
  fileExists <- System.Directory.doesFileExist disk_fn
  ds <- case disk_fn of
    "/tmp/crashlog.img" -> init_disk_crashlog disk_fn
    _ -> init_disk disk_fn
  (s, fsxp) <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      (s, (fsxp, ())) <- I.run ds $ FS.recover
      return (s, fsxp)
  else
    do
      putStrLn $ "Initializing file system"
      res <- I.run ds $ FS.mkfs nDataBitmaps nInodeBitmaps
      case res of
        Errno.Err _ -> error $ "mkfs failed"
        Errno.OK (s, (fsxp, ())) -> do
          set_nblocks_disk ds $ wordToNat 64 $ coq_FSXPMaxBlock fsxp
          return (s, fsxp)
  putStrLn $ "Starting file system, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
  ref <- newIORef s
  m_fsxp <- newMVar fsxp
  fuseRun "fscq" fuse_args (fscqFSOps disk_fn ds (doFScall ds ref) m_fsxp) defaultExceptionHandler

-- See the HFuse API docs at:
-- https://hackage.haskell.org/package/HFuse-0.2.1/docs/System-Fuse.html
fscqFSOps :: String -> DiskState -> FSrunner -> MVar Coq_fs_xparams -> FuseOperations HT
fscqFSOps fn ds fr m_fsxp = defaultFuseOps
  { fuseGetFileStat = fscqGetFileStat fr m_fsxp
  , fuseOpen = fscqOpen fr m_fsxp
  , fuseCreateDevice = fscqCreate fr m_fsxp
  , fuseCreateDirectory = fscqCreateDir fr m_fsxp
  , fuseRemoveLink = fscqUnlink fr m_fsxp
  , fuseRemoveDirectory = fscqUnlink fr m_fsxp
  , fuseRead = fscqRead ds fr m_fsxp
  , fuseWrite = fscqWrite fr m_fsxp
  , fuseSetFileSize = fscqSetFileSize fr m_fsxp
  , fuseOpenDirectory = fscqOpenDirectory fr m_fsxp
  , fuseReadDirectory = fscqReadDirectory fr m_fsxp
  , fuseGetFileSystemStats = fscqGetFileSystemStats fr m_fsxp
  , fuseDestroy = fscqDestroy ds fn
  , fuseSetFileTimes = fscqSetFileTimes
  , fuseRename = fscqRename fr m_fsxp
  , fuseSetFileMode = fscqChmod
  }

applyFlushgroup :: DiskState -> [(Word64, Coq_word)] -> IO ()
applyFlushgroup _ [] = return ()
applyFlushgroup ds ((a, v) : rest) = do
  applyFlushgroup ds rest
  write_disk ds (W64 a) v

applyFlushgroups :: DiskState -> [[(Word64, Coq_word)]] -> IO ()
applyFlushgroups _ [] = return ()
applyFlushgroups ds (flushgroup : rest) = do
  applyFlushgroups ds rest
  applyFlushgroup ds flushgroup

materializeFlushgroups :: IORef Integer -> [[(Word64, Coq_word)]] -> IO ()
materializeFlushgroups idxref groups = do
  idx <- readIORef idxref
  writeIORef idxref (idx+1)
  _ <- System.Process.system $ printf "cp --sparse=always /tmp/crashlog.img /tmp/crashlog-%06d.img" idx
  ds <- init_disk $ printf "/tmp/crashlog-%06d.img" idx
  applyFlushgroups ds groups

writeSubsets' :: [[(Word64, a)]] -> [[(Word64, a)]]
writeSubsets' [] = [[]]
writeSubsets' (heads : tails) =
    tailsubsets ++ (concat $ map (\ts -> map (\hd -> hd : ts) heads) tailsubsets)
  where
    tailsubsets = writeSubsets' tails

writeSubsets :: [(Word64, a)] -> [[(Word64, a)]]
writeSubsets writes = writeSubsets' addrWrites
  where
    addrWrites = Data.List.groupBy sameaddr writes
    sameaddr (x, _) (y, _) = (x == y)

materializeCrashes :: IORef Integer -> [[(Word64, Coq_word)]] -> IO ()
materializeCrashes idxref [] = materializeFlushgroups idxref []
materializeCrashes idxref (lastgroup : othergroups) = do
  materializeCrashes idxref othergroups
  mapM_ (\lastsubset -> materializeFlushgroups idxref (lastsubset : othergroups)) $ writeSubsets lastgroup

fscqDestroy :: DiskState -> String -> IO ()
fscqDestroy ds disk_fn = do
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
  case t of
    0 -> RegularFile
    1 -> Socket
    2 -> NamedPipe
    3 -> BlockSpecial
    4 -> CharacterSpecial
    _ -> Unknown
  where t = wordToNat 32 $ _INODE__coq_IType attr

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
  , statSpecialDeviceID = fromIntegral $ wordToNat 64 $ _INODE__coq_IDev attr
  , statFileSize = fromIntegral $ wordToNat 64 $ _INODE__coq_ISize attr
  , statBlocks = 1
  , statAccessTime = 0
  , statModificationTime = fromIntegral $ wordToNat 32 $ _INODE__coq_IMTime attr
  , statStatusChangeTime = 0
  }

fscqGetFileStat :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> IO (Either Errno FileStat)
fscqGetFileStat fr m_fsxp (_:path)
  | path == "stats" = do
    ctx <- getFuseContext
    return $ Right $ fileStat ctx (INODE__Build_iattr (W 1024) (W 0) (W 0) (W 0))
  | otherwise = withMVar m_fsxp $ \fsxp -> do
  debugStart "STAT" path
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  debugMore r
  case r of
    Nothing -> return $ Left eNOENT
    Just (inum, isdir)
      | isdir -> do
        ctx <- getFuseContext
        return $ Right $ dirStat ctx
      | otherwise -> do
        (attr, ()) <- fr $ FS.file_get_attr fsxp inum
        ctx <- getFuseContext
        return $ Right $ fileStat ctx attr
fscqGetFileStat _ _ _ = return $ Left eNOENT

fscqOpenDirectory :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> IO Errno
fscqOpenDirectory fr m_fsxp (_:path) = withMVar m_fsxp $ \fsxp -> do
  debugStart "OPENDIR" path
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  debugMore r
  case r of
    Nothing -> return eNOENT
    Just (_, isdir)
      | isdir -> return eOK
      | otherwise -> return eNOTDIR
fscqOpenDirectory _ _ "" = return eNOENT

fscqReadDirectory :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> IO (Either Errno [(FilePath, FileStat)])
fscqReadDirectory fr m_fsxp (_:path) = withMVar m_fsxp $ \fsxp -> do
  debugStart "READDIR" path
  ctx <- getFuseContext
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  debugMore r
  case r of
    Nothing -> return $ Left $ eNOENT
    Just (dnum, isdir)
      | isdir -> do
        (files, ()) <- fr $ FS.readdir fsxp dnum
        files_stat <- mapM (mkstat fsxp ctx) files
        return $ Right $ [(".",          dirStat ctx)
                         ,("..",         dirStat ctx)
                         ] ++ files_stat
      | otherwise -> return $ Left $ eNOTDIR
  where
    mkstat fsxp ctx (fn, (inum, isdir))
      | isdir = return $ (fn, dirStat ctx)
      | otherwise = do
        (attr, ()) <- fr $ FS.file_get_attr fsxp inum
        return $ (fn, fileStat ctx attr)

fscqReadDirectory _ _ _ = return (Left (eNOENT))

fscqOpen :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> OpenMode -> OpenFileFlags -> IO (Either Errno HT)
fscqOpen fr m_fsxp (_:path) _ _
  | path == "stats" = return $ Right $ W 0
  | otherwise = withMVar m_fsxp $ \fsxp -> do
  debugStart "OPEN" path
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  debugMore r
  case r of
    Nothing -> return $ Left eNOENT
    Just (inum, isdir)
      | isdir -> return $ Left eISDIR
      | otherwise -> return $ Right $ inum
fscqOpen _ _ _ _ _ = return $ Left eIO

splitDirsFile :: String -> ([String], String)
splitDirsFile path = (init parts, last parts)
  where parts = splitDirectories path

fscqCreate :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> EntryType -> FileMode -> DeviceID -> IO Errno
fscqCreate fr m_fsxp (_:path) entrytype _ dev = withMVar m_fsxp $ \fsxp -> do
  debugStart "CREATE" path
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dirparts
  debugMore rd
  case rd of
    Nothing -> return eNOENT
    Just (dnum, isdir)
      | isdir -> do
        (r, ()) <- case entrytype of
          RegularFile -> fr $ FS.create fsxp dnum filename
          Socket -> fr $ FS.mkdev fsxp dnum filename (W 1) (W 0)
          NamedPipe -> fr $ FS.mkdev fsxp dnum filename (W 2) (W 0)
          BlockSpecial -> fr $ FS.mkdev fsxp dnum filename (W 3) (W $ fromIntegral dev)
          CharacterSpecial -> fr $ FS.mkdev fsxp dnum filename (W 4) (W $ fromIntegral dev)
          _ -> return (Nothing, ())
        debugMore r
        case r of
          Nothing -> return eIO
          Just _ -> return eOK
      | otherwise -> return eNOTDIR
fscqCreate _ _ _ _ _ _ = return eOPNOTSUPP

fscqCreateDir :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> FileMode -> IO Errno
fscqCreateDir fr m_fsxp (_:path) _ = withMVar m_fsxp $ \fsxp -> do
  debugStart "MKDIR" path
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dirparts
  debugMore rd
  case rd of
    Nothing -> return eNOENT
    Just (dnum, isdir)
      | isdir -> do
        (r, ()) <- fr $ FS.mkdir fsxp dnum filename
        debugMore r
        case r of
          Nothing -> return eIO
          Just _ -> return eOK
      | otherwise -> return eNOTDIR
fscqCreateDir _ _ _ _ = return eOPNOTSUPP

fscqUnlink :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> IO Errno
fscqUnlink fr m_fsxp (_:path) = withMVar m_fsxp $ \fsxp -> do
  debugStart "UNLINK" path
  (dirparts, filename) <- return $ splitDirsFile path
  (rd, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) dirparts
  debugMore rd
  case rd of
    Nothing -> return eNOENT
    Just (dnum, isdir)
      | isdir -> do
        (r, ()) <- fr $ FS.delete fsxp dnum filename
        debugMore r
        case r of
          True -> return eOK
          False -> return eIO
      | otherwise -> return eNOTDIR
fscqUnlink _ _ _ = return eOPNOTSUPP

-- Wrappers for converting Coq_word to/from ByteString, with
-- the help of i2buf and buf2i from hslib/Disk.
blocksize :: Int
blocksize = _Valulen__valulen `div` 8

bs2i :: BS.ByteString -> IO Integer
bs2i (BSI.PS fp 0 len) = withForeignPtr fp $ buf2i $ fromIntegral len
bs2i (BSI.PS _ _ _) = error "Non-zero offset not implemented"

-- We should audit our use of [Int] vs [Word] vs [Foreign.C.Types.CSize]
-- for possible overflows, etc..  These are possibly hiding in our uses
-- of [fromIntegral].
i2bs :: Integer -> Int -> IO BS.ByteString
i2bs i nbytes = BSI.create nbytes $ i2buf i $ fromIntegral nbytes

fscqRead :: DiskState -> FSrunner -> MVar Coq_fs_xparams -> FilePath -> HT -> ByteCount -> FileOffset -> IO (Either Errno BS.ByteString)
fscqRead ds fr m_fsxp (_:path) inum byteCount offset
  | path == "stats" = do
    Stats r w s <- get_stats ds
    clear_stats ds
    statbuf <- return $ BSC8.pack $
      "Reads:  " ++ (show r) ++ "\n" ++
      "Writes: " ++ (show w) ++ "\n" ++
      "Syncs:  " ++ (show s) ++ "\n"
    return $ Right statbuf
  | otherwise = withMVar m_fsxp $ \fsxp -> do
  off <- return $ fromIntegral offset
  len <- return $ fromIntegral byteCount
  debugStart "READ" (path, inum, len)
  (buf, ()) <- fr $ FS.read_bytes fsxp inum off len
  BYTEFILE__Coq_len_bytes readlen (W w) <- return buf
  wdata <- i2bs w readlen
  return $ Right wdata

fscqRead _ _ _ [] _ _ _ = do
  return $ Left $ eIO

fscqWrite :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> HT -> BS.ByteString -> FileOffset -> IO (Either Errno ByteCount)
fscqWrite fr m_fsxp path inum bs offset = withMVar m_fsxp $ \fsxp -> do
  debugStart "WRITE" (path, inum)
  off <- return $ fromIntegral offset
  len <- return $ BS.length bs
  wnew <- bs2i bs
  (ok, ()) <- fr $ FS.append fsxp inum off len (W wnew)
  if ok then
    return $ Right (fromIntegral len)
  else
    return $ Left eIO

fscqSetFileSize :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> FileOffset -> IO Errno
fscqSetFileSize fr m_fsxp (_:path) size = withMVar m_fsxp $ \fsxp -> do
  debugStart "SETSIZE" (path, size)
  nameparts <- return $ splitDirectories path
  (r, ()) <- fr $ FS.lookup fsxp (coq_FSXPRootInum fsxp) nameparts
  debugMore r
  case r of
    Nothing -> return eNOENT
    Just (inum, isdir)
      | isdir -> return eISDIR
      | otherwise -> do
        (ok, ()) <- fr $ FS.file_resize fsxp inum (fromIntegral size)
        if ok then
          return eOK
        else
          return eIO
fscqSetFileSize _ _ _ _ = return eIO

fscqGetFileSystemStats :: FSrunner -> MVar Coq_fs_xparams -> String -> IO (Either Errno FileSystemStats)
fscqGetFileSystemStats fr m_fsxp _ = withMVar m_fsxp $ \fsxp -> do
  (freeblocks, (freeinodes, ())) <- fr $ FS.statfs fsxp
  block_bitmaps <- return $ coq_BmapNBlocks $ coq_FSXPBlockAlloc fsxp
  inode_bitmaps <- return $ coq_BmapNBlocks $ coq_FSXPInodeAlloc fsxp
  return $ Right $ FileSystemStats
    { fsStatBlockSize = 4096
    , fsStatBlockCount = 8 * 4096 * (fromIntegral $ wordToNat 64 block_bitmaps)
    , fsStatBlocksFree = fromIntegral $ wordToNat 64 freeblocks
    , fsStatBlocksAvailable = fromIntegral $ wordToNat 64 freeblocks
    , fsStatFileCount = 8 * 4096 * (fromIntegral $ wordToNat 64 inode_bitmaps)
    , fsStatFilesFree = fromIntegral $ wordToNat 64 freeinodes
    , fsStatMaxNameLength = fromIntegral DirName._SDIR__namelen
    }

fscqSetFileTimes :: FilePath -> EpochTime -> EpochTime -> IO Errno
fscqSetFileTimes _ _ _ = do
  return eOK

fscqRename :: FSrunner -> MVar Coq_fs_xparams -> FilePath -> FilePath -> IO Errno
fscqRename fr m_fsxp (_:src) (_:dst) = withMVar m_fsxp $ \fsxp -> do
  debugStart "RENAME" (src, dst)
  (srcparts, srcname) <- return $ splitDirsFile src
  (dstparts, dstname) <- return $ splitDirsFile dst
  (r, ()) <- fr $ FS.rename fsxp (coq_FSXPRootInum fsxp) srcparts srcname dstparts dstname
  debugMore r
  case r of
    True -> return eOK
    False -> return eIO
fscqRename _ _ _ _ = return eIO

fscqChmod :: FilePath -> FileMode -> IO Errno
fscqChmod _ _ = do
  return eOK
