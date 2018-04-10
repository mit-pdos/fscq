{-# LANGUAGE ScopedTypeVariables #-}
module DbenchExecute where

import           Control.Monad.State
import qualified Data.ByteString as BS
import           Data.List (elemIndices)
import qualified Data.Map.Strict as Map
import           DbenchScript
import           Foreign.C.Error
import           Fuse
import           GenericFs
import           System.Posix.Files (unionFileModes, stdFileMode, ownerExecuteMode)
import           System.Posix.IO
import           System.Posix.Time

type HandlePaths = Map.Map Handle String
type HandleInums fh = Map.Map Handle fh

data DbenchState fh =
  DbenchState { handlePaths :: HandlePaths
              , handleInums :: HandleInums fh }

addHandle :: Handle -> String -> StateT (DbenchState fh) IO ()
addHandle h p = modify' (\s -> s{handlePaths=Map.insert h p (handlePaths s)})

addInum :: Handle -> fh -> StateT (DbenchState fh) IO ()
addInum h inum = modify' (\s -> s{handleInums=Map.insert h inum (handleInums s)})

getFilePath :: Handle -> StateT (DbenchState fh) IO String
getFilePath h = do
  mp <- gets (Map.lookup h . handlePaths)
  case mp of
    Just p -> return p
    Nothing -> liftIO $ ioError (userError $ "unknown handle " ++ show h)

tryGetFile :: Handle -> StateT (DbenchState fh) IO (Maybe (String, fh))
tryGetFile h = do
  p <- getFilePath h
  mh <- gets (Map.lookup h . handleInums)
  return $ case mh of
             Nothing -> Nothing
             Just inum -> Just (p,inum)

getFile :: FuseOperations fh -> Handle -> StateT (DbenchState fh) IO (String, fh)
getFile fs h = do
  p <- getFilePath h
  mh <- gets (Map.lookup h . handleInums)
  case mh of
    Just inum -> return (p, inum)
    Nothing -> do
      r <- liftIO $ fuseOpen fs p ReadWrite defaultFileFlags
      case r of
        Left e -> liftIO $ ioError (errnoToIOError p e Nothing Nothing)
        Right inum -> do
          addInum h inum
          return (p, inum)

expectStatus :: MonadIO m => ExpectedStatus -> Either Errno a -> m ()
expectStatus StatusOk           (Right _) = return ()
-- TODO: check that the error number is correct
expectStatus StatusNameNotFound (Left _) = return ()
expectStatus StatusPathNotFound (Left _) = return ()
expectStatus StatusNoSuchFile   (Left _) = return ()
expectStatus StatusOk           (Left e) = liftIO $ ioError (errnoToIOError "" e Nothing Nothing)
expectStatus s                  (Right _) = error $ "expected failure " ++ show s

removeLastComponent :: Pattern -> String
removeLastComponent (Pattern p) =
  let slashIndices = elemIndices '/' p in
    case slashIndices of
      [] -> p
      _ -> take (last slashIndices) p

prefixPaths :: String -> Command -> Command
prefixPaths prefix c = addPrefix c where
  pre (Path p) = Path (prefix ++ p)
  addPrefix (CreateX p opts disp h s) = CreateX (pre p) opts disp h s
  addPrefix (QueryPath p level s) = QueryPath (pre p) level s
  addPrefix (Unlink p level s) = Unlink (pre p) level s
  addPrefix (FindFirst (Pattern p) level maxcount count s) =
    FindFirst (Pattern (prefix ++ p)) level maxcount count s
  addPrefix (Rename p1 p2 s) = Rename (pre p1) (pre p2) s
  addPrefix (Mkdir p s) = Mkdir (pre p) s
  addPrefix (Deltree p s) = Deltree (pre p) s
  addPrefix c = c

largeBytestring :: BS.ByteString
largeBytestring = BS.pack (replicate 65536 0)

smallBytestring :: BS.ByteString
smallBytestring = BS.singleton 1

zeroBytestring :: Int -> BS.ByteString
zeroBytestring len
  | len == 65526 = largeBytestring
  | len == 1 = smallBytestring
  | len <= 65536 = BS.take len largeBytestring
  | otherwise = BS.pack (replicate len 0)

createXDirectory :: forall fh. FuseOperations fh -> String -> IO ()
createXDirectory fs p =
  void $ fuseCreateDirectory fs p (unionFileModes stdFileMode ownerExecuteMode)

createXFile :: forall fh. FuseOperations fh -> String -> CreateDisposition -> IO ()
createXFile fs p createDisposition = do
  when (isOverwriteFile createDisposition) (void $ fuseRemoveLink fs p)
  inum <- getResult p =<< fuseCreateFile fs p stdFileMode ReadWrite defaultFileFlags
  closeFile fs p inum
  return ()

runCommand :: forall fh. FuseOperations fh -> Command -> StateT (DbenchState fh) IO ()
runCommand fs c = run c
  where run :: Command -> StateT (DbenchState fh) IO ()
        run (CreateX (Path p) createOptions createDisposition h _s) = {-# SCC "createx" #-} do
          addHandle h p
          when (isCreate createDisposition || isOverwriteFile createDisposition) $
            liftIO $ if hasFileDirectoryFile createOptions then
                       createXDirectory fs p
                     else createXFile fs p createDisposition
        run (ReadX h off len _expectedLen _s) = {-# SCC "readx" #-}do
          (p, inum) <- getFile fs h
          -- TODO: check read size
          _ <- liftIO $ fuseRead fs p inum (fromIntegral len) (fromIntegral off)
          return ()
        run (WriteX h off len _expectedLen _s) = {-# SCC "writex" #-} do
          (p, inum) <- getFile fs h
          -- TODO: check written bytes
          _ <- liftIO $ fuseWrite fs p inum (zeroBytestring len) (fromIntegral off)
          return ()
        run (Close h _s) = {-# SCC "close" #-} do
          mInum <- tryGetFile h
          case mInum of
            Nothing -> return ()
            Just (p,inum) -> liftIO $ closeFile fs p inum
        run (QueryPath (Path p) _ _s) = {-# SCC "querypath" #-} do
          _ <- liftIO $ fuseGetFileStat fs p
          return ()
        run (QueryFile h _level _s) = {-# SCC "queryfile" #-} do
          p <- getFilePath h
          _ <- liftIO $ fuseGetFileStat fs p
          return ()
        run (Unlink (Path p) _level _s) = do
          _ <- liftIO $ fuseRemoveLink fs p
          return ()
        run (FindFirst p0 _level _maxcount _count _s) =
          let p = removeLastComponent p0 in liftIO $ {-# SCC "findfirst" #-} do
          r <- fuseOpenDirectory fs p
          case r of
            Left _ -> return ()
            Right dir -> do
              _ <- fuseReadDirectory fs p dir
              return ()
        run (SetFileInfo h _level _s) = do
          p <- getFilePath h
          liftIO $ do
            t <- epochTime
            _ <- fuseSetFileTimes fs p t t
            return ()
        run (Flush h _s) = {-# SCC "flush" #-} do
          (p, inum) <- getFile fs h
          _ <- liftIO $ fuseSynchronizeFile fs p inum FullSync
          return ()
        run (Rename (Path p1) (Path p2) _s) = do
          _ <- liftIO $ fuseRename fs p1 p2
          return ()
        run (LockX _h _off _level _s) = return ()
        run (UnlockX _h _off _level _s) = return ()
        run (Mkdir (Path p) _s) = do
          liftIO $ checkError p $ fuseCreateDirectory fs p (unionFileModes stdFileMode ownerExecuteMode)
          return ()
        run (Deltree (Path p) _s) = do
          _ <- liftIO $ delTree fs p
          return ()
        run (QueryFilesystem _level _s) = do
          _ <- liftIO $ fuseGetFileSystemStats fs "/"
          return ()

runScript :: FuseOperations fh -> Script -> IO ()
runScript fs s = evalStateT (mapM_ (runCommand fs) s) (DbenchState Map.empty Map.empty)

prefixScript :: String -> Script -> Script
prefixScript root = map (prefixPaths root)
