module DbenchExecute where

import           Control.Monad.State
import qualified Data.ByteString as BS
import           Data.List (elemIndices)
import qualified Data.Map.Strict as Map
import           DbenchScript
import           Foreign.C.Error
import           Fuse
import           GenericFs
import           System.Posix.Files (stdFileMode)
import           System.Posix.IO
import           System.Posix.Time

type HandlePaths = Map.Map Handle String
type HandleInums = Map.Map Handle Integer

data DbenchState =
  DbenchState { handlePaths :: HandlePaths
              , handleInums :: HandleInums }

addHandle :: Handle -> String -> StateT DbenchState IO ()
addHandle h p = modify' (\s -> s{handlePaths=Map.insert h p (handlePaths s)})

addInum :: Handle -> Integer -> StateT DbenchState IO ()
addInum h inum = modify' (\s -> s{handleInums=Map.insert h inum (handleInums s)})

getFilePath :: Handle -> StateT DbenchState IO String
getFilePath h = do
  mp <- gets (Map.lookup h . handlePaths)
  case mp of
    Just p -> return p
    Nothing -> liftIO $ ioError (userError $ "unknown handle " ++ show h)

getFile :: FuseOperations Integer -> Handle -> StateT DbenchState IO (String, Integer)
getFile fs h = do
  p <- getFilePath h
  mh <- gets (Map.lookup h . handleInums)
  case mh of
    Just inum -> return (p, inum)
    Nothing -> do
      r <- liftIO $ fuseOpen fs p ReadOnly defaultFileFlags
      case r of
        Left e -> liftIO $ ioError (errnoToIOError "" e Nothing Nothing)
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
expectStatus s                  (Right _) = liftIO $ ioError (userError $ "expected failure " ++ show s)

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

runCommand :: FuseOperations Integer -> Command -> StateT DbenchState IO ()
runCommand fs c = run c
  where run :: Command -> StateT DbenchState IO ()
        run (CreateX (Path p) createOptions _createDisposition h _s) = do
          addHandle h p
          liftIO $ if hasFileDirectoryFile createOptions then
            void $ fuseCreateDirectory fs p stdFileMode
          else
            void $ fuseCreateFile fs p stdFileMode ReadWrite defaultFileFlags
          return ()
        run (ReadX h off len _expectedLen _s) = do
          (p, inum) <- getFile fs h
          -- TODO: check read size
          _ <- liftIO $ fuseRead fs p inum (fromIntegral len) (fromIntegral off)
          return ()
        run (WriteX h off len _expectedLen _s) = do
          (p, inum) <- getFile fs h
          -- TODO: check written bytes
          _ <- liftIO $ fuseWrite fs p inum (BS.pack (replicate len 0)) (fromIntegral off)
          return ()
        run (Close _h _s) = return ()
        run (QueryPath (Path p) _ _s) = do
          _ <- liftIO $ fuseOpen fs p ReadOnly defaultFileFlags
          return ()
        run (QueryFile h _level _s) = do
          p <- getFilePath h
          _ <- liftIO $ fuseGetFileStat fs p
          return ()
        run (Unlink (Path p) _level _s) = do
          _ <- liftIO $ fuseRemoveLink fs p
          return ()
        run (FindFirst p0 _level _maxcount _count _s) =
          let p = removeLastComponent p0 in liftIO $ do
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
        run (Flush h _s) = do
          (p, inum) <- getFile fs h
          _ <- liftIO $ fuseSynchronizeFile fs p inum FullSync
          return ()
        run (Rename (Path p1) (Path p2) _s) = do
          _ <- liftIO $ fuseRename fs p1 p2
          return ()
        run (LockX _h _off _level _s) = return ()
        run (UnlockX _h _off _level _s) = return ()
        run (Mkdir (Path p) _s) = do
          _ <- liftIO $ fuseCreateDirectory fs p stdFileMode
          return ()
        run (Deltree (Path p) _s) = do
          _ <- liftIO $ delTree fs p
          return ()
        run (QueryFilesystem _level _s) = do
          _ <- liftIO $ fuseGetFileSystemStats fs "/"
          return ()

runScript :: FuseOperations Integer -> Script -> IO ()
runScript fs s = evalStateT (mapM_ (runCommand fs) s) (DbenchState Map.empty Map.empty)

runScriptWithRoot :: FuseOperations Integer -> String -> Script -> IO ()
runScriptWithRoot fs root s =
  evalStateT
  (mapM_ (runCommand fs . prefixPaths root) s)
  (DbenchState Map.empty Map.empty)
