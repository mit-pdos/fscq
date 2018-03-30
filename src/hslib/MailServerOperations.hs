{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module MailServerOperations
  ( Config(..)
  , configFlags
  , randomOps
  , cleanup
  ) where

import Control.Concurrent (threadDelay)
import Control.Monad (when)
import Control.Monad.Reader
import Data.IORef
import Options
import System.Random

import System.FilePath.Posix
import System.Posix.Files (ownerModes)
import System.Posix.IO (defaultFileFlags)

import GenericFs
import Fuse

data Config = Config
  { readPerc :: Double
  , waitTimeMicros :: Int
  , mailboxDir :: FilePath }

instance Options Config where
  defineOptions = pure Config
    <*> simpleOption "read-perc" 0.5
        "fraction of operations that should be reads"
    <*> simpleOption "wait-micros" 0
        "time to wait between operations (in microseconds)"
    <*> simpleOption "dir" "/mailboxes"
        "(initially empty) directory to store user mailboxes"

configFlags :: Config -> [String]
configFlags Config{..} =
  [ "--read-perc", show readPerc
  , "--wait-micros", show waitTimeMicros
  , "--dir", mailboxDir ]

type AppPure a = forall m. Monad m => ReaderT Config m a
type App a = ReaderT Config IO a

type User = Int

userDir :: User -> AppPure FilePath
userDir uid = do
  mailDir <- reader mailboxDir
  return $ joinPath [mailDir, "user" ++ show uid]

data UserState = UserState
  { lastMessage :: IORef Int
  , lastRead :: IORef Int }

initUser :: Filesystem fh -> Int -> App UserState
initUser Filesystem{fuseOps=fs} uid = do
  dir <- userDir uid
  liftIO $ do
    checkError dir $ fuseCreateDirectory fs dir ownerModes
    pure UserState <*> newIORef 0 <*> newIORef 0

getFreshMessage :: UserState -> IO Int
getFreshMessage s = do
  m <- readIORef $ lastMessage s
  modifyIORef' (lastMessage s) (+1)
  return m

mailDeliver :: Filesystem fh -> UserState -> User -> App ()
mailDeliver fs s uid = userDir uid >>= \d -> liftIO $ do
  m <- getFreshMessage s
  let p = joinPath [d, show m]
  inum <- createSmallFile fs p
  closeFile (fuseOps fs) p inum
  return ()

readMessage :: Filesystem fh -> FilePath -> IO ()
readMessage Filesystem{fuseOps=fs} p = do
  fh <- getResult p =<< fuseOpen fs p ReadOnly defaultFileFlags
  fileSize <- getFileSize fs p
  forM_ [0,4096..fileSize] $ \off ->
    fuseRead fs p fh 4096 off
  fuseRelease fs p fh

getLastRead :: UserState -> IO Int
getLastRead = readIORef . lastRead

updateLastRead :: UserState -> Int -> IO ()
updateLastRead s = writeIORef (lastRead s)

mailRead :: Filesystem fh -> UserState -> User -> App ()
mailRead fs@Filesystem{fuseOps} s uid = userDir uid >>= \d -> liftIO $ do
  dnum <- getResult d =<< fuseOpenDirectory fuseOps d
  allEntries <- getResult d =<< fuseReadDirectory fuseOps d dnum
  lastId <- getLastRead s
  forM_ allEntries $ \(p, _) -> do
    let fname = takeFileName p
    let mId = read fname
    when ( fname /= "." && fname /= ".." && mId > lastId) $ do
      readMessage fs $ joinPath [d, p]
      updateLastRead s mId
  fuseRelease fuseOps d dnum

randomDecisions :: Double -> IO [Bool]
randomDecisions percTrue = do
  gen <- newStdGen
  let nums = randomRs (0, 1.0) gen
  return $ map (< percTrue) nums

doRandomOps :: Filesystem fh -> User -> Int -> App ()
doRandomOps fs uid iters = do
  s <- initUser fs uid
  Config{..} <- ask
  isReads <- liftIO $ randomDecisions readPerc
  forM_ (take iters isReads) $ \isRead -> do
    if isRead then mailRead fs s uid else mailDeliver fs s uid
    liftIO $ threadDelay waitTimeMicros

emptyMailboxes :: Filesystem fh -> App ()
emptyMailboxes Filesystem{fuseOps=fs} = reader mailboxDir >>= \dir -> liftIO $ do
  dnum <- getResult dir =<< fuseOpenDirectory fs dir
  allEntries <- getResult dir =<< fuseReadDirectory fs dir dnum
  let entries = filterDots allEntries
      names = map fst entries
  forM_ names $ \n ->
    delTree fs (dir `pathJoin` n)
  _ <- fuseSynchronizeDirectory fs dir dnum FullSync
  closeFile fs dir dnum

randomOps :: Config -> Filesystem fh -> Int -> User -> IO ()
randomOps c fs iters uid = runReaderT (doRandomOps fs uid iters) c

cleanup :: Config -> Filesystem fh -> IO ()
cleanup c fs = runReaderT (emptyMailboxes fs) c
