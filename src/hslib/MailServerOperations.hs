{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
module MailServerOperations
  ( Config(..)
  , configFlags
  , randomOps
  , initializeMailboxes
  , cleanupMailboxes
  ) where

import           Control.Concurrent (threadDelay)
import           Control.Monad (when, unless, void)
import           Control.Monad.Reader
import           Data.IORef
import qualified Data.Set as Set
import           Options
import           System.Random

import           System.FilePath.Posix
import           System.Posix.Files (ownerModes)
import           System.Posix.IO (defaultFileFlags)

import           GenericFs
import           Fuse

data Config = Config
  { readPerc :: Double
  , alwaysReadMessages :: Int
  , waitTimeMicros :: Int
  , mailboxDir :: FilePath }

instance Options Config where
  defineOptions = pure Config
    <*> simpleOption "read-perc" 0.5
        "fraction of operations that should be reads"
    <*> simpleOption "read-last" 0
        "number of recent messages to always read"
    <*> simpleOption "wait-micros" 0
        "time to wait between operations (in microseconds)"
    <*> simpleOption "dir" "/mailboxes"
        "(initially empty) directory to store user mailboxes"

configFlags :: Config -> [String]
configFlags Config{..} =
  [ "--read-perc", show readPerc
  , "--read-last", show alwaysReadMessages
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
  , readIds :: IORef (Set.Set String) }

initUser :: Filesystem fh -> Int -> App UserState
initUser Filesystem{fuseOps=fs} uid = do
  dir <- userDir uid
  liftIO $ do
    _ <- fuseCreateDirectory fs dir ownerModes
    pure UserState <*> newIORef 0 <*> newIORef Set.empty

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

getHaveRead :: UserState -> String -> IO Bool
getHaveRead s mId = Set.member mId <$> readIORef (readIds s)

updateRead :: UserState -> String -> IO ()
updateRead s mId = modifyIORef' (readIds s) (Set.insert mId)

mailRead :: Filesystem fh -> UserState -> User -> App ()
mailRead fs@Filesystem{fuseOps} s uid = do
  d <- userDir uid
  Config{alwaysReadMessages} <- ask
  liftIO $ do
    dnum <- getResult d =<< fuseOpenDirectory fuseOps d
    allEntries <- getResult d =<< fuseReadDirectory fuseOps d dnum
    forM_ (zip [1..] allEntries) $ \(index, (p, _)) -> do
      let fname = takeFileName p
      when ( fname /= "." && fname /= ".." ) $ do
        haveRead <- if index < alwaysReadMessages
          then return False
          else getHaveRead s fname
        unless haveRead $ do
          readMessage fs $ joinPath [d, p]
          updateRead s fname
    fuseRelease fuseOps d dnum

randomDecisions :: Double -> IO [Bool]
randomDecisions percTrue = do
  gen <- newStdGen
  let nums = randomRs (0, 1.0) gen
  return $ map (< percTrue) nums

doRandomOps :: Filesystem fh -> User -> Int -> App UserState
doRandomOps fs uid iters = do
  s <- initUser fs uid
  Config{..} <- ask
  isReads <- liftIO $ randomDecisions readPerc
  forM_ (take iters isReads) $ \isRead -> do
    if isRead then mailRead fs s uid else mailDeliver fs s uid
    liftIO $ threadDelay waitTimeMicros
  return s

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

initializeMailboxes_ :: Filesystem fh -> Int -> Int -> App ()
initializeMailboxes_ fs numUsers numMessages = forM_ [0..numUsers-1] $ \uid ->
  local (\c -> c{readPerc=0.0}) $ do
    c <- doRandomOps fs uid numMessages
    mailRead fs c uid
    -- TODO: should pass the user state on to randomOps so that subsequent
    -- deliver operations work

initializeMailboxes :: Config -> Filesystem fh -> Int -> Int -> IO ()
initializeMailboxes c fs numUsers numMessages =
  runReaderT (initializeMailboxes_ fs numUsers numMessages) c

randomOps :: Config -> Filesystem fh -> Int -> User -> IO ()
randomOps c fs iters uid =
  runReaderT (void $ doRandomOps fs uid iters) c

cleanupMailboxes :: Config -> Filesystem fh -> IO ()
cleanupMailboxes c fs = runReaderT (emptyMailboxes fs) c
