{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Control.Concurrent
import Control.Monad
import Control.Monad (void)
import Data.List (intercalate, dropWhileEnd)
import Options
import System.Clock
import System.Exit

import Fuse
import FscqFs
import CfscqFs
import GenericFs
import System.Posix.IO (defaultFileFlags)
import GHC.RTS.Flags

data NoOptions = NoOptions {}
instance Options NoOptions where
  defineOptions = pure NoOptions

statOp :: NoOptions -> Filesystem -> IO ()
statOp _ fs = do
    _ <- fuseOpen fs "/" ReadOnly defaultFileFlags
    _ <- fuseGetFileStat fs "/"
    _ <- fuseOpen fs "/dir1" ReadOnly defaultFileFlags
    _ <- fuseGetFileStat fs "/dir1"
    _ <- fuseGetFileStat fs "/dir1/file1"
    return ()

statfsOp :: NoOptions -> Filesystem -> IO ()
statfsOp _ fs = void $ fuseGetFileSystemStats fs "/"

data ScanDirOptions =
  ScanDirOptions { optScanRoot :: String }
instance Options ScanDirOptions where
  defineOptions = pure ScanDirOptions <*>
    simpleOption "dir" "/"
      "root directory to scan from"

getResult :: String -> Either Errno a -> IO a
getResult fname (Left e) = ioError (errnoToIOError "" e Nothing (Just fname))
getResult _ (Right a) = return a

isDot :: FilePath -> Bool
isDot p = p == "." || p == ".."

filterDots :: [(FilePath, a)] -> [(FilePath, a)]
filterDots = filter (not . isDot . fst)

isFile :: FileStat -> Bool
isFile s =
  case statEntryType s of
  RegularFile -> True
  _ -> False

isDirectory :: FileStat -> Bool
isDirectory s = case statEntryType s of
  Directory -> True
  _ -> False

onlyDirectories :: [(FilePath, FileStat)] -> [FilePath]
onlyDirectories = map fst . filter (isDirectory . snd)

pathJoin :: FilePath -> FilePath -> FilePath
pathJoin p1 p2 = dropWhileEnd (== '/') p1 ++ "/" ++ p2

traverseDirectory :: Filesystem -> FilePath -> IO [(FilePath, FileStat)]
traverseDirectory fs p = do
  dnum <- getResult p =<< fuseOpenDirectory fs p
  allEntries <- getResult p =<< fuseReadDirectory fs p dnum
  let entries = filterDots allEntries
      paths = map (\(n, s) -> (p `pathJoin` n, s)) entries
      directories = onlyDirectories paths
  recursive <- concat <$> mapM (traverseDirectory fs) directories
  return $ paths ++ recursive

catFiles :: Filesystem -> [(FilePath, FileStat)] -> IO ()
catFiles fs es = forM_ es $ \(p, s) -> when (isFile s) $ do
  fh <- getResult p =<< fuseOpen fs p ReadOnly defaultFileFlags
  _ <- getResult p =<< fuseRead fs p fh (fromIntegral $ statFileSize s) 0
  return ()

catDirOp :: ScanDirOptions -> Filesystem -> IO ()
catDirOp ScanDirOptions{..} fs = do
  entries <- traverseDirectory fs optScanRoot
  catFiles fs entries

traverseDirOp :: ScanDirOptions -> Filesystem -> IO ()
traverseDirOp ScanDirOptions{..} fs =
  void $ traverseDirectory fs optScanRoot

-- mini benchmarking library

elapsedMicros :: TimeSpec -> IO Float
elapsedMicros start = do
  end <- getTime Monotonic
  let elapsedNanos = toNanoSecs $ diffTimeSpec start end
      elapsed = (fromIntegral elapsedNanos)/1e3 :: Float in
    return elapsed

timeIt :: IO a -> IO Float
timeIt act = do
  start <- getTime Monotonic
  _ <- act
  totalTime <- elapsedMicros start
  return totalTime

runInThread :: IO a -> IO (MVar a)
runInThread act = do
  m <- newEmptyMVar
  _ <- forkIO $ do
    -- TODO: if act throws an exception, takeMVar blocks indefinitely
    -- should probably switch to IO () -> IO (MVar ()) and close the channel
    v <- act
    putMVar m v
  return m

-- replicateInParallel par iters act runs act in n parallel copies, passing
-- 0..n-1 to each copy
replicateInParallel :: Int -> (Int -> IO a) -> IO [a]
replicateInParallel par act = do
  ms <- mapM (runInThread . act) [0..par-1]
  mapM takeMVar ms

data RtsInfo =
  RtsInfo { rtsN :: Int
          , rtsMinAllocMB :: Float }

getRtsInfo :: IO RtsInfo
getRtsInfo = do
  n <- getNumCapabilities
  gc <- getGCFlags
  return $ RtsInfo n (fromIntegral (minAllocAreaSize gc) * 4.0 / 1000 )

rtsValues :: RtsInfo -> [(String, String)]
rtsValues RtsInfo{..} =
  [ ("capabilities", show rtsN)
  , ("alloc area MB", show rtsMinAllocMB) ]

data DataPoint =
  DataPoint { pRts :: RtsInfo
            , pBenchName :: String
            , pSystem :: String
            , pIters :: Int
            , pPar :: Int
            , pElapsedMicros :: Float }

dataValues :: DataPoint -> [(String, String)]
dataValues DataPoint{..} =
  rtsValues pRts ++
  [ ("benchmark", pBenchName)
  , ("system", pSystem)
  , ("iters", show pIters)
  , ("par", show pPar)
  , ("total micros", show pElapsedMicros) ]

valueHeader :: [(String, String)] -> String
valueHeader kvs = intercalate "\t" (map fst kvs)

valueData :: [(String, String)] -> String
valueData kvs = intercalate "\t" (map snd kvs)

emptyData :: DataPoint
emptyData = DataPoint { pRts = RtsInfo{ rtsN = 0
                                      , rtsMinAllocMB = 0.0 }
                      , pBenchName = ""
                      , pSystem = "none"
                      , pIters = 0
                      , pPar = 0
                      , pElapsedMicros = 0.0 }

data ParOptions = ParOptions
  { optFscq :: Bool
  , optDiskImg :: FilePath
  , optIters :: Int
  , optN :: Int
  , optWarmup :: Bool }

instance Options ParOptions where
  defineOptions = pure ParOptions
    <*> simpleOption "fscq" False
        "run sequential FSCQ"
    <*> simpleOption "img" "disk.img"
         "path to FSCQ disk image"
    <*> simpleOption "iters" 100
         "number of iterations of stat to run"
    <*> simpleOption "n" 1
         "number of parallel threads to issue stats from"
    <*> simpleOption "warmup" True
         "warmup by running 10 untimed iterations"

-- fill in some dimensions based on global options
optsData :: ParOptions -> IO DataPoint
optsData ParOptions{..} = do
  rts <- getRtsInfo
  return $ emptyData{ pRts=rts
                    , pSystem=if optFscq then "fscq" else "cfscq"
                    , pIters=optIters
                    , pPar=optN }

type Parcommand a = Subcommand ParOptions (IO a)

checkArgs :: [String] -> IO ()
checkArgs args = when (length args > 0) $ do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)

parcommand :: Options subcmdOpts =>
              String -> (ParOptions -> subcmdOpts -> IO a) ->
              Parcommand a
parcommand name action = subcommand name $ \opts cmdOpts args -> do
  checkArgs args
  action opts cmdOpts

parallelBench :: ParOptions -> String -> (Int -> IO a) -> IO DataPoint
parallelBench opts name act = do
  when (optWarmup opts) $ forM_ [1..(optN opts)-1] $ replicateM_ 10 . act
  totalMicros <- timeIt $ replicateInParallel
    (optN opts)
    (replicateM_ (optIters opts) . act)
  p <- optsData opts
  return $ p{ pBenchName=name
            , pElapsedMicros=totalMicros}

withFs :: ParOptions -> (Filesystem -> IO a) -> IO a
withFs opts act =
  if optFscq opts then
    initFscq (optDiskImg opts) True getProcessIds >>= act
  else
    initCfscq (optDiskImg opts) True getProcessIds >>= act

simpleBenchmark :: Options subcmdOpts =>
                   String -> (subcmdOpts -> Filesystem -> IO a) ->
                   Parcommand ()
simpleBenchmark name act = parcommand name $ \opts cmdOpts -> do
  p <- withFs opts $ \fs -> parallelBench opts name (\_ -> act cmdOpts fs)
  putStrLn . valueData . dataValues $ p

headerCommand :: Parcommand ()
headerCommand = parcommand "print-header" $ \_ (_::NoOptions) -> do
  putStrLn . valueHeader . dataValues $ emptyData

main :: IO ()
main = runSubcommand [ simpleBenchmark "stat" statOp
                     , simpleBenchmark "statfs" statfsOp
                     , simpleBenchmark "cat-dir" catDirOp
                     , simpleBenchmark "traverse-dir" traverseDirOp
                     , headerCommand ]
