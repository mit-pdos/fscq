{-# LANGUAGE RankNTypes, ForeignFunctionInterface #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Concurrent
import           Control.Monad
import           Control.Monad (void)
import qualified Data.ByteString as BS
import           Data.IORef
import           Data.List (intercalate, dropWhileEnd)
import           Options
import           System.Clock
import           System.Exit
import           System.IO (hPutStrLn, stderr)

import           CfscqFs
import           FscqFs
import           Fuse
import           GenericFs
import           System.Posix.IO (defaultFileFlags)
import           Timings

import           GHC.RTS.Flags
import           System.Mem (performMajorGC)

data NoOptions = NoOptions {}
instance Options NoOptions where
  defineOptions = pure NoOptions

statfsOp :: NoOptions -> Filesystem -> IO ()
statfsOp _ Filesystem{fuseOps=fs} = void $ fuseGetFileSystemStats fs "/"

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
traverseDirectory fs@Filesystem{fuseOps} p = do
  dnum <- getResult p =<< fuseOpenDirectory fuseOps p
  allEntries <- getResult p =<< fuseReadDirectory fuseOps p dnum
  let entries = filterDots allEntries
      paths = map (\(n, s) -> (p `pathJoin` n, s)) entries
      directories = onlyDirectories paths
  recursive <- concat <$> mapM (traverseDirectory fs) directories
  return $ paths ++ recursive

readEntireFile :: Filesystem -> FilePath -> IO ()
readEntireFile Filesystem{fuseOps=fs} p = do
  fh <- getResult p =<< fuseOpen fs p ReadOnly defaultFileFlags
  go fh 0
    where chunkSize :: Num a => a
          chunkSize = 4096
          go fh off = do
            bs <- getResult p =<< fuseRead fs p fh chunkSize off
            if BS.length bs < chunkSize
              then return ()
              else go fh (off+chunkSize)

catFiles :: Filesystem -> [(FilePath, FileStat)] -> IO ()
catFiles fs es = forM_ es $ \(p, s) -> when (isFile s) $ do
  readEntireFile fs p

catDirOp :: ScanDirOptions -> Filesystem -> IO ()
catDirOp ScanDirOptions{..} fs = do
  entries <- traverseDirectory fs optScanRoot
  catFiles fs entries

traverseDirOp :: ScanDirOptions -> Filesystem -> IO ()
traverseDirOp ScanDirOptions{..} fs =
  void $ traverseDirectory fs optScanRoot

data FileOpOptions =
  FileOpOptions { optFile :: String }
instance Options FileOpOptions where
  defineOptions = pure FileOpOptions <*>
    simpleOption "file" "/small"
      "file to operate on"

statOp :: FileOpOptions -> Filesystem -> IO ()
statOp FileOpOptions{..} Filesystem{fuseOps=fs} = do
    _ <- fuseGetFileStat fs optFile
    return ()

catFileOp :: FileOpOptions -> Filesystem -> IO ()
catFileOp FileOpOptions{..} fs = do
    _ <- readEntireFile fs optFile
    return ()

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

timeAsync :: IO a -> IO (MVar Float)
timeAsync act = do
  start <- getTime Monotonic
  m <- newEmptyMVar
  _ <- forkIO $ do
    _ <- act
    totalTime <- elapsedMicros start
    putMVar m totalTime
  return m

type ThreadNum = Int

-- replicateInParallel par iters act runs act in n parallel copies, passing
-- 0..n-1 to each copy
replicateInParallel :: Int -> (ThreadNum -> IO a) -> IO [a]
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
            , pWarmup :: Bool
            , pBenchName :: String
            , pSystem :: String
            , pReps :: Int
            , pIters :: Int
            , pPar :: Int
            , pElapsedMicros :: Float }

dataValues :: DataPoint -> [(String, String)]
dataValues DataPoint{..} =
  rtsValues pRts ++
  [ ("warmup", if pWarmup then "warmup" else "cold")
  , ("benchmark", pBenchName)
  , ("system", pSystem)
  , ("reps", show pReps)
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
                      , pWarmup = False
                      , pBenchName = ""
                      , pSystem = "none"
                      , pReps = 0
                      , pIters = 0
                      , pPar = 0
                      , pElapsedMicros = 0.0 }

data ParOptions = ParOptions
  { optVerbose :: Bool
  , optShowDebug :: Bool
  , optFscq :: Bool
  , optDiskImg :: FilePath
  , optReps :: Int
  , optIters :: Int
  , optTargetMs :: Int
  , optN :: Int
  , optWarmup :: Bool }

instance Options ParOptions where
  defineOptions = pure ParOptions
    <*> simpleOption "verbose" False
        "print debug statements for parbench itself"
    <*> simpleOption "debug" False
        "print debug statements from (C)FSCQ"
    <*> simpleOption "fscq" False
        "run sequential FSCQ"
    <*> simpleOption "img" "disk.img"
         "path to FSCQ disk image"
    <*> simpleOption "reps" 1
         "number of repetitions to run per data point"
    <*> simpleOption "iters" 1
         "number of iterations to run"
    <*> simpleOption "target-ms" 0
         "pick iterations to run for at least this many ms (0 to disable)"
    <*> simpleOption "n" 1
         "number of parallel threads to issue stats from"
    <*> simpleOption "warmup" True
         "warmup by running 10 untimed iterations"

-- fill in some dimensions based on global options
optsData :: ParOptions -> IO DataPoint
optsData ParOptions{..} = do
  rts <- getRtsInfo
  return $ emptyData{ pRts=rts
                    , pReps=optReps
                    , pWarmup=optWarmup
                    , pSystem=if optFscq then "fscq" else "cfscq"
                    , pPar=optN }

logVerbose :: ParOptions -> String -> IO ()
logVerbose ParOptions{..} s = when optVerbose $ hPutStrLn stderr s

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

type NumIters = Int

searchIters :: ParOptions -> (NumIters -> IO [Float]) -> Float -> IO [Float]
searchIters opts act targetMicros = go 1
  where go iters = do
          performMajorGC
          logVerbose opts $ "trying " ++ show iters ++ " iters"
          micros <- act iters
          if sum micros < targetMicros
            then let iters' = fromInteger . round $
                       (fromIntegral iters :: Float) * targetMicros / sum micros
                     nextIters = max
                       (min
                         (iters'+(iters' `div` 5))
                         (100*iters))
                       (iters+1) in
                 go nextIters
          else return micros

pickAndRunIters :: ParOptions -> (NumIters -> IO [Float]) -> IO [Float]
pickAndRunIters opts@ParOptions{..} act = do
  if optTargetMs > 0 then
    searchIters opts act (fromIntegral optTargetMs * 1000)
  else act optIters

parallelTimeForIters :: Int -> (ThreadNum -> IO a) -> Int -> IO [Float]
parallelTimeForIters par act iters =
  concat <$> (replicateInParallel par $ \tid ->
    if tid == 0
    then replicateM iters (timeIt . act $ tid)
    else replicateM_ iters (act tid) >> return [])

parallelBench :: ParOptions -> (ThreadNum -> IO a) -> IO [DataPoint]
parallelBench opts@ParOptions{..} act = do
  when optWarmup $ do
    forM_ [0..optN-1] act
    logVerbose opts "===> warmup done <==="
  performMajorGC
  micros <- pickAndRunIters opts $
    parallelTimeForIters optN $ replicateM_ optReps . act
  p <- optsData opts
  return $ map (\t -> p{ pIters=length micros
                       , pElapsedMicros=t }) micros

withFs :: ParOptions -> (Filesystem -> IO a) -> IO a
withFs ParOptions{..} act =
  if optFscq then
    initFscq optDiskImg True getProcessIds >>= act
  else
    initCfscq optDiskImg True getProcessIds >>= act

reportTimings :: ParOptions -> Filesystem -> IO ()
reportTimings ParOptions{..} fs = when optShowDebug $ do
  tm <- readIORef (timings fs)
  writeIORef (timings fs) emptyTimings
  printTimings tm

reportData :: [DataPoint] -> IO ()
reportData = mapM_ (putStrLn . valueData . dataValues)

simpleBenchmark :: Options subcmdOpts =>
                   String -> (subcmdOpts -> Filesystem -> IO a) ->
                   Parcommand ()
simpleBenchmark name act = parcommand name $ \opts cmdOpts -> do
  ps <- withFs opts $ \fs -> parallelBench opts (\_ -> act cmdOpts fs)
    <* reportTimings opts fs
  reportData $ map (\p -> p{pBenchName=name}) ps

data IOConcurOptions =
  IOConcurOptions { optLargeFile :: String
                  , optSmallFile :: String }

instance Options IOConcurOptions where
  defineOptions = IOConcurOptions <$>
    simpleOption "large-file" "/large"
       "path to large file to read once"
    <*> simpleOption "small-file" "/small"
       "path to small file to read <reps> times"

parIOConcur :: Int -> IOConcurOptions -> Filesystem -> IO (Float, Float)
parIOConcur reps IOConcurOptions{..} fs = do
  m1 <- timeAsync $ readEntireFile fs optLargeFile
  m2 <- timeAsync $ replicateM_ reps (readEntireFile fs optSmallFile)
  largeMicros <- takeMVar m1
  smallMicros <- takeMVar m2
  return (largeMicros, smallMicros)

seqIOConcur :: Int -> IOConcurOptions -> Filesystem -> IO (Float, Float)
seqIOConcur reps IOConcurOptions{..} fs = do
  largeMicros <- timeIt $ readEntireFile fs optLargeFile
  smallMicros <- timeIt $ replicateM_ reps (readEntireFile fs optSmallFile)
  return (largeMicros, smallMicros)

runIOConcur :: ParOptions -> IOConcurOptions -> Filesystem -> IO [DataPoint]
runIOConcur opts@ParOptions{..} ioOpts fs = do
  (largeMicros, smallMicros) <-
    if optN >= 2
    then parIOConcur optReps ioOpts fs
    else seqIOConcur optReps ioOpts fs
  basePoint <- optsData opts
  let p = basePoint{ pIters=1
                   , pWarmup=False } in
    return $ [ p{ pBenchName="ioconcur-large"
                , pReps=1
                , pElapsedMicros=largeMicros }
              , p{ pBenchName="ioconcur-small"
                 , pReps=optReps
                 , pElapsedMicros=smallMicros} ]

ioConcurCommand :: Parcommand ()
ioConcurCommand = parcommand "io-concur" $ \opts cmdOpts -> do
  ps <- withFs opts $ \fs -> runIOConcur opts cmdOpts fs
    <* reportTimings opts fs
  reportData ps

headerCommand :: Parcommand ()
headerCommand = parcommand "print-header" $ \_ (_::NoOptions) -> do
  putStrLn . valueHeader . dataValues $ emptyData

main :: IO ()
main = runSubcommand [ simpleBenchmark "stat" statOp
                     , simpleBenchmark "statfs" statfsOp
                     , simpleBenchmark "cat-dir" catDirOp
                     , simpleBenchmark "cat-file" catFileOp
                     , simpleBenchmark "traverse-dir" traverseDirOp
                     , ioConcurCommand
                     , headerCommand ]
