{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Concurrent
import           Control.Monad
import           Control.Monad (void)
import qualified Data.ByteString.Char8 as BSC8
import           Data.IORef
import           Data.List (intercalate)
import           Options
import           System.Exit
import           System.IO (hPutStrLn, stderr)
import           System.Random (getStdGen, setStdGen, mkStdGen)
import           System.Random.Shuffle (shuffle')

import           CfscqFs
import           DbenchExecute
import           DbenchScript (parseScriptFile)
import           FscqFs
import           Fuse
import           GenericFs
import           ParallelSearch
import           System.Posix.IO (defaultFileFlags)
import           System.Posix.Types (FileOffset)
import           Timings
import           Benchmarking

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

getFileSize :: FuseOperations Integer -> FilePath -> IO FileOffset
getFileSize fs p = do
  s <- getResult p =<< fuseGetFileStat fs p
  return $ statFileSize s

shuffleList :: [a] -> IO [a]
shuffleList xs = shuffle' xs (length xs) <$> getStdGen

readEntireFile :: Filesystem -> Maybe FileOffset -> FilePath -> IO ()
readEntireFile Filesystem{fuseOps=fs} msize p = do
  fh <- getResult p =<< fuseOpen fs p ReadOnly defaultFileFlags
  fileSize <- case msize of
    Just s -> return s
    Nothing -> getFileSize fs p
  offsets <- shuffleList [0,4096..fileSize]
  forM_ offsets $ \off ->
    fuseRead fs p fh 4096 off

catFiles :: Filesystem -> [(FilePath, FileStat)] -> IO ()
catFiles fs es = forM_ es $ \(p, s) -> when (isFile s) $ do
  readEntireFile fs (Just $ statFileSize s) p

catDirOp :: ScanDirOptions -> Filesystem -> IO ()
catDirOp ScanDirOptions{..} fs@Filesystem{fuseOps} = do
  entries <- traverseDirectory fuseOps optScanRoot
  catFiles fs entries

traverseDirOp :: ScanDirOptions -> Filesystem -> IO ()
traverseDirOp ScanDirOptions{..} Filesystem{fuseOps} =
  void $ traverseDirectory fuseOps optScanRoot

readDirPrepare :: ScanDirOptions -> Filesystem -> IO Integer
readDirPrepare ScanDirOptions{..} Filesystem{fuseOps=fs} =
  getResult optScanRoot =<< fuseOpenDirectory fs optScanRoot

readDirOp :: ScanDirOptions -> Filesystem -> Integer -> IO ()
readDirOp ScanDirOptions{..} Filesystem{fuseOps=fs} dnum =
  void $ fuseReadDirectory fs optScanRoot dnum

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
    _ <- readEntireFile fs Nothing optFile
    return ()

openOp :: FileOpOptions -> Filesystem -> IO ()
openOp FileOpOptions{..} Filesystem{fuseOps=fs} = do
    _ <- fuseOpen fs optFile ReadOnly defaultFileFlags
    return ()

data FileOffsetOpOptions =
  FileOffsetOpOptions { optFileName :: String
                      , optFileOffset :: Int }
instance Options FileOffsetOpOptions where
  defineOptions = pure FileOffsetOpOptions
    <*> simpleOption "file" "/large"
      "file to operate on"
    <*> simpleOption "offset" 0
      "offset (in bytes) to read from"

readFilePrepare :: FileOffsetOpOptions -> Filesystem -> IO Integer
readFilePrepare FileOffsetOpOptions{..} Filesystem{fuseOps=fs} =
  getResult optFileName =<< fuseOpen fs optFileName ReadOnly defaultFileFlags

readFileOp :: FileOffsetOpOptions -> Filesystem -> Integer -> IO ()
readFileOp FileOffsetOpOptions{..} Filesystem{fuseOps=fs} inum =
  void $ fuseRead fs optFileName inum 4096 (fromIntegral optFileOffset)

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
         "warmup by running untimed iterations"

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

parallelBench :: ParOptions -> IO b -> (b -> ThreadNum -> IO a) -> IO [DataPoint]
parallelBench opts@ParOptions{..} prepare act = do
  setup <- prepare
  when optWarmup $ do
    forM_ [0..optN-1] (act setup)
    logVerbose opts "===> warmup done <==="
  performMajorGC
  micros <- pickAndRunIters opts $
    parallelTimeForIters optN $ replicateM_ optReps . (act setup)
  p <- optsData opts
  return $ map (\t -> p{ pIters=length micros
                       , pElapsedMicros=t }) micros

reportTimings :: ParOptions -> Filesystem -> IO ()
reportTimings ParOptions{..} fs = when optShowDebug $ do
  tm <- readIORef (timings fs)
  printTimings tm

withFs :: ParOptions -> (Filesystem -> IO a) -> IO a
withFs opts@ParOptions{..} act =
  let initFs = if optFscq then initFscq else initCfscq in
    do
      fs <- initFs optDiskImg True getProcessIds
      act fs <* reportTimings opts fs

clearTimings :: Filesystem -> IO ()
clearTimings fs = writeIORef (timings fs) emptyTimings

reportData :: [DataPoint] -> IO ()
reportData = mapM_ (putStrLn . valueData . dataValues)

simpleBenchmarkWithSetup :: Options subcmdOpts =>
                            String ->
                            (subcmdOpts -> Filesystem -> IO b) ->
                            (subcmdOpts -> Filesystem -> b -> IO a) ->
                            Parcommand ()
simpleBenchmarkWithSetup name prepare act = parcommand name $ \opts cmdOpts -> do
  ps <- withFs opts $ \fs -> parallelBench opts
    (clearTimings fs >> prepare cmdOpts fs)
    (\setup _thread -> act cmdOpts fs setup)
  reportData $ map (\p -> p{pBenchName=name}) ps

simpleBenchmark :: Options subcmdOpts =>
                   String -> (subcmdOpts -> Filesystem -> IO a) ->
                   Parcommand ()
simpleBenchmark name act = simpleBenchmarkWithSetup name (\_ _ -> return ()) (\opts fs _ -> act opts fs)

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
  m1 <- timeAsync $ readEntireFile fs Nothing optLargeFile
  size <- getFileSize (fuseOps fs) optSmallFile
  m2 <- timeAsync $ replicateM_ reps (readEntireFile fs (Just size) optSmallFile)
  largeMicros <- takeMVar m1
  smallMicros <- takeMVar m2
  return (largeMicros, smallMicros)

seqIOConcur :: Int -> IOConcurOptions -> Filesystem -> IO (Float, Float)
seqIOConcur reps IOConcurOptions{..} fs = do
  largeMicros <- timeIt $ readEntireFile fs Nothing optLargeFile
  size <- getFileSize (fuseOps fs) optSmallFile
  smallMicros <- timeIt $ replicateM_ reps (readEntireFile fs (Just size) optSmallFile)
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
  reportData ps

data ParallelSearchOptions =
  ParallelSearchOptions { searchDir :: FilePath
                        , searchString :: String }

instance Options ParallelSearchOptions where
  defineOptions = pure ParallelSearchOptions
    <*> simpleOption "dir" "/search-benchmarks/coq"
        "directory to search under"
    <*> simpleOption "query" "propositional equality"
        "string to search for"

withCapabilities :: Int -> IO a -> IO a
withCapabilities n act = do
  n' <- getNumCapabilities
  setNumCapabilities n
  r <- act
  setNumCapabilities n'
  return r

parSearch :: ParallelSearchOptions -> Filesystem -> Int -> IO [(FilePath, Int)]
parSearch ParallelSearchOptions{..} Filesystem{fuseOps} par =
  parallelSearchAtRoot fuseOps par (BSC8.pack searchString) searchDir

printSearchResults :: ParOptions -> [(FilePath, Int)] -> IO ()
printSearchResults opts = mapM_ $ \(p, count) -> do
  when (count > 0) $ logVerbose opts $ p ++ ": " ++ show count

runParallelSearch :: ParOptions -> ParallelSearchOptions -> Filesystem -> IO [DataPoint]
runParallelSearch opts@ParOptions{..} cmdOpts fs = do
  let benchmark = parSearch cmdOpts fs
  when optWarmup $ do
    _ <- withCapabilities 1 $ benchmark optN
    clearTimings fs
    logVerbose opts "===> warmup done <==="
  performMajorGC
  micros <- pickAndRunIters opts $ \iters ->
    replicateM iters . timeIt $ replicateM_ optReps $ do
      results <- benchmark optN
      when optVerbose $ printSearchResults opts results
  p <- optsData opts
  return $ map (\t -> p{ pBenchName="par-search"
                       , pElapsedMicros=t }) micros

parSearchCommand :: Parcommand ()
parSearchCommand = parcommand "par-search" $ \opts cmdOpts -> do
  ps <- withFs opts $ \fs -> runParallelSearch opts cmdOpts fs
  reportData ps

data DbenchOptions =
  DbenchOptions { rootDir :: FilePath
                , scriptFile :: FilePath }

instance Options DbenchOptions where
  defineOptions = pure DbenchOptions
    <*> simpleOption "dir" "/dbench"
        "directory to run dbench script under"
    <*> simpleOption "script" "client.txt"
        "path to dbench fileio script to run (client.txt)"

runDbenchScript :: ParOptions -> DbenchOptions -> Filesystem -> IO [DataPoint]
runDbenchScript opts@ParOptions{..} DbenchOptions{..} Filesystem{fuseOps} = do
  parse <- parseScriptFile scriptFile
  case parse of
    Left e -> error e
    Right script -> do
    -- TODO: potentially need to force script
    logVerbose opts $ intercalate "\n" (map show script)
    performMajorGC
    let threadRoot tid = rootDir ++ "/core" ++ show tid
        run tid = runScript fuseOps . prefixScript (threadRoot tid) $ script in do
    micros <- parallelTimeForIters optN run optIters
    p <- optsData opts
    return $ map (\t -> p { pBenchName="dbench"
              , pWarmup=False
              , pReps=1
              , pElapsedMicros=t }) micros

dbenchCommand :: Parcommand ()
dbenchCommand = parcommand "dbench" $ \opts cmdOpts -> do
  ps <- withFs opts $ \fs -> runDbenchScript opts cmdOpts fs
  reportData ps

headerCommand :: Parcommand ()
headerCommand = parcommand "print-header" $ \_ (_::NoOptions) -> do
  putStrLn . valueHeader . dataValues $ emptyData

main :: IO ()
main = do
  setStdGen (mkStdGen 0)
  runSubcommand [ simpleBenchmark "stat" statOp
                , simpleBenchmark "open" openOp
                , simpleBenchmark "statfs" statfsOp
                , simpleBenchmark "cat-dir" catDirOp
                , simpleBenchmark "cat-file" catFileOp
                , simpleBenchmarkWithSetup "readdir" readDirPrepare readDirOp
                , simpleBenchmarkWithSetup "read" readFilePrepare readFileOp
                , simpleBenchmark "traverse-dir" traverseDirOp
                , ioConcurCommand
                , parSearchCommand
                , dbenchCommand
                , headerCommand ]
