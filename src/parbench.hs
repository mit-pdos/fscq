{-# LANGUAGE RecordWildCards, NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import           Control.Concurrent
import           Control.Exception (Exception, catch)
import           Control.Monad
import           Control.Monad (void)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Char8 as BSC8
import           Data.IORef
import           Data.List (intercalate)
import           Options
import           System.Exit
import           System.IO (hPutStrLn, stderr)
import           System.Random
import           System.Random.Shuffle (shuffle')

import           Benchmarking
import           CfscqFs
import           DbenchExecute
import           DbenchScript (parseScriptFile)
import           FscqFs
import           Fuse
import           GenericFs
import           ParallelSearch
import           System.Posix.Files (ownerModes)
import           System.Posix.IO (defaultFileFlags)
import           System.Posix.Types (FileOffset, CDev(..))
import           Timings

import           GHC.RTS.Flags
import           System.Mem (performMajorGC)

data NoOptions = NoOptions {}
instance Options NoOptions where
  defineOptions = pure NoOptions

statfsOp :: ParOptions -> NoOptions -> Filesystem -> IO ()
statfsOp _ _ Filesystem{fuseOps=fs} = void $ fuseGetFileSystemStats fs "/"

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

catDirOp :: ParOptions -> ScanDirOptions -> Filesystem -> IO ()
catDirOp _ ScanDirOptions{..} fs@Filesystem{fuseOps} = do
  entries <- traverseDirectory fuseOps optScanRoot
  catFiles fs entries

traverseDirOp :: ParOptions -> ScanDirOptions -> Filesystem -> IO ()
traverseDirOp _ ScanDirOptions{..} Filesystem{fuseOps} =
  void $ traverseDirectory fuseOps optScanRoot

readDirPrepare :: ParOptions -> ScanDirOptions -> Filesystem -> IO Integer
readDirPrepare _ ScanDirOptions{..} Filesystem{fuseOps=fs} =
  getResult optScanRoot =<< fuseOpenDirectory fs optScanRoot

readDirOp :: ParOptions -> ScanDirOptions -> Filesystem -> Integer -> IO ()
readDirOp _ ScanDirOptions{..} Filesystem{fuseOps=fs} dnum =
  void $ fuseReadDirectory fs optScanRoot dnum

data FileOpOptions =
  FileOpOptions { optFile :: String }
instance Options FileOpOptions where
  defineOptions = pure FileOpOptions <*>
    simpleOption "file" "/small"
      "file to operate on"

statOp :: ParOptions -> FileOpOptions -> Filesystem -> IO ()
statOp _ FileOpOptions{..} Filesystem{fuseOps=fs} = do
    _ <- fuseGetFileStat fs optFile
    return ()

catFileOp :: ParOptions -> FileOpOptions -> Filesystem -> IO ()
catFileOp _ FileOpOptions{..} fs = do
    _ <- readEntireFile fs Nothing optFile
    return ()

openOp :: ParOptions -> FileOpOptions -> Filesystem -> IO ()
openOp _ FileOpOptions{..} Filesystem{fuseOps=fs} = do
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

readFilePrepare :: ParOptions -> FileOffsetOpOptions -> Filesystem -> IO Integer
readFilePrepare _ FileOffsetOpOptions{..} Filesystem{fuseOps=fs} =
  getResult optFileName =<< fuseOpen fs optFileName ReadOnly defaultFileFlags

readFileOp :: ParOptions -> FileOffsetOpOptions -> Filesystem -> Integer -> IO ()
readFileOp _ FileOffsetOpOptions{..} Filesystem{fuseOps=fs} inum =
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
            , pBenchCategory :: String
            , pSystem :: String
            , pReps :: Int
            , pIters :: Int
            , pPar :: Int
            , pElapsedMicros :: Float }

strVal :: String -> String
strVal s = let quoted_s = "\"" ++ s ++ "\"" in
             if s == "" || ' ' `elem` s then quoted_s else s

dataValues :: DataPoint -> [(String, String)]
dataValues DataPoint{..} =
  rtsValues pRts ++
  [ ("warmup", if pWarmup then "warmup" else "cold")
  , ("benchmark", strVal pBenchName)
  , ("category", strVal pBenchCategory)
  , ("system", strVal pSystem)
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
                      , pBenchCategory = ""
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

searchIters :: ParOptions -> (NumIters -> IO a) -> Float -> IO a
searchIters opts act targetMicros = go 1
  where go iters = do
          performMajorGC
          logVerbose opts $ "trying " ++ show iters ++ " iters"
          (x, micros) <- timed $ act iters
          if micros < targetMicros
            then let iters' = fromInteger . round $
                       (fromIntegral iters :: Float) * targetMicros / micros
                     nextIters = max
                       (min
                         (iters'+(iters' `div` 5))
                         (100*iters))
                       (iters+1) in
                 go nextIters
          else return x

pickAndRunIters :: ParOptions -> (NumIters -> IO a) -> IO a
pickAndRunIters opts@ParOptions{..} act = do
  if optTargetMs > 0 then
    searchIters opts act (fromIntegral optTargetMs * 1000)
  else act optIters

parallelTimeForIters :: Int -> (ThreadNum -> IO a) -> NumIters -> IO [Float]
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

benchCommand :: Options subcmdOpts =>
             String -> (ParOptions -> subcmdOpts -> Filesystem -> IO [DataPoint]) ->
             Parcommand ()
benchCommand name bench = parcommand name $ \opts cmdOpts -> do
  ps <- withFs opts $ \fs -> bench opts cmdOpts fs
  reportData $ map (\p -> p{pBenchName=name}) ps

benchmarkWithSetup :: Options subcmdOpts =>
                      String ->
                      (ParOptions -> subcmdOpts -> Filesystem -> IO b) ->
                      (ParOptions -> subcmdOpts -> Filesystem -> b -> ThreadNum -> IO a) ->
                      Parcommand ()
benchmarkWithSetup name prepare act = benchCommand name $ \opts cmdOpts fs ->
  parallelBench opts
    (clearTimings fs >> prepare opts cmdOpts fs)
    (\setup thread -> act opts cmdOpts fs setup thread)

simpleBenchmarkWithSetup :: Options subcmdOpts =>
                            String ->
                            (ParOptions -> subcmdOpts -> Filesystem -> IO b) ->
                            (ParOptions -> subcmdOpts -> Filesystem -> b -> IO a) ->
                            Parcommand ()
simpleBenchmarkWithSetup name prepare act =
  benchmarkWithSetup name prepare
  (\opts cmdOpts fs setup _thread -> act opts cmdOpts fs setup)

simpleBenchmark :: Options subcmdOpts =>
                   String -> (ParOptions -> subcmdOpts -> Filesystem -> IO a) ->
                   Parcommand ()
simpleBenchmark name act = simpleBenchmarkWithSetup name
  (\_ _ _ -> return ())
  (\opts cmdOpts fs _ -> act opts cmdOpts fs)

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
    return $ [ p{ pBenchCategory="large"
                , pReps=1
                , pElapsedMicros=largeMicros }
              , p{ pBenchCategory="small"
                 , pReps=optReps
                 , pElapsedMicros=smallMicros} ]

ioConcurCommand :: Parcommand ()
ioConcurCommand = benchCommand "io-concur" $ \opts cmdOpts fs ->
  runIOConcur opts cmdOpts fs

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
  return $ map (\t -> p{pElapsedMicros=t}) micros

parSearchCommand :: Parcommand ()
parSearchCommand = benchCommand "par-search" $ \opts cmdOpts fs ->
  runParallelSearch opts cmdOpts fs

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
    return $ map (\t -> p
                   { pWarmup=False
                   , pReps=1
                   , pElapsedMicros=t }) micros

dbenchCommand :: Parcommand ()
dbenchCommand = benchCommand "dbench" $ \opts cmdOpts fs ->
  runDbenchScript opts cmdOpts fs

headerCommand :: Parcommand ()
headerCommand = parcommand "print-header" $ \_ (_::NoOptions) -> do
  putStrLn . valueHeader . dataValues $ emptyData

type UniqueCtr = [IORef Int]

initUnique :: Int -> IO UniqueCtr
initUnique par = replicateM par (newIORef 0)

getUnique :: UniqueCtr -> ThreadNum -> IO Int
getUnique ctr t = let ref = ctr !! t in do
  c <- readIORef ref
  modifyIORef' ref (+1)
  return c

data WriteOptions =
  WriteOptions { writeDir :: FilePath }

instance Options WriteOptions where
  defineOptions = pure WriteOptions
    <*> simpleOption "dir" "/empty-dir"
        "directory to write within"

counterPrepare :: ParOptions -> subcmdOpts -> Filesystem -> IO UniqueCtr
counterPrepare ParOptions{..} _ _ = initUnique optN

uniqueName :: ThreadNum -> Int -> String
uniqueName tid n = "thread" ++ show tid ++ "_file" ++ show n

genericCounterOp :: (String -> IO a) -> UniqueCtr -> ThreadNum -> IO ()
genericCounterOp act ctr tid = do
  n <- getUnique ctr tid
  _ <- act (uniqueName tid n)
  return ()

createOp :: ParOptions -> WriteOptions -> Filesystem ->
            UniqueCtr -> ThreadNum -> IO ()
createOp _ WriteOptions{..} Filesystem{fuseOps} = genericCounterOp $ \name -> do
  let fname = writeDir ++ "/" ++ name
  checkError fname $ fuseCreateDevice fuseOps fname RegularFile ownerModes (CDev 0)

createDirOp :: ParOptions -> WriteOptions -> Filesystem ->
               UniqueCtr -> ThreadNum -> IO ()
createDirOp _ WriteOptions{..} Filesystem{fuseOps} = genericCounterOp $ \name -> do
  let fname = writeDir ++ "/" ++ name
  checkError fname $ fuseCreateDirectory fuseOps fname ownerModes

zeroBlock :: BS.ByteString
zeroBlock = BS.pack (replicate 4096 0)

-- returns inum of created file
createSmallFile :: Filesystem -> FilePath -> IO Integer
createSmallFile Filesystem{fuseOps=fs} fname = do
  checkError fname $ fuseCreateDevice fs fname RegularFile ownerModes (CDev 0)
  inum <- getResult fname =<< fuseOpen fs fname ReadOnly defaultFileFlags
  bytes <- getResult fname =<< fuseWrite fs fname inum zeroBlock 0
  when (bytes < 4096) (error $ "failed to initialize " ++ fname)
  return inum

writeFilePrepare :: ParOptions -> WriteOptions -> Filesystem ->
                    IO [(FilePath, Integer)]
writeFilePrepare ParOptions{..} WriteOptions{..} fs = do
  forM [0..optN-1] $ \tid -> do
    let fname = uniqueName tid 0
    inum <- createSmallFile fs fname
    return (fname, inum)

writeFileOp :: ParOptions -> WriteOptions -> Filesystem ->
               [(FilePath, Integer)] -> ThreadNum -> IO ()
writeFileOp _ WriteOptions{..} Filesystem{fuseOps=fs} inums tid = do
  let (fname, inum) = inums !! tid
  bytes <- getResult fname =<< fuseWrite fs fname inum zeroBlock 0
  when (bytes < 4096) (error $ "failed to write to " ++ fname)
  return ()

data ReaderWriterOptions = ReaderWriterOptions
  { optRWSmallFile :: FilePath
  , optRWWriteDir :: FilePath
  , optWriteReps :: Int }

instance Options ReaderWriterOptions where
  defineOptions = pure ReaderWriterOptions
    <*> simpleOption "file" "/small"
        "small file to read"
    <*> simpleOption "dir" "/empty-dir"
        "directory to write to"
    <*> simpleOption "write-reps" 1
        "run this many reps for writes (reps applies to reads)"

rwRead :: ParOptions -> ReaderWriterOptions -> Filesystem -> IO ()
rwRead ParOptions{..} ReaderWriterOptions{..} fs =
  replicateM_ optReps $ readEntireFile fs Nothing optRWSmallFile

rwWrite :: ParOptions -> ReaderWriterOptions -> Filesystem ->
           UniqueCtr -> ThreadNum -> IO ()
rwWrite ParOptions{..} ReaderWriterOptions{..} fs ctr tid =
  replicateM_ optWriteReps $ genericCounterOp (\name ->
  let fname = optRWWriteDir ++ "/" ++ name in
    createSmallFile fs fname) ctr tid

data ReadsTerminated = ReadsTerminated
  deriving Show

instance Exception ReadsTerminated

runTillException :: IO a -> IO [a]
runTillException act = do
  mx <- catch (Just <$> act) (\(_::ReadsTerminated) -> return Nothing)
  case mx of
    Nothing -> return []
    Just x -> (x:) <$> runTillException act

data RawReadWriteResults = RawReadWriteResults
  { readTimings :: [Float]
  , writeTimings :: [Float] }

startReadThreads :: ParOptions -> ReaderWriterOptions -> Filesystem ->
                   NumIters -> IO (MVar [Float])
startReadThreads opts@ParOptions{..} cmdOpts fs iters =
  if optN == 0
  then newMVar []
  else
    runInThread $ do
      let readOp = rwRead opts cmdOpts fs
      m_timings <- runInThread $ replicateM iters (timeIt readOp)
      other_reads <- replicateM (optN-1) $ runInThread readOp
      forM_ other_reads takeMVar
      takeMVar m_timings

readwriteIterate :: ParOptions -> ReaderWriterOptions -> Filesystem ->
                    UniqueCtr -> NumIters -> IO RawReadWriteResults
readwriteIterate opts@ParOptions{..} cmdOpts fs ctr iters = do
  -- start the reads and writes in separate threads
  let writeOp = rwWrite opts cmdOpts fs ctr 0
  m_reads <- startReadThreads opts cmdOpts fs iters
  m_writes <- newEmptyMVar
  w_tid <- forkIO $ do
    v <- runTillException $ timeIt writeOp
    putMVar m_writes v
  -- now finish the reads
  readTimes <- takeMVar m_reads
  -- ...and then terminate the writer thread
  throwTo w_tid ReadsTerminated
  writeTimes <- takeMVar m_writes
  return $ RawReadWriteResults { readTimings=readTimes
                               , writeTimings=writeTimes }

readWriteData :: ParOptions -> ReaderWriterOptions -> RawReadWriteResults -> IO [DataPoint]
readWriteData opts@ParOptions{..} ReaderWriterOptions{..} RawReadWriteResults{..} = do
  p <- optsData opts
  let for = flip map
      readPoints = for readTimings $ \f ->
        p { pBenchCategory="reader"
          , pElapsedMicros=f
          , pIters=length readTimings }
      writePoints = for writeTimings $ \f ->
        p { pBenchCategory="writer"
          , pElapsedMicros=f
          , pReps=optWriteReps
          , pIters=length writeTimings }
  return (readPoints ++ writePoints)

warmupReadWrite :: ParOptions -> ReaderWriterOptions -> Filesystem -> IO UniqueCtr
warmupReadWrite opts@ParOptions{..} cmdOpts fs = do
  ctr <- initUnique optN
  when optWarmup $ do
    rwRead opts cmdOpts fs
    rwWrite opts cmdOpts fs ctr 0
    logVerbose opts "===> warmup done <==="
  return ctr

runReadersWriter :: ParOptions -> ReaderWriterOptions -> Filesystem ->
                    IO [DataPoint]
runReadersWriter opts cmdOpts fs = do
  ctr <- warmupReadWrite opts cmdOpts fs
  performMajorGC
  raw <- pickAndRunIters opts $
    readwriteIterate opts cmdOpts fs ctr
  ps <- readWriteData opts cmdOpts raw
  return ps

readwriteCommand :: Parcommand ()
readwriteCommand = benchCommand "readers-writer" $ \opts cmdOpts fs -> do
  runReadersWriter opts cmdOpts fs

data ReadWriteMixOptions = ReadWriteMixOptions
  { optMixReaderWriter :: ReaderWriterOptions
  , optMixReadPercentage :: Float }

instance Options ReadWriteMixOptions where
  defineOptions = pure ReadWriteMixOptions
    <*> defineOptions
    <*> simpleOption "read-perc" 0.5
        "percentage of reads to issue"

data RawReadWriteMixResults = RawReadWriteMixResults
  { -- (isRead, micros) tuples
    readWriteMixTimings :: [(Bool, Float)] }

randomDecisions :: RandomGen g =>
                   Float -> g -> [Bool]
randomDecisions percTrue gen = do
  map (\f -> f < percTrue) (randomRs (0.0, 1.0) gen)

randomReadWrites :: RandomGen g =>
                    ParOptions -> ReadWriteMixOptions -> Filesystem ->
                    g -> UniqueCtr -> ThreadNum -> NumIters -> IO RawReadWriteMixResults
randomReadWrites opts ReadWriteMixOptions{..} fs gen ctr tid iters =
  let isReads = take iters $ randomDecisions optMixReadPercentage gen in do
  timings <- forM isReads $ \isRead -> do
    t <- if isRead
         then timeIt $ rwRead opts optMixReaderWriter fs
         else timeIt $ rwWrite opts optMixReaderWriter fs ctr tid
    return (isRead, t)
  return $ RawReadWriteMixResults timings

parRandomReadWrites :: ParOptions -> ReadWriteMixOptions -> Filesystem ->
                       UniqueCtr -> NumIters -> IO RawReadWriteMixResults
parRandomReadWrites opts@ParOptions{..} cmdOpts fs ctr iters = do
  gens <- replicateM optN newStdGen
  m_results <- forM (zip [0..] gens) $ \(tid, gen) ->
    runInThread $ randomReadWrites opts cmdOpts fs gen ctr tid iters
  threadResults <- mapM takeMVar m_results
  -- TODO: should we report results from every thread?
  return $ head threadResults

rwMixData :: ParOptions -> ReadWriteMixOptions -> RawReadWriteMixResults -> IO [DataPoint]
rwMixData opts@ParOptions{..} ReadWriteMixOptions{..} RawReadWriteMixResults{..} = do
  p <- optsData opts
  let for = flip map
      ps = for readWriteMixTimings $ \(isRead, f) ->
        p { pBenchCategory=if isRead then "r" else "w"
          , pReps=if isRead then optReps else optWriteReps optMixReaderWriter
          , pElapsedMicros=f
          , pIters=length readWriteMixTimings }
  return ps

runReadWriteMix :: ParOptions -> ReadWriteMixOptions -> Filesystem ->
                   IO [DataPoint]
runReadWriteMix opts cmdOpts@ReadWriteMixOptions{..} fs = do
  ctr <- warmupReadWrite opts optMixReaderWriter fs
  performMajorGC
  raw <- pickAndRunIters opts $
    parRandomReadWrites opts cmdOpts fs ctr
  ps <- rwMixData opts cmdOpts raw
  return ps

readWriteMixCommand :: Parcommand ()
readWriteMixCommand = benchCommand "rw-mix" $ \opts cmdOpts fs ->
  runReadWriteMix opts cmdOpts fs

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
                , benchmarkWithSetup "create" counterPrepare createOp
                , benchmarkWithSetup "create-dir" counterPrepare createDirOp
                , benchmarkWithSetup "write" writeFilePrepare writeFileOp
                , ioConcurCommand
                , parSearchCommand
                , dbenchCommand
                , readwriteCommand
                , readWriteMixCommand
                , headerCommand ]
