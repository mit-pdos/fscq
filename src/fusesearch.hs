{-# LANGUAGE RecordWildCards, Rank2Types #-}
module Main where

import Control.Monad.Catch (bracket)
import Control.Monad (when)
import Control.Monad.Reader
import Data.List (isPrefixOf)
import System.Exit
import System.IO

import Benchmarking
import BenchmarkingData
import DataSet

import Options
import System.Directory
import System.FilePath.Posix (joinPath)
import System.Process

data FsOptions = FsOptions
  { optDiskImg :: FilePath
  , optMountPath :: FilePath
  , optFscq :: Bool
  , optRtsFlags :: String
  , optFsN :: Int
  , optFsPin :: String
  , optFuseOptions :: String
  , optDowncalls :: Bool }

data FuseSearchOptions = FuseSearchOptions
  { optFsOpts :: FsOptions
  , optWarmup :: Bool
  , optN :: Int
  , optAppPin :: String
  , optSearchDir :: FilePath
  , optSearchQuery :: String
  , optCategory :: String
  , optVerbose :: Bool }

instance Options FsOptions where
  defineOptions = pure FsOptions
    <*> simpleOption "img" "/tmp/disk.img"
        "disk image to mount"
    <*> simpleOption "mount" "/tmp/fscq"
        "directory to mount FSCQ at"
    <*> simpleOption "fscq" False
        "use FSCQ instead of CFSCQ"
    <*> simpleOption "rts-flags" ""
        "RTS flags to pass to FSCQ binary"
    <*> simpleOption "fs-N" 1
        "number of capabilities for FS"
    <*> simpleOption "fs-pin" ""
        "cpu list to pin filesystem to"
    <*> simpleOption "fuse-opts" ""
        "options to pass to FUSE library via -o"
    <*> simpleOption "use-downcalls" True
        "use downcalls (opqueue) instead of C->HS upcalls"

instance Options FuseSearchOptions where
  defineOptions = pure FuseSearchOptions
    <*> defineOptions
    <*> simpleOption "warmup" True
        "warmup before timing search"
    <*> simpleOption "n" 1
        "parallelism to use in ripgrep"
    <*> simpleOption "app-pin" ""
        "cpu list to pin app to"
    <*> simpleOption "dir" "search-benchmarks/coq"
        "directory to search in"
    <*> simpleOption "query" "dependency graph"
        "string to search for"
    <*> simpleOption "category" ""
        "category field to use for output data"
    <*> simpleOption "verbose" False
        "print debug messages for fusesearch"

type AppPure a = forall m. Monad m => ReaderT FuseSearchOptions m a
type App a = ReaderT FuseSearchOptions IO a

optsData :: AppPure DataPoint
optsData = do
  FuseSearchOptions{optFsOpts=FsOptions{..}, ..} <- ask
  let rts = RtsInfo{rtsN=optFsN, rtsMinAllocMB=0}
  return $ emptyData{ pRts=rts
                    , pWarmup=optWarmup
                    , pSystem=if optFscq then "fscq" else "cfscq"
                    , pPar=optN
                    , pIters=1
                    , pReps=1
                    , pBenchName="ripgrep"
                    , pBenchCategory=optCategory }

debug :: String -> App ()
debug s = do
  v <- reader optVerbose
  when v (liftIO $ hPutStrLn stderr s)

splitArgs :: String -> [String]
splitArgs = words

pinProcess :: String -> CreateProcess -> CreateProcess
pinProcess cpuList p = if cpuList == ""
  then p
  else let cmdspec' = case cmdspec p of
             ShellCommand s -> ShellCommand $ "taskset -c " ++ cpuList ++ " " ++ s
             RawCommand prog args -> RawCommand "taskset" $
               ["-c", cpuList] ++ [prog] ++ args in
         p{cmdspec=cmdspec'}

fsProcess :: AppPure CreateProcess
fsProcess = ask >>= \FuseSearchOptions{optFsOpts=FsOptions{..}} -> do
  let binary = if optFscq then "fscq" else "cfscq"
  return $ pinProcess optFsPin $ proc binary $
    ["+RTS", "-N" ++ show optFsN, "-RTS"]
    ++ ["+RTS"] ++ splitArgs optRtsFlags ++ ["-RTS"]
    ++ ["--use-downcalls=" ++ if optDowncalls then "true" else "false"]
    ++ [optDiskImg, optMountPath]
    ++ ["--", "-f"]
    ++ if optFuseOptions == "" then [] else ["-o", optFuseOptions]

debugProc :: CreateProcess -> App ()
debugProc cp = do
  let cmd = case cmdspec cp of
        ShellCommand s -> s
        RawCommand bin args -> showCommandForUser bin args
  debug $ "> " ++ cmd

data FsHandle = FsHandle { procHandle :: ProcessHandle
                         , procStdout :: Handle }

untilM :: Monad m => m Bool -> m ()
untilM test = do
  p <- test
  if p then return () else untilM test

hReadTill :: Handle -> (String -> Bool) -> IO ()
hReadTill h p = untilM $ p <$> hGetLine h

waitForPath :: FilePath -> IO ()
waitForPath = untilM . doesPathExist

getSearchPath :: AppPure FilePath
getSearchPath = ask >>= \FuseSearchOptions{..} ->
  return $ joinPath [optMountPath optFsOpts, optSearchDir]

startFs :: App FsHandle
startFs = do
  cp <- fsProcess
  debugProc cp
  (_, Just hout, _, ph) <- liftIO $ createProcess
    cp{ std_in=NoStream
      , std_out=CreatePipe }
  liftIO $ hSetBinaryMode hout True
  liftIO $ hReadTill hout ("Starting file system" `isPrefixOf`)
  search <- getSearchPath
  liftIO $ waitForPath search
  debug "==> started file system"
  return $ FsHandle ph hout

stopFs :: FsHandle -> App ()
stopFs FsHandle{..} = do
  mountPath <- reader (optMountPath . optFsOpts)
  liftIO $ callProcess "fusermount" $ ["-u", mountPath]
  debug $ "unmounted " ++ mountPath
  -- for a clean shutdown, we have to finish reading from the pipe
  _ <- liftIO $ hGetContents procStdout
  e <- liftIO $ waitForProcess procHandle
  debug $ "==> file system shut down"
  case e of
    ExitSuccess -> return ()
    ExitFailure _ -> liftIO $ do
      hPutStrLn stderr "filesystem terminated badly"
      exitWith e

parSearch :: Int -> App ()
parSearch par = do
  FuseSearchOptions{..} <- ask
  path <- getSearchPath
  let cp = pinProcess optAppPin $ proc "rg" $
        [ "-j", show par
        , "-u", "-c"
        , optSearchQuery
        , path ]
  debugProc cp
  _ <- liftIO $ readCreateProcess cp ""
  return ()

withFs :: App a -> App a
withFs act = bracket startFs stopFs (\_ -> act)

fuseSearch :: App ()
fuseSearch = do
  warmup <- reader optWarmup
  par <- reader optN
  t <- withFs $ do
    when warmup $ parSearch 2
    debug "==> warmup done"
    timeIt $ parSearch par
  p <- optsData
  liftIO $ reportData [p{pElapsedMicros=t}]
  return ()

data NoOptions = NoOptions {}

instance Options NoOptions where
  defineOptions = pure NoOptions

type FuseSearchCommand = Subcommand FuseSearchOptions (IO ())

checkArgs :: [String] -> IO ()
checkArgs args = when (length args > 0) $ do
    putStrLn "arguments are unused, pass options as flags"
    exitWith (ExitFailure 1)

printHeaderCommand :: FuseSearchCommand
printHeaderCommand = subcommand "print-header" $ \_ NoOptions args -> do
  checkArgs args
  putStrLn . dataHeader . dataValues $ emptyData

fuseSearchCommand :: FuseSearchCommand
fuseSearchCommand = subcommand "search" $ \opts NoOptions args -> do
  checkArgs args
  runReaderT fuseSearch opts

main :: IO ()
main = runSubcommand [ printHeaderCommand
                     , fuseSearchCommand ]
