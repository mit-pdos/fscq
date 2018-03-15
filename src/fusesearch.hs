{-# LANGUAGE RecordWildCards, Rank2Types #-}
module Main where

import Control.Monad (when)
import Control.Monad.Reader
import Data.List (isPrefixOf)
import System.IO
import System.Exit

import Benchmarking
import BenchmarkingData
import DataSet

import Options
import System.Process

data FuseSearchOptions = FuseSearchOptions
  { optDiskImg :: FilePath
  , optMountPath :: FilePath
  , optFscq :: Bool
  , optRtsFlags :: String
  , optFuseOptions :: String
  , optWarmup :: Bool
  , optN :: Int
  , optSearchDir :: FilePath
  , optSearchQuery :: String
  , optCategory :: String }

instance Options FuseSearchOptions where
  defineOptions = pure FuseSearchOptions
    <*> simpleOption "img" "/tmp/disk.img"
        "disk image to mount"
    <*> simpleOption "mount" "/tmp/fscq"
        "directory to mount FSCQ at"
    <*> simpleOption "fscq" False
        "use FSCQ instead of CFSCQ"
    <*> simpleOption "rts-flags" ""
        "RTS flags to pass to FSCQ binary"
    <*> simpleOption "fuse-opts" ""
        "options to pass to FUSE library via -o"
    <*> simpleOption "warmup" True
        "warmup before timing search"
    <*> simpleOption "n" 1
        "parallelism to use in ripgrep"
    <*> simpleOption "dir" "/coq"
        "directory to search in"
    <*> simpleOption "query" "dependency graph"
        "string to search for"
    <*> simpleOption "category" ""
        "category field to use for output data"

type AppPure a = forall m. Monad m => ReaderT FuseSearchOptions m a
type App a = ReaderT FuseSearchOptions IO a

optsData :: AppPure DataPoint
optsData = do
  -- we don't get RTS info for the underlying file system, so just put in dummy
  -- values
  let rts = RtsInfo{rtsN=0, rtsMinAllocMB=0}
  FuseSearchOptions{..} <- ask
  return $ emptyData{ pRts=rts
                    , pWarmup=optWarmup
                    , pSystem=if optFscq then "fscq" else "cfscq"
                    , pPar=optN
                    , pBenchName="ripgrep"
                    , pBenchCategory=optCategory }

splitArgs :: String -> [String]
splitArgs = words

fsProcess :: AppPure CreateProcess
fsProcess = ask >>= \FuseSearchOptions{..} -> do
  let binary = if optFscq then "fscq" else "cfscq"
  return $ proc binary $ ["+RTS"] ++ splitArgs optRtsFlags ++ ["-RTS"]
    ++ [optDiskImg, optMountPath]
    ++ ["--", "-f"]
    ++ if optFuseOptions == "" then [] else "-o":optFuseOptions

newtype FsHandle = FsHandle { procHandle :: ProcessHandle }

hReadTill :: Handle -> (String -> Bool) -> IO ()
hReadTill h p = do
  done <- p <$> hGetLine h
  if done then return () else hReadTill h p

startFs :: App FsHandle
startFs = do
  cp <- fsProcess
  liftIO $ do
    (_, Just hout, _, ph) <- createProcess
      cp{ std_in=NoStream
        , std_out=CreatePipe }
    hReadTill hout ("Starting file system" `isPrefixOf`)
    return $ FsHandle ph

stopFs :: FsHandle -> App ()
stopFs FsHandle{..} = do
  mountPath <- reader optMountPath
  liftIO $ do
    callProcess "fusermount" $ ["-u", mountPath]
    e <- waitForProcess procHandle
    case e of
      ExitSuccess -> return ()
      ExitFailure _ -> do
        hPutStrLn stderr "filesystem terminated badly"
        exitWith e

parSearch :: App ()
parSearch = ask >>= \FuseSearchOptions{..} -> liftIO $ do
  _ <- readCreateProcess
    (proc "rg" $ [ "-j", show optN
                 , "-u", "-c"
                 , optSearchQuery
                 , optSearchDir]){ cwd=Just optMountPath } ""
  return ()

withFs :: App a -> App a
withFs act = do
  fsh <- startFs
  r <- act
  stopFs fsh
  return r

fuseSearch :: App ()
fuseSearch = do
  t <- withFs $ do
    warmup <- reader optWarmup
    when warmup $ parSearch
    timeIt parSearch
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
