{-# LANGUAGE RecordWildCards #-}
module Main where

import Benchmarking
import MailServerOperations
import NativeFs
import Options

import Control.Concurrent.MVar (takeMVar)
import Control.Monad (forM)

data MailServerOptions = MailServerOptions
  { optConfig :: Config
  , optIters :: Int
  , optNumUsers :: Int
  , optDiskPath :: FilePath }

instance Options MailServerOptions where
  defineOptions = pure MailServerOptions
    <*> defineOptions
    <*> simpleOption "iters" 100
        "number of operations to run per user"
    <*> simpleOption "par" 100
        "number of users to run concurrently"
    <*> simpleOption "disk-path" "/tmp/fscq"
        "file system mount path"

app :: MailServerOptions -> IO ()
app MailServerOptions{..} = do
  fs <- createNativeFs optDiskPath
  runInParallel optNumUsers $ randomOps optConfig fs optIters

main :: IO ()
main = runCommand $ \opts _args ->
  app opts
