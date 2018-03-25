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

configOptions :: DefineOptions Config
configOptions = pure Config
  <*> simpleOption "read-perc" 0.5
      "fraction of operations that should be reads"
  <*> simpleOption "wait-micros" 0
      "time to wait between operations (in microseconds)"
  <*> simpleOption "dir" "/mailboxes"
      "(initially empty) directory to store user mailboxes"

instance Options MailServerOptions where
  defineOptions = pure MailServerOptions
    <*> configOptions
    <*> simpleOption "iters" 100
        "number of operations to run per user"
    <*> simpleOption "par" 100
        "number of users to run concurrently"
    <*> simpleOption "disk-path" "/tmp/fscq"
        "file system mount path"

app :: MailServerOptions -> IO ()
app MailServerOptions{..} = do
  fs <- createNativeFs optDiskPath
  ms <- forM [1..optNumUsers] $ \uid ->
    runInThread $ randomOps optConfig fs uid optIters
  mapM_ takeMVar ms

main :: IO ()
main = runCommand $ \opts _args ->
  app opts
