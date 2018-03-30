{-# LANGUAGE RecordWildCards #-}
module Main where

import Benchmarking
import MailServerOperations
import NativeFs
import Options

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
    <*> simpleOption "par" 1
        "number of users to run concurrently"
    <*> simpleOption "disk-path" "/tmp/fscq"
        "file system mount path"

app :: MailServerOptions -> IO ()
app MailServerOptions{..} = do
  fs <- createNativeFs optDiskPath
  t <- timeIt $ runInParallel optNumUsers $ randomOps optConfig fs optIters
  cleanup optConfig fs
  print t

main :: IO ()
main = runCommand $ \opts _args ->
  app opts
