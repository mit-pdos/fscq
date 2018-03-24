{-# LANGUAGE RecordWildCards #-}
module Main where

import MailServerOperations
import Options

data MailServerOptions = MailServerOptions
  { optConfig :: Config
  , optIters :: Int
  , optNumUsers :: Int }

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
    <*> simpleOption "users" 100
        "number of users to run concurrently"

app :: MailServerOptions -> IO ()
app MailServerOptions{optConfig=Config{..},..} = do
  return ()

main :: IO ()
main = runCommand $ \opts _args ->
  app opts
