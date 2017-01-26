{-# LANGUAGE RankNTypes, MagicHash, EmptyCase #-}

module Main where

import AsyncDisk
import Cache
import Data.List.Split
import Disk
import Interpreter as I
import Prog
import System.Environment
import System.IO
import Word

cachesize :: Integer
cachesize = 100000

cacheInit :: Integer -> Prog.Coq_prog Coq_cachestate
cacheInit size = do
    _BUFCACHE__init size

do_read :: DiskState -> Coq_cachestate -> Integer -> IO Coq_cachestate
do_read ds cs addr = do
  (cs, block) <- I.run ds (_BUFCACHE__read addr cs)
  return cs

do_write :: DiskState -> Coq_cachestate -> Integer -> IO Coq_cachestate
do_write ds cs addr = do
  I.run ds (_BUFCACHE__write addr (wzero _Valulen__valulen) cs)

do_sync :: DiskState -> Coq_cachestate -> Integer -> IO Coq_cachestate
do_sync ds cs addr = do
  I.run ds (_BUFCACHE__sync addr cs)

exec_line :: DiskState -> Coq_cachestate -> String -> IO Coq_cachestate
exec_line ds cs line = do
  case (splitOn " " line) of
    "write" : addr : _ ->
      do_write ds cs (read addr)
    "read" : addr : _ ->
          do_read ds cs (read addr)
    "sync" : addr : _ ->
          do_sync ds cs (read addr)

exec_input :: DiskState -> Coq_cachestate -> IO Coq_cachestate
exec_input ds cs = do
  done <- isEOF
  if done
    then return cs
    else do
      line <- getLine
      cs <- exec_line ds cs line
      exec_input ds cs

run_test :: String -> [String] -> IO()
run_test disk_fn args = do
    ds <- init_disk disk_fn
    cs <- I.run ds (cacheInit cachesize)
    cs <- exec_input ds cs
    return ()


main :: IO ()
main = do
  args <- getArgs
  case args of
    fn:rest -> run_test fn rest
    _ ->
      putStrLn $ "Usage: hscache_test disk"