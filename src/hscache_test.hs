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
import Log
import FSLayout
import AsyncFS
import BFile

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

do_log_read :: DiskState -> Coq_log_xparams -> LOG__Coq_memstate -> Integer -> IO LOG__Coq_memstate
do_log_read ds lxp mscs addr = do
  (mscs, block) <- I.run ds (_LOG__read lxp addr mscs)
  return mscs

do_get_sz :: DiskState -> Coq_fs_xparams -> BFILE__Coq_memstate -> Integer -> IO BFILE__Coq_memstate
do_get_sz ds fsxp mscs inum = do
  (mscs, sz) <- I.run ds (_AFS__file_get_sz fsxp inum mscs)
  return mscs

exec_line :: DiskState -> Coq_cachestate -> String -> IO Coq_cachestate
exec_line ds cs line = do
  case (splitOn " " line) of
    "write" : addr : _ ->
      do_write ds cs (read addr)
    "read" : addr : _ ->
      do_read ds cs (read addr)
    "sync" : addr : _ ->
      do_sync ds cs (read addr)

exec_line_log :: DiskState -> Coq_log_xparams -> LOG__Coq_memstate -> String -> IO LOG__Coq_memstate
exec_line_log ds lxp mscs line = do
  case (splitOn " " line) of
    "log_read" : addr : _ ->
      do_log_read ds lxp mscs (read addr)

exec_line_afs :: DiskState -> Coq_fs_xparams -> BFILE__Coq_memstate -> String -> IO BFILE__Coq_memstate
exec_line_afs ds fsxp mscs line = do
  case (splitOn " " line) of
    "get_sz" : inum : _ ->
      do_get_sz ds fsxp mscs (read inum)

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

exec_input_log :: DiskState -> Coq_log_xparams -> LOG__Coq_memstate -> IO LOG__Coq_memstate
exec_input_log ds lxp cs = do
  done <- isEOF
  if done
    then return cs
    else do
      line <- getLine
      cs <- exec_line_log ds lxp cs line
      exec_input_log ds lxp cs

run_test_log :: String -> [String] -> IO()
run_test_log disk_fn args = do
  ds <- init_disk disk_fn
  fsxp <- return $ _AFS__compute_xparams 1 1 1
  lxp <- return $ coq_FSXPLog fsxp
  cs <- I.run ds (_BUFCACHE__init_load cachesize)
  mscs <- I.run ds (_LOG__init lxp cs)
  mscs <- exec_input_log ds lxp mscs
  return ()

exec_input_afs :: DiskState -> Coq_fs_xparams -> BFILE__Coq_memstate -> IO BFILE__Coq_memstate
exec_input_afs ds fsxp cs = do
  done <- isEOF
  if done
    then return cs
    else do
      line <- getLine
      cs <- exec_line_afs ds fsxp cs line
      exec_input_afs ds fsxp cs

run_test_afs :: String -> [String] -> IO()
run_test_afs disk_fn args = do
  ds <- init_disk disk_fn
  fsxp <- return $ _AFS__compute_xparams 1 1 1
  cs <- I.run ds (_BUFCACHE__init_load cachesize)
  mscs <- I.run ds (_LOG__init (coq_FSXPLog fsxp) cs)
  mscs <- exec_input_afs ds fsxp (True, mscs)
  return ()


main :: IO ()
main = do
  args <- getArgs
  case args of
    -- fn:rest -> run_test fn rest
    -- fn:rest -> run_test_log fn rest
    fn:rest -> run_test_afs fn rest
    _ ->
      putStrLn $ "Usage: hscache_test disk"
