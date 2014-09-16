module Main where

import System.IO
import Log
import Prog
import Word

disk_fn = "disk.img"

read_disk :: Coq_word -> IO Coq_word
read_disk addr = do
  f <- openFile disk_fn ReadMode
  hClose f
  -- XXX actually read block at addr, return value..
  return addr

write_disk :: Coq_word -> Coq_word -> IO ()
write_disk addr val = do
  f <- openFile disk_fn WriteMode
  hClose f
  -- XXX actually write block at addr with val..
  return ()

run_dcode :: Prog.Coq_prog -> IO ()
run_dcode prog =
  case prog of
    Done _ -> return ()
    Read addr rx ->
      do val <- read_disk addr; run_dcode $ rx val
    Write addr val rx ->
      do write_disk addr val; run_dcode $ rx ()

the_prog :: Coq_xparams -> Prog.Coq_prog
the_prog xp =
  _LOG__init xp $ \_ ->
  _LOG__begin xp $ \_ ->
  _LOG__abort xp $ \_ ->
  Prog.Done ()

-- xp :: Coq_xparams

main :: IO ()
main = do
  putStrLn "Hello world"

