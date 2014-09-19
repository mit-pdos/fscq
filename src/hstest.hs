module Main where

import System.IO
import Log
import Prog
import Word
import qualified Data.ByteString

disk_fn = "disk.img"

read_disk :: Handle -> Coq_word -> IO Coq_word
read_disk f addr = case addr of {
  W64 a -> (do
    putStrLn $ "read(" ++ (show a) ++ ")"
    hSeek f AbsoluteSeek (512 * (fromIntegral a))
    bs <- Data.ByteString.hGet f 512
    return $ W4096 bs);
  _ -> error "read_disk: non-W64 addr"
}

write_disk :: Handle -> Coq_word -> Coq_word -> IO ()
write_disk f addr val = case addr of {
  W64 a -> case val of {
    W4096 v -> (do
      putStrLn $ "write(" ++ (show a) ++ ")"
      hSeek f AbsoluteSeek (512 * (fromIntegral a))
      Data.ByteString.hPut f v
      return ());
    _ -> error "write_disk: non-W4096 val"
  };
  _ -> error "write_disk: non-W64 addr"
}

run_dcode :: Handle -> Prog.Coq_prog -> IO ()
run_dcode f prog =
  case prog of
    Done _ -> return ()
    Read addr rx ->
      do val <- read_disk f addr; run_dcode f $ rx val
    Write addr val rx ->
      do write_disk f addr val; run_dcode f $ rx ()

the_prog :: Coq_xparams -> Prog.Coq_prog
the_prog xp =
  _LOG__init xp $ \_ ->
  _LOG__begin xp $ \_ ->
  _LOG__read xp (W64 5) $ \v ->
  _LOG__write xp (W64 6) v $ \_ ->
  _LOG__commit xp $ \_ ->
  Prog.Done ()

xp :: Coq_xparams
xp = Build_xparams
  (W64 100)   -- log length sector
  (W64 101)   -- commit flag sector
  (W64 102)   -- log start sector
  (W64 50)    -- log length

main :: IO ()
main = do
  putStrLn "Running program.."
  f <- openFile disk_fn ReadWriteMode
  run_dcode f $ the_prog xp
  hClose f
  putStrLn "Done."

