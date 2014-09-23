module Main where

import System.IO
import Log
import Balloc
import Prog
import Word
import qualified Data.ByteString
import qualified Testprog

disk_fn :: String
disk_fn = "disk.img"

verbose :: Bool
verbose = True

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

read_disk :: Handle -> Coq_word -> IO Coq_word
read_disk f (W64 a) = do
  debugmsg $ "read(" ++ (show a) ++ ")"
  hSeek f AbsoluteSeek (512 * (fromIntegral a))
  bs <- Data.ByteString.hGet f 512
  return $ W4096 bs
read_disk _ _ = error "read_disk: non-W64 addr"

write_disk :: Handle -> Coq_word -> Coq_word -> IO ()
write_disk f (W64 a) (W4096 v) = do
  debugmsg $ "write(" ++ (show a) ++ ")"
  hSeek f AbsoluteSeek (512 * (fromIntegral a))
  Data.ByteString.hPut f v
  return ()
write_disk _ _ _ = error "write_disk: unexpected addr or val"

run_dcode :: Handle -> Prog.Coq_prog -> IO ()
run_dcode _ (Done _) = return ()
run_dcode f (Read a rx) = do val <- read_disk f a; run_dcode f $ rx val
run_dcode f (Write a v rx) = do write_disk f a v; run_dcode f $ rx ()

the_prog :: Log.Coq_xparams -> Prog.Coq_prog
the_prog xp =
  _LOG__init xp $ \_ ->
  _LOG__begin xp $ \_ ->
  _LOG__read xp (W64 5) $ \v ->
  _LOG__write xp (W64 6) v $ \_ ->
  _LOG__commit xp $ \_ ->
  Prog.Done ()

lxp :: Log.Coq_xparams
lxp = Log.Build_xparams
  (W64 1000)  -- log length sector
  (W64 1001)  -- commit flag sector
  (W64 1002)  -- log start sector
  (W64 1000)  -- log length

bxp :: Balloc.Coq_xparams
bxp = Balloc.Build_xparams
  (W64 950)   -- bitmap start sector
  (W64 50)    -- bitmap length

main :: IO ()
main = do
  putStrLn "Running program.."
  f <- openFile disk_fn ReadWriteMode
  -- run_dcode f $ the_prog lxp
  -- run_dcode f $ Testprog.testcopy lxp $ Prog.Done ()
  run_dcode f $ Testprog.testalloc lxp bxp $ Prog.Done ()
  hClose f
  putStrLn "Done."

