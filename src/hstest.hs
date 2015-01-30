module Main where

import System.IO
import MemLog
import Balloc
import Prog
import Word
import qualified System.Directory
import qualified System.Exit
import qualified System.Random -- apt-get install libghc-random-dev
import qualified Data.ByteString
import qualified Data.Bits
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

crashRandom :: IO Int
crashRandom = System.Random.getStdRandom (System.Random.randomR (1, 20))

maybeCrash :: IO ()
maybeCrash = do
  x <- crashRandom
  if x == 1
  then
    do
      putStrLn "CRASH!"
      System.Exit.exitFailure
  else
    return ()

bs2i :: Data.ByteString.ByteString -> Integer
bs2i = Data.ByteString.foldl' (\i b -> (i `Data.Bits.shiftL` 8) + fromIntegral b) 0

i2bs :: Integer -> Data.ByteString.ByteString
i2bs = Data.ByteString.reverse . Data.ByteString.unfoldr (\i -> if i == 0 then Nothing else Just (fromIntegral i, i `Data.Bits.shiftR` 8))

read_disk :: Handle -> Coq_word -> IO Coq_word
read_disk f (W a) = do
  debugmsg $ "read(" ++ (show a) ++ ")"
  hSeek f AbsoluteSeek $ 512*a
  bs <- Data.ByteString.hGet f 512
  return $ W $ bs2i bs

write_disk :: Handle -> Coq_word -> Coq_word -> IO ()
write_disk f (W a) (W v) = do
  maybeCrash
  debugmsg $ "write(" ++ (show a) ++ ")"
  hSeek f AbsoluteSeek $ 512*a
  Data.ByteString.hPut f $ i2bs v
  return ()

run_dcode :: Handle -> Prog.Coq_prog a -> IO a
run_dcode _ (Done r) = return r
run_dcode f (Read a rx) = do val <- read_disk f a; run_dcode f $ rx val
run_dcode f (Write a v rx) = do write_disk f a v; run_dcode f $ rx ()

-- the_prog :: Log.Coq_xparams -> Prog.Coq_prog ()
-- the_prog xp =
--   _LOG__init xp $ \_ ->
--   _LOG__begin xp $ \_ ->
--   _LOG__read xp (W64 5) $ \v ->
--   _LOG__write xp (W64 6) v $ \_ ->
--   _LOG__commit xp $ \_ ->
--   Prog.Done ()

lxp :: MemLog.Coq_xparams
lxp = MemLog.Build_xparams
  (W 0x1000)  -- log header sector
  (W 0x1001)  -- commit flag sector
  (W 0x1010)  -- log start sector
  (W 0x1000)  -- log length, and MemLog uses one more for a block of addrs

bxp :: Balloc.Coq_xparams
bxp = Balloc.Build_xparams
  (W 0x500)   -- bitmap start sector
  (W 0x10)    -- bitmap length

main :: IO ()
main = do
  -- This is racy (stat'ing the file first and opening it later)
  fileExists <- System.Directory.doesFileExist disk_fn
  f <- openFile disk_fn ReadWriteMode
  if fileExists
  then
    do
      putStrLn "Recovering disk.."
      run_dcode f $ _MEMLOG__recover lxp $ \_ -> Prog.Done ()
  else
    do
      putStrLn "Initializing disk.."
      run_dcode f $ _MEMLOG__init lxp $ \_ -> Prog.Done ()
  putStrLn "Running program.."
  -- r <- run_dcode f $ the_prog lxp
  -- r <- run_dcode f $ Testprog.testcopy lxp $ Prog.Done ()
  r <- run_dcode f $ Testprog.testalloc lxp bxp $ \x -> Prog.Done x
  hClose f
  putStrLn $ "Done: " ++ (show r)

