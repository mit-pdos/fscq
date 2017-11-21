module Main where

import qualified Interpreter as SeqI
import qualified ConcurInterp as I
import TranslateTest
import ConcurCompile
import Disk

import Control.Monad (replicateM_)
import System.CPUTime.Rdtsc

timeAction :: IO a -> IO Int
timeAction io = do
  t1 <- rdtsc
  r <- io
  t2 <- rdtsc
  return $ r `seq` (fromIntegral (t2-t1))

iterations :: Int
iterations = 10000000

timePerIter :: Int -> Float
timePerIter n = (fromIntegral n) / (fromIntegral iterations)

measureAction :: String -> IO a -> IO ()
measureAction label act = do
  t <- timeAction $ replicateM_ iterations $ act
  putStrLn $ label ++ show (timePerIter t) ++ " cycles/op"
  return ()

main :: IO ()
main = do
  ds <- init_disk "/dev/null"
  cs <- I.newState ds
  measureAction "fscq prog " (SeqI.run ds $ add_tuple ((5,6),7) True)
  measureAction "translate " (I.run cs $ add_tuple_concur ((5,6),7) True)
  measureAction "compiled  " (I.run cs $ compiled_add_tuple ((5,6),7) True)
  measureAction "raw       " (I.run cs $ add_tuple_concur_raw ((5,6),7) True)
