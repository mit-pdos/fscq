module Main where

import qualified ConcurInterp as I
import TranslateTest
import Disk

import Control.Monad (replicateM_)
import System.CPUTime.Rdtsc

timeAction :: IO a -> IO Int
timeAction io = do
  t1 <- rdtsc
  _ <- io
  t2 <- rdtsc
  return (fromIntegral (t2-t1))

main :: IO ()
main = do
  ds <- init_disk "/dev/null"
  cs <- I.newState ds
  t <- timeAction $ replicateM_ 10000 $ I.run cs (add_tuple_concur ((5,6),7))
  t' <- timeAction $ replicateM_ 10000 $ I.run cs (add_tuple_concur_raw ((5,6),7))
  putStrLn $ "translate " ++ show t
  putStrLn $ "raw       " ++ show t'
