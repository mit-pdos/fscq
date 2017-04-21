module Main where

import qualified ConcurInterp as I
import TranslateTest
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

main :: IO ()
main = do
  ds <- init_disk "/dev/null"
  cs <- I.newState ds
  t <- timeAction $ replicateM_ iterations  $ I.run cs (add_tuple_concur ((5,6),7))
  t' <- timeAction $ replicateM_ iterations $ I.run cs (add_tuple_concur_raw ((5,6),7))
  putStrLn $ "translate " ++ show (timePerIter t) ++ " cycles/op"
  putStrLn $ "raw       " ++ show (timePerIter t') ++ " cycles/op"
