module Main where

import qualified Interpreter as SeqI
import qualified ConcurInterp as I
import qualified OptimisticTranslator
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

instance Show OptimisticTranslator.OptimisticException where
  show (OptimisticTranslator.CacheMiss a) = "CacheMiss " ++ show a
  show OptimisticTranslator.Unsupported = "Unsupported"
  show OptimisticTranslator.WriteRequired = "WriteRequired"

instance Show a => Show (OptimisticTranslator.Result a) where
  show (OptimisticTranslator.Success _ v) = "Success " ++ show v
  show (OptimisticTranslator.Failure e) = "Failure " ++ show e

main :: IO ()
main = do
  ds <- init_disk "/dev/null"
  cs <- I.newState ds
  putStrLn "add_tuple results:"
  measureAction "fscq prog " (SeqI.run ds $ add_tuple ((5,6),7) True)
  measureAction "translate " (I.run cs $ add_tuple_concur ((5,6),7) True)
  measureAction "compiled  " (I.run cs $ add_tuple_compiled ((5,6),7) True)
  measureAction "raw       " (I.run cs $ add_tuple_concur_raw ((5,6),7) True)
  putStrLn ""
  putStrLn "consecutive rdtsc:"
  t <- SeqI.run ds consecutive_rdtsc
  putStrLn $ "fscq:      " ++ show t
  (t, _) <- I.run cs consecutive_rdtsc_concur
  putStrLn $ "translate: " ++ show t
  putStrLn ""
  putStrLn "speed of rdtscs:"
  measureAction "fscq prog " (SeqI.run ds $ consecutive_rdtsc)
  measureAction "translate " (I.run cs $ consecutive_rdtsc_concur)
  measureAction "compiled  " (I.run cs $ consecutive_rdtsc_compiled)
