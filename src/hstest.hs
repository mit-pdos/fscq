module Main where

import Word
import qualified ConcurInterp as I
import qualified TwoBlockExample
import qualified EventCSL
import Disk
import Control.Concurrent

disk_fn :: String
disk_fn = "disk.img"

waitForChildren :: MVar [MVar ()] -> IO ()
waitForChildren children = do
  cs <- takeMVar children
  case cs of
    []   -> return ()
    m:ms -> do
      putMVar children ms
      takeMVar m
      waitForChildren children

forkChild :: MVar [MVar ()] -> IO () -> IO ()
forkChild children io = do
  mvar <- newEmptyMVar
  childlist <- takeMVar children
  putMVar children (mvar : childlist)
  _ <- forkFinally io (\_ -> putMVar mvar ())
  return ()

testprog :: Disk.DiskState -> Int -> IO ()
testprog ds tid = do
  _ <- I.run ds tid $
    \done -> EventCSL.StartRead (natToWord 64 tid) $
    \_ -> EventCSL.Yield $
    \_ -> EventCSL.FinishRead (natToWord 64 tid) $
    \val -> EventCSL.Write (natToWord 64 (tid+1)) val $
    done
  return ()

main :: IO ()
main = do
  ds <- init_disk disk_fn
  set_nblocks_disk ds 128
  putStrLn "Disk initialized.."

  children <- newMVar []
  forkChild children $ testprog ds 3
  forkChild children $ testprog ds 5
  waitForChildren children

  stats <- close_disk ds
  print_stats stats
  putStrLn "Done."

