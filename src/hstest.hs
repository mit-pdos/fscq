{-# OPTIONS_GHC -XMagicHash #-}

module Main where

import Word
import qualified ConcurInterp as I
import qualified TwoBlockExample
import qualified EventCSL
import qualified MemCache
import Disk
import Control.Concurrent
import GHC.Base

unsafeCoerce :: a -> b
unsafeCoerce = GHC.Base.unsafeCoerce#

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

initmem :: Disk.DiskState -> Int -> IO ()
initmem ds tid = do
  I.run ds tid $ \done ->
    EventCSL.Assgn TwoBlockExample._MyCacheSemantics__Transitions__coq_Cache (unsafeCoerce (MemCache._Map__empty :: MemCache.Map__Coq_t (MemCache.Coq_cache_entry EventCSL.BusyFlag))) $ \_ ->
    done ()

testprog :: Disk.DiskState -> Int -> IO ()
testprog ds tid = do
  _ <- I.run ds tid $
    \done -> EventCSL.StartRead (natToWord 64 tid) $
    \_ -> EventCSL.Yield (natToWord 64 123) $
    \_ -> EventCSL.FinishRead (natToWord 64 tid) $
    \val -> EventCSL.Write (natToWord 64 (tid+1)) val $
    done
  return ()

twoblock :: Disk.DiskState -> Int -> IO ()
twoblock ds tid = do
  _ <- I.run ds tid $ TwoBlockExample._TwoBlocksI__write_yield_read (W 0)
  return ()

main :: IO ()
main = do
  ds <- init_disk disk_fn
  set_nblocks_disk ds 128
  putStrLn "Disk initialized.."

  initmem ds 0

  children <- newMVar []
  forkChild children $ twoblock ds 1
  forkChild children $ twoblock ds 2
  forkChild children $ testprog ds 3
  forkChild children $ testprog ds 5
  waitForChildren children

  stats <- close_disk ds
  print_stats stats
  putStrLn "Done."

