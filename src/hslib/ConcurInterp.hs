module ConcurInterp where

import EventCSL
import Hlist
import qualified Disk
import Control.Exception as E
import Control.Concurrent.MVar

verbose :: Bool
verbose = True

debugmsg :: Int -> String -> IO ()
debugmsg tid s =
  if verbose then
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

hmember_to_int :: Hlist.Coq_member a -> Int
hmember_to_int (HFirst _) = 0
hmember_to_int (HNext _ _ x) = 1 + (hmember_to_int x)

run_dcode :: Disk.DiskState -> Int -> EventCSL.Coq_prog a -> IO a
run_dcode _ tid (Done r) = do
  debugmsg tid $ "Done"
  return r
run_dcode ds tid (StartRead a rx) = do
  debugmsg tid $ "StartRead " ++ (show a)
  -- XXX start a read, somehow...
  run_dcode ds tid $ rx ()
run_dcode ds tid (FinishRead a rx) = do
  debugmsg tid $ "FinishRead " ++ (show a)
  -- XXX it would be nice if we didn't wait until the last minute to read..
  val <- Disk.read_disk ds a
  run_dcode ds tid $ rx val
run_dcode ds tid (Write a v rx) = do
  debugmsg tid $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  run_dcode ds tid $ rx ()
run_dcode ds tid (Sync a rx) = do
  debugmsg tid $ "Sync " ++ (show a)
  Disk.sync_disk ds a
  run_dcode ds tid $ rx ()
run_dcode ds tid (Get a rx) = do
  debugmsg tid $ "Get " ++ (show (hmember_to_int a))
  val <- Disk.get_var ds (hmember_to_int a)
  run_dcode ds tid $ rx val
run_dcode ds tid (Assgn a v rx) = do
  debugmsg tid $ "Assgn " ++ (show (hmember_to_int a))
  Disk.set_var ds (hmember_to_int a) v
  run_dcode ds tid $ rx ()
run_dcode ds tid (GetTID rx) = do
  debugmsg tid $ "GetTID"
  run_dcode ds tid $ rx tid
run_dcode ds tid (Yield wchan rx) = do
  debugmsg tid $ "Yield " ++ (show wchan)
  waiter <- newEmptyMVar
  Disk.register_waiter ds wchan waiter
  Disk.release_global_lock ds
  _ <- takeMVar waiter
  Disk.acquire_global_lock ds
  run_dcode ds tid $ rx ()
run_dcode ds tid (Wakeup wchan rx) = do
  debugmsg tid $ "Wakeup " ++ (show wchan)
  waiters <- Disk.get_waiters ds wchan
  _ <- mapM (\waiter -> putMVar waiter ()) waiters
  run_dcode ds tid $ rx ()

run_dcode ds tid (GhostUpdate _ rx) = do
  debugmsg tid $ "GhostUpdate"
  run_dcode ds tid $ rx ()

run_e :: Disk.DiskState -> Int -> ((a -> EventCSL.Coq_prog a) -> EventCSL.Coq_prog a) -> IO a
run_e ds tid p = do
  Disk.acquire_global_lock ds
  ret <- run_dcode ds tid $ p (\x -> EventCSL.Done x)
  Disk.release_global_lock ds
  return ret

spin_forever :: IO a
spin_forever = do
  spin_forever

print_exception :: Int -> ErrorCall -> IO a
print_exception tid e = do
  putStrLn $ "[" ++ (show tid) ++ "] Exception: " ++ (show e)
  spin_forever

run :: Disk.DiskState -> Int -> ((a -> EventCSL.Coq_prog a) -> EventCSL.Coq_prog a) -> IO a
run ds tid p = E.catch (run_e ds tid p) (print_exception tid)
