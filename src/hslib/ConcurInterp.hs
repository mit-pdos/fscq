module ConcurInterp where

import EventCSL
import Hlist
import qualified Disk

verbose :: Bool
verbose = False

debugmsg :: String -> IO ()
debugmsg s =
  if verbose then
    putStrLn s
  else
    return ()

hmember_to_int :: Hlist.Coq_member a -> Int
hmember_to_int (HFirst _) = 0
hmember_to_int (HNext _ _ x) = 1 + (hmember_to_int x)

run_dcode :: Disk.DiskState -> Int -> EventCSL.Coq_prog a -> IO a
run_dcode _ _ (Done r) = do
  debugmsg $ "Done"
  return r
run_dcode ds tid (StartRead a rx) = do
  debugmsg $ "StartRead " ++ (show a)
  -- XXX start a read, somehow...
  run_dcode ds tid $ rx ()
run_dcode ds tid (FinishRead a rx) = do
  debugmsg $ "FinishRead " ++ (show a)
  -- XXX it would be nice if we didn't wait until the last minute to read..
  val <- Disk.read_disk ds a
  run_dcode ds tid $ rx val
run_dcode ds tid (Write a v rx) = do
  debugmsg $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  run_dcode ds tid $ rx ()
run_dcode ds tid (Sync a rx) = do
  debugmsg $ "Sync " ++ (show a)
  Disk.sync_disk ds a
  run_dcode ds tid $ rx ()
run_dcode ds tid (Get a rx) = do
  debugmsg $ "Get " ++ (show (hmember_to_int a))
  run_dcode ds tid $ rx $ Disk.get_var ds (hmember_to_int a)
run_dcode ds tid (Assgn a v rx) = do
  debugmsg $ "Assgn " ++ (show (hmember_to_int a))
  run_dcode (Disk.set_var ds (hmember_to_int a) v) tid $ rx ()
run_dcode ds tid (GetTID rx) = do
  debugmsg $ "GetTID"
  run_dcode ds tid $ rx tid
run_dcode ds tid (Yield rx) = do
  debugmsg $ "Yield"
  -- XXX how to yield?
  run_dcode ds tid $ rx ()
run_dcode ds tid (GhostUpdate _ rx) = do
  debugmsg $ "GhostUpdate"
  run_dcode ds tid $ rx ()
run_dcode ds tid (AcquireLock lockvar _ rx) = do
  debugmsg $ "AcquireLock"
  -- XXX check that it's not currently locked....
  run_dcode (Disk.set_var ds (hmember_to_int lockvar) (unsafeCoerce Locked)) tid $ rx ()

run :: Disk.DiskState -> Int -> ((a -> EventCSL.Coq_prog a) -> EventCSL.Coq_prog a) -> IO a
run ds tid p = run_dcode ds tid $ p (\x -> EventCSL.Done x)
