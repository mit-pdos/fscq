module ConcurInterp where

import CoopConcur
import Variables
import Hlist
import qualified Log
import qualified FSLayout
import qualified Disk
import Word
import Control.Exception as E
import Control.Concurrent.MVar
import Data.Map
import GHC.Prim
import Data.IORef
import qualified Crypto.Hash.SHA256 as SHA256

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

-- hlist, represented as a mapping from variable indices to values
type VMap = Data.Map.Map Int GHC.Prim.Any

get_var :: VMap -> Variables.Coq_var a -> a
get_var vm a =
  case Data.Map.lookup (hmember_to_int a) vm of
    Just x -> unsafeCoerce x
    Nothing -> error $ "get of unset variable " ++ (show (hmember_to_int a))

set_var :: VMap -> Variables.Coq_var a -> a -> VMap
  -- TODO: implement
set_var m a v = Data.Map.insert (hmember_to_int a) (unsafeCoerce v) m

data ConcurrentState =
  -- CS vm lock
  CS !(IORef VMap) !(MVar ())

acquire_global_lock :: ConcurrentState -> IO ()
acquire_global_lock (CS _ lock) = takeMVar lock

release_global_lock :: ConcurrentState -> IO ()
release_global_lock (CS _ lock) = putMVar lock ()

type ProgramState = (Disk.DiskState, ConcurrentState)

run_dcode :: ProgramState -> Int -> CoopConcur.Coq_prog a -> IO a
run_dcode _ tid (Ret r) = do
  debugmsg tid $ "Done"
  return . unsafeCoerce $ r
run_dcode _ tid (StartRead a) = do
  debugmsg tid $ "StartRead " ++ (show a)
  -- XXX start a read, somehow...
  return . unsafeCoerce $ ()
run_dcode (ds, _) tid (FinishRead a) = do
  debugmsg tid $ "FinishRead " ++ (show a)
  -- XXX it would be nice if we didn't wait until the last minute to read..
  val <- Disk.read_disk ds a
  return . unsafeCoerce $ val
run_dcode (ds, _) tid (Write a v) = do
  debugmsg tid $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  return . unsafeCoerce $ ()
run_dcode (_, CS vm _) tid (Get a) = do
    debugmsg tid $ "Get " ++ (show (hmember_to_int a))
    m <- readIORef vm
    return . unsafeCoerce $ get_var m a
run_dcode (_, CS vm _) tid (Assgn a v) = do
  debugmsg tid $ "Assgn " ++ (show (hmember_to_int a))
  modifyIORef vm (\m -> set_var m a v)
  return . unsafeCoerce $ ()
run_dcode _ tid (GetTID) = do
  debugmsg tid $ "GetTID"
  return . unsafeCoerce $ tid
run_dcode (_, cs) tid (Yield wchan) = do
  debugmsg tid $ "Yield " ++ (show wchan)
  -- ignore wchan for now
  release_global_lock cs
  acquire_global_lock cs
  return . unsafeCoerce $ ()
run_dcode _ tid (Wakeup wchan) = do
  debugmsg tid $ "Wakeup " ++ (show wchan)
  return . unsafeCoerce $ ()
run_dcode _ tid (GhostUpdate _) = do
  debugmsg tid $ "GhostUpdate"
  return . unsafeCoerce $ ()
run_dcode ps tid (Hash sz (W64 w)) =
  run_dcode ps tid (Hash sz (W $ fromIntegral w))
run_dcode _ tid (Hash sz (W w)) = do
  debugmsg tid $ "Hash " ++ (show sz) ++ " " ++ (show w)
  wbs <- Disk.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  h <- return $ SHA256.hash wbs
  ih <- Disk.bs2i h
  return $ unsafeCoerce $ W ih
run_dcode ps tid (Bind p1 p2) = do
  debugmsg tid $ "Bind"
  r1 <- run_dcode ps tid p1
  r2 <- run_dcode ps tid (p2 r1)
  return . unsafeCoerce $ r2

run_e :: ProgramState -> Int -> CoopConcur.Coq_prog a -> IO a
run_e (ds, cs) tid p = do
  acquire_global_lock cs
  ret <- run_dcode (ds, cs) tid p
  release_global_lock cs
  return ret

spin_forever :: IO a
spin_forever = do
  spin_forever

print_exception :: Int -> ErrorCall -> IO a
print_exception tid e = do
  putStrLn $ "[" ++ (show tid) ++ "] Exception: " ++ (show e)
  spin_forever

type MSCS = (Bool, Log.LOG__Coq_memstate)
type FSXP = FSLayout.Coq_fs_xparams

init_concurrency :: VMap -> IO ConcurrentState
init_concurrency m = do
  vm <- newIORef m
  lock <- newMVar ()
  return $ CS vm lock

run :: ProgramState -> Int -> CoopConcur.Coq_prog a -> IO a
run ps tid p = E.catch (run_e ps tid p) (print_exception tid)
