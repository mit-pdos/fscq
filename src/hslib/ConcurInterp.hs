module ConcurInterp where

import CoopConcur
import Variables
import Hlist
import Data.Maybe (fromJust)
import qualified Disk
import Word
import Control.Exception as E
import Control.Concurrent.MVar
import Control.Concurrent (forkIO)
import Control.Monad (when)
import System.CPUTime
import qualified Data.Map
import qualified Data.List
import GHC.Prim
import Data.IORef
import qualified Crypto.Hash.SHA256 as SHA256

data InterpOptions = InterpOptions
  { logDebug :: Bool
  , logReadTimings :: Bool
  , releaseOnYield :: Bool }

debugmsg :: InterpOptions -> Int -> String -> IO ()
debugmsg opts tid s =
  if logDebug opts then
    putStrLn $ "[" ++ (show tid) ++ "] " ++ s
  else
    return ()

timingStart :: InterpOptions -> String -> IO Integer
timingStart opts s =
  if logReadTimings opts then do
    t <- getCPUTime
    putStrLn $ "[" ++ show t ++ "] " ++ s
    return t
  else
    return 0

timingFinish :: InterpOptions -> Integer -> String -> IO ()
timingFinish opts start s =
  if logReadTimings opts then do
    t <- getCPUTime
    let elapsed = (fromIntegral (t - start))/1e9 :: Float
    putStrLn $ "[" ++ show t ++ "] " ++ s ++ " (" ++ show elapsed ++ "ms" ++ ")"
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
set_var m a v = Data.Map.insert (hmember_to_int a) (unsafeCoerce v) m

type PendingRead = MVar Coq_word
type ThreadReads = [Integer]

data BackgroundReads =
  BackgroundReads !(Data.Map.Map Integer PendingRead) !(Data.Map.Map Int ThreadReads)

new_read :: InterpOptions -> Disk.DiskState -> BackgroundReads -> Integer -> Int -> IO BackgroundReads
new_read opts ds (BackgroundReads pendings tid_reads) a tid = do
  pending <- newEmptyMVar
  _ <- forkIO $ do
    start <- timingStart opts $ "fetch from  " ++ show a
    val <- Disk.read_disk ds a
    val' <- evaluate val
    timingFinish opts start $ "done with " ++ show a
    putMVar pending val'
  let pendings' = Data.Map.insert a pending pendings
      tid_reads' = Data.Map.alter
        (\v -> case v of
            Nothing -> Just $ [a]
            Just tids -> Just $ tids ++ [a]) tid tid_reads in
    return $ BackgroundReads pendings' tid_reads'

finish_read :: InterpOptions -> BackgroundReads -> Integer -> Int -> IO (Coq_word, BackgroundReads)
finish_read opts (BackgroundReads pendings tid_reads) a tid =
  let m_read = fromJust . Data.Map.lookup a $ pendings in do
    v <- do
      maybe_v <- tryTakeMVar m_read
      case maybe_v of
        Just v -> return v
        Nothing -> do
          putStrLn $ "waiting for fetch " ++ show a;
          takeMVar m_read
    -- it's possible for this address to be initiated by another tid, which is
    -- waiting for it to finish before resuming; we will remove the reference to
    -- this pending read, but if another thread has a reference to it
    putMVar m_read v
    let pendings' = Data.Map.delete a pendings
    tid_addrs <- return $ Data.Map.findWithDefault [] tid tid_reads
    (tid_pendings, tid_dones) <- return $
      Data.List.partition (`Data.Map.member` pendings') tid_addrs
    when (length tid_pendings > 0) $ do
      error $ show tid ++ " issued multiple pending reads: " ++ show tid_pendings
    when (length tid_addrs > 1) $ do
      -- this isn't an error, it just means we initiated some other reads that
      -- have since finished due to other threads
      debugmsg opts tid $ "left multiple reads: " ++ show tid_addrs
    let tid_reads' = Data.Map.adjust (Data.List.\\ tid_dones) tid tid_reads in
      return $ (v, BackgroundReads pendings' tid_reads')

waitMVar :: MVar a -> IO ()
waitMVar m = do
  v <- takeMVar m
  putMVar m v

wait_tid_reads :: Int -> BackgroundReads -> IO ()
wait_tid_reads tid (BackgroundReads pendings tid_reads) = do
  let pending_reads = Data.Map.findWithDefault [] tid tid_reads in
    mapM_ (\a -> case Data.Map.lookup a pendings of
              Just m -> waitMVar m
              Nothing -> return ()) pending_reads

data ConcurrentState =
  -- CS vm lock reads tid_reads
  CS !(IORef VMap) !(MVar ()) !(IORef BackgroundReads)

acquire_global_lock :: ConcurrentState -> IO ()
acquire_global_lock (CS _ lock _) = takeMVar lock

release_global_lock :: ConcurrentState -> IO ()
release_global_lock (CS _ lock _) = putMVar lock ()

type ProgramState = (Disk.DiskState, ConcurrentState)

run_dcode :: InterpOptions -> ProgramState -> Int -> CoopConcur.Coq_prog a -> IO a
run_dcode opts _ tid (Ret r) = do
  debugmsg opts tid $ "Done"
  return . unsafeCoerce $ r
run_dcode opts (ds, CS _ _ m_reads) tid (StartRead a) = do
  debugmsg opts tid $ "StartRead " ++ (show a)
  bg_reads <- readIORef m_reads
  bg_reads' <- new_read opts ds bg_reads a tid
  writeIORef m_reads bg_reads'
  return . unsafeCoerce $ ()
run_dcode opts (_, CS _ _ m_reads) tid (FinishRead a) = do
  debugmsg opts tid $ "FinishRead " ++ (show a)
  bg_reads <- readIORef m_reads
  (val, bg_reads') <- finish_read opts bg_reads a tid
  writeIORef m_reads bg_reads'
  return . unsafeCoerce $ val
run_dcode opts (ds, _) tid (Write a v) = do
  debugmsg opts tid $ "Write " ++ (show a) ++ " " ++ (show v)
  Disk.write_disk ds a v
  return . unsafeCoerce $ ()
run_dcode opts (_, CS vm _ _) tid (Get a) = do
    debugmsg opts tid $ "Get " ++ (show (hmember_to_int a))
    m <- readIORef vm
    return . unsafeCoerce $ get_var m a
run_dcode opts (_, CS vm _ _) tid (Assgn a v) = do
  debugmsg opts tid $ "Assgn " ++ (show (hmember_to_int a))
  modifyIORef vm (\m -> set_var m a v)
  return . unsafeCoerce $ ()
run_dcode opts _ tid (GetTID) = do
  debugmsg opts tid $ "GetTID"
  return . unsafeCoerce $ tid
run_dcode opts (_, cs@(CS _ _ m_reads)) tid (Yield wchan) = do
  debugmsg opts tid $ "Yield " ++ (show wchan)
  bg_reads <- readIORef m_reads
  when (releaseOnYield opts) $ release_global_lock cs
  wait_tid_reads tid bg_reads
  when (releaseOnYield opts) $ acquire_global_lock cs
  return . unsafeCoerce $ ()
run_dcode opts _ tid (Wakeup wchan) = do
  debugmsg opts tid $ "Wakeup " ++ (show wchan)
  return . unsafeCoerce $ ()
run_dcode opts _ tid (GhostUpdate _) = do
  debugmsg opts tid $ "GhostUpdate"
  return . unsafeCoerce $ ()
run_dcode opts ps tid (Hash sz (W64 w)) =
  run_dcode opts ps tid (Hash sz (W $ fromIntegral w))
run_dcode opts _ tid (Hash sz (W w)) = do
  debugmsg opts tid $ "Hash " ++ (show sz) ++ " " ++ (show w)
  wbs <- Disk.i2bs w $ fromIntegral $ (sz + 7) `div` 8
  h <- return $ SHA256.hash wbs
  ih <- Disk.bs2i h
  return $ unsafeCoerce $ W ih
run_dcode opts ps tid (Bind p1 p2) = do
  debugmsg opts tid $ "Bind"
  r1 <- run_dcode opts ps tid p1
  r2 <- run_dcode opts ps tid (p2 r1)
  return . unsafeCoerce $ r2

run_e :: InterpOptions -> ProgramState -> Int -> CoopConcur.Coq_prog a -> IO a
run_e opts (ds, cs) tid p = do
  acquire_global_lock cs
  ret <- run_dcode opts (ds, cs) tid p
  release_global_lock cs
  return ret

spin_forever :: IO a
spin_forever = do
  spin_forever

print_exception :: Int -> ErrorCall -> IO a
print_exception tid e = do
  putStrLn $ "[" ++ (show tid) ++ "] Exception: " ++ (show e)
  spin_forever

-- initialize the concurrent state with an empty variable map
init_concurrency :: IO ConcurrentState
init_concurrency = do
  vm <- newIORef Data.Map.empty
  lock <- newMVar ()
  m_reads <- newIORef (BackgroundReads Data.Map.empty Data.Map.empty)
  return $ CS vm lock m_reads

run :: InterpOptions -> ProgramState -> Int -> CoopConcur.Coq_prog a -> IO a
run opts ps tid p = E.catch (run_e opts ps tid p) (print_exception tid)
