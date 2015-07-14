module Main where

import Word
import qualified Interpreter as I
import qualified System.Directory
import qualified Testprog
import qualified FS
import FSLayout
import Disk
import Errno

disk_fn :: String
disk_fn = "disk.img"

-- the_prog :: Log.Coq_xparams -> Prog.Coq_prog ()
-- the_prog xp =
--   _LOG__init xp $ \_ ->
--   _LOG__begin xp $ \_ ->
--   _LOG__read xp (W64 5) $ \v ->
--   _LOG__write xp (W64 6) v $ \_ ->
--   _LOG__commit xp $ \_ ->
--   Prog.Done ()

repf :: Integer -> t -> s -> (s -> t -> IO (s, t)) -> IO (s, t)
repf 0 x s _ = return (s, x)
repf n x s f = do
  (s, y) <- f s x
  (s, z) <- repf (n-1) y s f
  return (s, z)

repf2 :: Integer -> r -> s -> (s -> IO (s, (r, ()))) -> IO (s, (r, ()))
repf2 0 r s _ = return (s, (r, ()))
repf2 n _ s f = do
  (s, (r, ())) <- f s
  (s, (rr, ())) <- repf2 (n-1) r s f
  return (s, (rr, ()))

main :: IO ()
main = do
  -- This is racy (stat'ing the file first and opening it later)
  fileExists <- System.Directory.doesFileExist disk_fn
  ds <- init_disk disk_fn
  (s, fsxp) <- if fileExists
  then
    do
      putStrLn $ "Recovering file system"
      (s, (fsxp, ())) <- I.run ds $ FS.recover
      return (s, fsxp)
  else
    do
      putStrLn $ "Initializing file system"
      res <- I.run ds $ FS.mkfs (W 1) (W 1)
      case res of
        Err _ -> error $ "mkfs failed"
        OK (s, (fsxp, ())) -> do
          set_nblocks_disk ds $ wordToNat 64 $ coq_FSXPMaxBlock fsxp
          return (s, fsxp)
  putStrLn $ "File system mounted, " ++ (show $ coq_FSXPMaxBlock fsxp) ++ " blocks"
  putStrLn "Running program.."
  -- r <- I.run ds $ the_prog lxp
  -- r <- I.run ds $ Testprog.testcopy lxp
  -- r <- I.run ds $ Testprog.testalloc lxp bxp

  -- (s, r) <- repf 10000 (Just (W 123)) s
  --     (\s x -> case x of
  --         Nothing -> return (s, Nothing)
  --         Just xv -> I.run ds $ Testprog.test_bfile fsxp xv s)

  -- (s, (setok, ())) <- I.run ds $ FS.set_size fsxp (W 3) (W 68) s
  -- putStrLn $ "set_size: " ++ (show setok)
  (s, (r, ())) <- repf2 1000 False s $ \s -> I.run ds $ Testprog.test_bfile_bulkwrite fsxp (W 99) (W 64) s

  flushlog <- get_flush_log ds
  putStrLn $ "Flush log: " ++ (show $ length flushlog)

  stats <- close_disk ds
  print_stats stats
  putStrLn $ "Done: " ++ (show r)

