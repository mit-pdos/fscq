module Main where

import System.Posix.IO
import MemLog
import Balloc
import Inode
import Word
import Cache
import qualified Interpreter as I
import qualified System.Directory
import qualified Testprog
import qualified FS

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

cxp :: Cache.Coq_xparams
cxp = (W 0x1000)  -- number of blocks in cache

lxp :: MemLog.Coq_xparams
lxp = MemLog.Build_xparams
  cxp
  (W 0x2000)  -- log header sector
  (W 0x2001)  -- commit flag sector
  (W 0x2002)  -- log descriptor sector
  (W 0x2010)  -- log start sector
  (W 0x40)    -- log length (at most addr_per_block)

bxp :: Balloc.Coq_xparams
bxp = Balloc.Build_xparams
  (W 0x1100)  -- bitmap start sector
  (W 0x1)     -- bitmap length

ixp :: Inode.Coq_xparams
ixp = Inode.Build_xparams
  (W 0x1000)   -- inode start sector
  (W 0x100)    -- number of inode sectors

repf :: Integer -> t -> s -> (s -> t -> IO (s, t)) -> IO (s, t)
repf 0 x s _ = return (s, x)
repf n x s f = do
  (s, y) <- f s x
  (s, z) <- repf (n-1) y s f
  return (s, z)

repf2 :: Integer -> r -> s -> (s -> IO (s, r)) -> IO (s, r)
repf2 0 r s _ = return (s, r)
repf2 n _ s f = do
  (s, r) <- f s
  (s, rr) <- repf2 (n-1) r s f
  return (s, rr)

main :: IO ()
main = do
  -- This is racy (stat'ing the file first and opening it later)
  fileExists <- System.Directory.doesFileExist disk_fn
  fd <- openFd disk_fn ReadWrite (Just 0o666) defaultFileFlags
  s <- if fileExists
  then
    do
      putStrLn "Recovering disk.."
      I.run fd $ _MEMLOG__recover lxp
  else
    do
      putStrLn "Initializing disk.."
      I.run fd $ _MEMLOG__init lxp
  putStrLn "Running program.."
  -- r <- I.run fd $ the_prog lxp
  -- r <- I.run fd $ Testprog.testcopy lxp
  -- r <- I.run fd $ Testprog.testalloc lxp bxp

  -- (s, r) <- repf 10000 (Just (W 123)) s
  --     (\s x -> case x of
  --         Nothing -> return (s, Nothing)
  --         Just xv -> I.run fd $ Testprog.test_bfile lxp bxp ixp xv s)

  (s, setok) <- I.run fd $ FS.set_size lxp bxp ixp (W 3) (W 68) s
  putStrLn $ "set_size: " ++ (show setok)
  (s, r) <- repf2 1000 False s $ \s -> I.run fd $ Testprog.test_bfile_bulkwrite lxp ixp (W 99) (W 64) s

  closeFd fd
  putStrLn $ "Done: " ++ (show r)

