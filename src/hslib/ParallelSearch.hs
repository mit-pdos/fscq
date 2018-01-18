module ParallelSearch
  ( parallelSearch
  ) where

import           Control.Concurrent.Async
import qualified Data.ByteString as BS
import           Fuse
import           GenericFs
import           System.Posix.IO (defaultFileFlags)

parForFiles :: FuseOperations fh -> (FilePath -> IO a) -> FilePath -> IO [a]
parForFiles fs act p = do
  dnum <- getResult p =<< fuseOpenDirectory fs p
  allEntries <- getResult p =<< fuseReadDirectory fs p dnum
  let entries = filterDots allEntries
      paths = map (\(n, s) -> (p `pathJoin` n, s)) entries
      files = onlyFiles paths
      directories = onlyDirectories paths
  fileAsync <- mapM (async . act) files
  recursiveAsync <- async $ concat <$> mapM (parForFiles fs act) directories
  fileResults <- mapM wait fileAsync
  dirResults <- wait recursiveAsync
  return $ fileResults ++ dirResults

readEntireFile :: FuseOperations fh -> FilePath -> IO BS.ByteString
readEntireFile fs p = do
  fh <- getResult p =<< fuseOpen fs p ReadOnly defaultFileFlags
  go fh 0
    where chunkSize :: Num a => a
          chunkSize = 4096
          go fh off = do
            bs <- getResult p =<< fuseRead fs p fh chunkSize off
            if BS.length bs < chunkSize
              then return BS.empty
              else BS.append bs <$> go fh (off+chunkSize)

searchString :: BS.ByteString -> BS.ByteString -> Int
searchString needle = go
  where breakAt = BS.breakSubstring needle
        skip = BS.length needle
        go s = if BS.null s
                then 0
                else let (_, tl) = breakAt s
                         remaining = BS.drop skip tl in
                         1+go remaining

searchFile :: BS.ByteString -> FuseOperations fh -> FilePath -> IO Int
searchFile needle fs p = searchString needle <$> readEntireFile fs p

parallelSearch :: FuseOperations fh -> BS.ByteString -> FilePath -> IO [(FilePath, Int)]
parallelSearch fs needle = parForFiles fs search
  where search p = do
          count <- searchFile needle fs p
          return (p, count)
