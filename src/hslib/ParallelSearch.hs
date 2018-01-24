module ParallelSearch
  ( parallelSearch
  ) where

import           Control.Concurrent (setNumCapabilities)
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
                         matches = if BS.take skip tl == needle then 1 else 0
                         remaining = BS.drop skip tl in
                         matches+go remaining

searchFile :: BS.ByteString -> FuseOperations fh -> FilePath -> IO Int
searchFile needle fs p = searchString needle <$> readEntireFile fs p

parallelSearch :: FuseOperations fh -> Int -> BS.ByteString -> FilePath -> IO [(FilePath, Int)]
parallelSearch fs par needle = parAtRoot fs par search
  where search p = do
          count <- searchFile needle fs p
          return (p, count)

parAtRoot :: FuseOperations fh -> Int -> (FilePath -> IO a) -> FilePath -> IO [a]
parAtRoot fs par act p = setNumCapabilities par >> do
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

runAtRoot :: FuseOperations fh -> (FilePath -> IO a) -> FilePath -> IO [a]
runAtRoot fs act p = do
  files <- traverseDirectory fs p
  mapM (act . fst) files

parallelSearchAtRoot :: FuseOperations fh -> Int -> BS.ByteString -> FilePath -> IO [(FilePath, Int)]
parallelSearchAtRoot fs par needle p = do
  dnum <- getResult p =<< fuseOpenDirectory fs p
  allEntries <- getResult p =<< fuseReadDirectory fs p dnum
  let entries = filterDots allEntries
      paths = map (\(n, s) -> (p `pathJoin` n, s)) entries
      directories = take par (onlyDirectories paths)
      search p = do
        count <- searchFile needle fs p
        return (p, count)
  dirAsync <- mapM (async . runAtRoot fs search) directories
  concat <$> mapM wait dirAsync
