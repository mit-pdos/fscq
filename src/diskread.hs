{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Monad
import Disk
import Foreign.Marshal.Alloc
import Options
import UnixIO

data MainOptions = MainOptions
  { optDiskImg :: FilePath
  , optTotalDataMb :: Int
  , optSkipSizeKb :: Int
  , optSimpleRead :: Bool }

instance Options MainOptions where
  defineOptions = pure MainOptions
    <*> simpleOption "img" "disk.img"
        "disk image file to read from"
    <*> simpleOption "data-mb" 100
        "total MB to read"
    <*> simpleOption "skip-kb" 4
        "read 4KB every this many KB"
    <*> simpleOption "simple" False
        "simplify reads to avoid buf2i"

readOffsets :: MainOptions -> [Int]
readOffsets MainOptions{..} =
  go 0
  where -- go takes an initial offset in kb
    go :: Int -> [Int]
    go n = if n < optTotalDataMb * 1024
           then n `div` 4:go (n+optSkipSizeKb)
           else []

-- read 4KB from disk at offset, with minimal extra work
simple_read :: DiskState -> Int -> IO ()
simple_read (S fd _ _ _) a = do
  allocaBytes 4096 $ \buf -> do
    cc <- pread fd buf 4096 (fromIntegral $ 4096*a)
    if cc == 4096 then return ()
    else error $ "simple_read: short read: " ++ show cc ++ " @ " ++ show a

mainCmd :: MainOptions -> [String] -> IO ()
mainCmd opts@MainOptions{..} _ = do
  ds <- init_disk optDiskImg
  let offsets = readOffsets opts in
    if optSimpleRead
    then forM_ offsets $ simple_read ds
    else forM_ offsets $ read_disk ds . fromIntegral

main :: IO ()
main = runCommand mainCmd
