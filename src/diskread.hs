{-# LANGUAGE RecordWildCards #-}
module Main where

import Control.Exception (evaluate)
import Control.Monad
import Disk
import Foreign.Marshal.Alloc
import Options
import System.Random (getStdGen)
import System.Random.Shuffle (shuffle')
import UnixIO

data ReadType = ReadDisk | Simple | CpuIntensive
  deriving (Bounded, Enum, Show)

data MainOptions = MainOptions
  { optDiskImg :: FilePath
  , optTotalDataMb :: Int
  , optSkipSizeKb :: Int
  , optRandom :: Bool
  , optReadType :: ReadType
  , optFibonacciArg :: Int }

instance Options MainOptions where
  defineOptions = pure MainOptions
    <*> simpleOption "img" "disk.img"
        "disk image file to read from"
    <*> simpleOption "data-mb" 100
        "total MB to read"
    <*> simpleOption "skip-kb" 4
        "read 4KB every this many KB"
    <*> simpleOption "random" False
        "read in random order"
    <*> defineOption (optionType_enum "read type (ReadDisk|Simple|CpuIntensive)") (\o -> o
        { optionLongFlags = ["read-type"]
        , optionDefault = Simple
        })
    <*> simpleOption "fibonacci" 16
        "fibonacci argument for CpuIntensive read"

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

fibonacci :: Int -> Int
fibonacci 0 = 1
fibonacci 1 = 1
fibonacci n = fibonacci (n-1) + fibonacci (n-2)

cpu_read :: Int -> DiskState -> Int -> IO ()
cpu_read fibArg (S fd _ _ _) a = do
  allocaBytes 4096 $ \buf -> do
    cc <- pread fd buf 4096 (fromIntegral $ 4096*a)
    if cc == 4096 then do
      _ <- evaluate (fibonacci fibArg)
      return ()
    else error $ "simple_read: short read: " ++ show cc ++ " @ " ++ show a

shuffleList :: [a] -> IO [a]
shuffleList xs = shuffle' xs (length xs) <$> getStdGen

mainCmd :: MainOptions -> [String] -> IO ()
mainCmd opts@MainOptions{..} _ = do
  ds <- init_disk optDiskImg
  offsets <- if optRandom then shuffleList (readOffsets opts) else return (readOffsets opts)
  case optReadType of
    Simple -> forM_ offsets $ simple_read ds
    ReadDisk -> forM_ offsets $ read_disk ds . fromIntegral
    CpuIntensive -> forM_ offsets $ cpu_read optFibonacciArg ds

main :: IO ()
main = runCommand mainCmd
