{-# LANGUAGE RecordWildCards #-}
module BenchmarkingData where

import DataSet
import GHC.RTS.Flags
import Control.Concurrent (getNumCapabilities)

data RtsInfo =
  RtsInfo { rtsN :: Int
          , rtsMinAllocMB :: Double }

getRtsInfo :: IO RtsInfo
getRtsInfo = do
  n <- getNumCapabilities
  gc <- getGCFlags
  return $ RtsInfo n (fromIntegral (minAllocAreaSize gc) * 4.0 / 1000 )

rtsValues :: RtsInfo -> [DataValue]
rtsValues RtsInfo{..} =
  [ kv "capabilities" rtsN
  , kv "alloc area MB" rtsMinAllocMB ]

data DataPoint =
  DataPoint { pRts :: RtsInfo
            , pWarmup :: Bool
            , pBenchName :: String
            , pBenchCategory :: String
            , pSystem :: String
            , pReps :: Int
            , pIters :: Int
            , pPar :: Int
            , pElapsedMicros :: Double }

strVal :: String -> String
strVal s = let quoted_s = "\"" ++ s ++ "\"" in
             if s == "" || ' ' `elem` s then quoted_s else s

dataValues :: DataPoint -> [DataValue]
dataValues DataPoint{..} =
  rtsValues pRts ++
  [ kv "warmup" pWarmup
  , kv "benchmark" pBenchName
  , kv "category" pBenchCategory
  , kv "system" pSystem
  , kv "reps" pReps
  , kv "iters" pIters
  , kv "par" pPar
  , kv "total micros" pElapsedMicros ]

emptyData :: DataPoint
emptyData = DataPoint { pRts = RtsInfo{ rtsN = 0
                                      , rtsMinAllocMB = 0.0 }
                      , pWarmup = False
                      , pBenchName = ""
                      , pBenchCategory = ""
                      , pSystem = "none"
                      , pReps = 0
                      , pIters = 0
                      , pPar = 0
                      , pElapsedMicros = 0.0 }

reportData :: [DataPoint] -> IO ()
reportData = mapM_ (putStrLn . dataRow . dataValues)
