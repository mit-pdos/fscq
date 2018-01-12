module Timings
  (
    Timings
  , insertTime
  , combineTimes
  , emptyTimings
  , printTimings
  ) where

import           Control.Monad.State
import qualified Data.Map.Strict as Map
import           Data.Monoid
import           System.IO (hPutStrLn, stderr)
import           Text.Printf

data Aggregate = Aggregate Integer Int

type Timings = Map.Map String Aggregate

instance Monoid Aggregate where
  mempty = Aggregate 0 0
  mappend (Aggregate s1 c1) (Aggregate s2 c2) = Aggregate (s1+s2) (c1+c2)

insertTime :: String -> Integer -> Timings -> Timings
insertTime s n = Map.insertWith (<>) s (Aggregate n 1)

combineTimes :: Timings -> Timings -> Timings
combineTimes = Map.unionWith (<>)

emptyTimings :: Timings
emptyTimings = Map.empty

printTimings :: Timings -> IO ()
printTimings tm =
  forM_ (Map.assocs tm) $ \(name, Aggregate s c) ->
    let total_us = fromIntegral s/3333::Double
        mean_us = total_us/fromIntegral c
        total_ms = total_us/1000
        l = printf "%30s %6.1fus aggregate: %-7d -> %8.1fms" name mean_us c total_ms in
    hPutStrLn stderr l
