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
    hPutStrLn stderr $ name ++ " " ++ show c ++ " -> " ++ show (fromIntegral s/3333000::Double)
