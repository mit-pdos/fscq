module Timings where

import           Control.Monad.State
import qualified Data.Map.Strict as Map
import           System.IO (hPutStrLn, stderr)

type Timings = Map.Map String [Integer]

insertTime :: String -> Integer -> Timings -> Timings
insertTime s n = Map.insertWith (++) s [n]

combineTimes :: Timings -> Timings -> Timings
combineTimes = Map.unionWith (++)

emptyTimings :: Timings
emptyTimings = Map.empty

printTimings :: Timings -> IO ()
printTimings tm =
  forM_ (Map.assocs tm) $ \(s, ns) ->
    forM_ ns $ \n ->
      hPutStrLn stderr $ "debug: " ++ s ++ " " ++ show n
