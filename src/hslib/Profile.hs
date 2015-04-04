{-# LANGUAGE ViewPatterns #-}

module Profile where

import Debug.Trace

doTraceFile :: String -> Bool
doTraceFile "codegen/FS.hs" = True
doTraceFile "codegen/DirTree.hs" = True
doTraceFile "codegen/DirName.hs" = True
doTraceFile "codegen/Dir.hs" = True
doTraceFile _ = False

progseq :: String -> Int -> (b -> a) -> b -> a
progseq file line p1 p2 =
  if doTraceFile file then
    let evt = file ++ ":" ++ (show line) in
    traceEvent ("START " ++ evt) $ p1 $ traceEvent ("STOP " ++ evt) p2
  else
    p1 p2
