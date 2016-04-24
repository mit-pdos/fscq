module Evict where

data EvictionState =
  LRU

eviction_init :: EvictionState
eviction_init = LRU

eviction_update :: EvictionState -> Integer -> EvictionState
eviction_update s _ = s

eviction_choose :: EvictionState -> (Integer, EvictionState)
eviction_choose s = (0, s)
