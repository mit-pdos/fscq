module Evict where

import Word

data EvictionState =
  LRU

eviction_init :: EvictionState
eviction_init = LRU

eviction_update :: EvictionState -> Coq_word -> EvictionState
eviction_update s _ = s

eviction_choose :: EvictionState -> (Coq_word, EvictionState)
eviction_choose s = (W 0, s)
