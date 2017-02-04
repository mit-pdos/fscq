Require MapUtils.

(* Fast maps using Haskell's [Data.Map.Strict] *)
Extract Constant MapUtils.AddrMap.Map.t "v" => "(Data.Map.Strict.Map Prelude.Integer v)".
Extract Constant MapUtils.AddrMap.Map.empty => "Data.Map.Strict.empty".
Extract Constant MapUtils.AddrMap.Map.is_empty => "Data.Map.Strict.null".
Extract Constant MapUtils.AddrMap.Map.add => "Data.Map.Strict.insert".
Extract Constant MapUtils.AddrMap.Map.remove => "Data.Map.Strict.delete".
Extract Constant MapUtils.AddrMap.Map.find => "Data.Map.Strict.lookup".
Extract Constant MapUtils.AddrMap.Map.map => "Data.Map.Strict.map".
Extract Constant MapUtils.AddrMap.Map.elements => "Data.Map.Strict.assocs".
Extract Constant MapUtils.AddrMap.Map.cardinal => "\m -> Prelude.fromIntegral (Data.Map.Strict.size m)".
Extract Constant MapUtils.AddrMap.Map.mem => "Data.Map.Strict.member".
Extract Constant MapUtils.AddrMap.Map.fold => "\f m z -> Data.Map.Strict.foldrWithKey f z m".

(* Not used, no obvious equivalent *)
Extract Constant MapUtils.AddrMap.Map.mapi => "GHC.Base.error ""mapi""".
Extract Constant MapUtils.AddrMap.Map.map2 => "GHC.Base.error ""map2""".
Extract Constant MapUtils.AddrMap.Map.equal => "GHC.Base.error ""equal""".
