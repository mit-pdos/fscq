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

Extract Constant MapUtils.AddrSet.SS.t => "(Data.Set.Set Prelude.Integer)".
Extract Constant MapUtils.AddrSet.SS.mem => "Data.Set.member".
Extract Constant MapUtils.AddrSet.SS.add => "Data.Set.insert".
Extract Constant MapUtils.AddrSet.SS.remove => "Data.Set.delete".
Extract Constant MapUtils.AddrSet.SS.singleton => "Data.Set.singleton".
Extract Constant MapUtils.AddrSet.SS.union => "Data.Set.union".
Extract Constant MapUtils.AddrSet.SS.inter => "Data.Set.intersection".
Extract Constant MapUtils.AddrSet.SS.diff => "Data.Set.difference".
Extract Constant MapUtils.AddrSet.SS.subset => "Data.Set.isSubsetOf".
Extract Constant MapUtils.AddrSet.SS.empty => "Data.Set.empty".
Extract Constant MapUtils.AddrSet.SS.is_empty => "Data.Set.null".
Extract Constant MapUtils.AddrSet.SS.elements => "Data.Set.elems".
Extract Constant MapUtils.AddrSet.SS.filter => "Data.Set.filter".
Extract Constant MapUtils.AddrSet.SS.fold => "(\f -> (\e -> (\s -> Data.Set.foldr f s e)))".
Extract Constant MapUtils.AddrSet.SS.for_all => "(\f -> (\s -> Data.Set.foldr (\a -> (\b -> case (f a) of Prelude.True -> b; Prelude.False -> Prelude.False)) Prelude.True s))".
Extract Constant MapUtils.AddrSet.SS.exists_ => "(\f -> (\s -> Data.Set.foldr (\a -> (\b -> case (f a) of Prelude.False -> b; Prelude.True -> Prelude.True)) Prelude.False s))".
Extract Constant MapUtils.AddrSet.SS.cardinal => "(\x -> (Prelude.fromIntegral (Data.Set.size x)))".
Extract Constant MapUtils.AddrSet.SS.partition => "Data.Set.partition".

(* Not used *)
Extract Constant MapUtils.AddrSet.SS.min_elt => "GHC.Base.error ""set_min_elt""".
Extract Constant MapUtils.AddrSet.SS.max_elt => "GHC.Base.error ""set_min_elt""".

(* Not used, no obvious equivalent *)
Extract Constant MapUtils.AddrSet.SS.equal => "GHC.Base.error ""set_equal""".
Extract Constant MapUtils.AddrSet.SS.eq_dec => "GHC.Base.error ""set_eq_dec""".
Extract Constant MapUtils.AddrSet.SS.compare => "GHC.Base.error ""set_compare""".
Extract Constant MapUtils.AddrSet.SS.choose => "GHC.Base.error ""set_choose""".