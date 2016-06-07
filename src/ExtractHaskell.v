Require Import ExtrHaskellPrelude.
Require Import AsyncFS.

Extraction Language Haskell.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.progseq.
Extraction Inline Prog.pair_args_helper.

(* Uncomment the next line to enable eventlog-based profiling *)
(* Extract Inlined Constant Prog.progseq => "Profile.progseq __FILE__ __LINE__". *)

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant UniCache.eviction_state  => "Evict.EvictionState".
Extract Inlined Constant UniCache.eviction_init   => "Evict.eviction_init".
Extract Inlined Constant UniCache.eviction_update => "Evict.eviction_update".
Extract Inlined Constant UniCache.eviction_choose => "Evict.eviction_choose".
Extract Constant AsyncFS.AFS.cachesize => "10000".

Cd "../codegen".
Recursive Extraction Library AsyncFS.
