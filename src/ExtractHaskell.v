Require Import ExtrHaskellPrelude.
Require Import AsyncFS.
Require Import DirectoryIsolatedFS.

Extraction Language Haskell.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.pair_args_helper.

(* Uncomment the next line to enable eventlog-based profiling *)
(* Extract Inlined Constant Prog.progseq => "Profile.progseq __FILE__ __LINE__". *)

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant Cache.eviction_state  => "Evict.EvictionState".
Extract Inlined Constant Cache.eviction_init   => "Evict.eviction_init".
Extract Inlined Constant Cache.eviction_update => "Evict.eviction_update".
Extract Inlined Constant Cache.eviction_choose => "Evict.eviction_choose".

Extract Inlined Constant Log.should_flushall => "Prelude.False".

Cd "../codegen".
Recursive Extraction Library AsyncFS.
Recursive Extraction Library DirectoryIsolatedFS.
