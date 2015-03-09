Require Import ExtrHaskellPrelude.
Require Import FS.
Require Import Testprog.

Extraction Language Haskell.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.progseq.
Extraction Inline Prog.pair_args_helper.

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant Cache.eviction_state  => "Evict.EvictionState".
Extract Inlined Constant Cache.eviction_init   => "Evict.eviction_init".
Extract Inlined Constant Cache.eviction_update => "Evict.eviction_update".
Extract Inlined Constant Cache.eviction_choose => "Evict.eviction_choose".

Cd "codegen".
Recursive Extraction Library FS.
Recursive Extraction Library Testprog.
