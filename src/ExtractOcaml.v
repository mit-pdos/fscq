Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import FS.
Require Import Testprog.

Extraction Language Ocaml.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.progseq.
Extraction Inline Prog.pair_args_helper.

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant Cache.eviction_state  => "unit".
Extract Inlined Constant Cache.eviction_init   => "()".
Extract Inlined Constant Cache.eviction_update => "fun state addr -> state".
Extract Inlined Constant Cache.eviction_choose => "fun state -> (0, state)".
Extract Constant FS.cachesize => "10000".

Cd "../codegen".
Recursive Extraction Library FS.
Recursive Extraction Library Testprog.
