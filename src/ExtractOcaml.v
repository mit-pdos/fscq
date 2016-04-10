Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import FS.
Require Import Testprog.

Extraction Language Ocaml.

(* Avoid conflicts with existing Ocaml module names. *)
Extraction Blacklist String List Nat Array Bytes.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.progseq.
Extraction Inline Prog.pair_args_helper.

(* Work around bug in Coq's ExtrOcamlZBigInt *)
Require Import ZArith.
Extract Constant Pos.compare_cont => "fun c x y -> Big.compare_case c Lt Gt x y".

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant Cache.eviction_state  => "unit".
Extract Inlined Constant Cache.eviction_init   => "()".
Extract Inlined Constant Cache.eviction_update => "(fun state addr -> state)".
Extract Inlined Constant Cache.eviction_choose => "(fun state -> (Word.wzero Prog.addrlen, state))".
Extract Constant FS.cachesize => "10000".

Cd "../codegen".
Recursive Extraction Library FS.
Recursive Extraction Library Testprog.
