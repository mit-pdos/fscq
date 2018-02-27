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

(* Optimize away control flow constructs. *)
Extraction Inline BasicProg.If_.

(* Work around bug in Coq's ExtrOcamlZBigInt *)
Require Import ZArith.
Extract Constant Pos.compare_cont => "fun c x y -> Big.compare_case c Lt Gt x y".

(* Extract some things that ExtrOcamlNatBigInt missed *)
Extract Constant Nat.add => "Big.add".
Extract Constant Nat.mul => "Big.mult".
Extract Constant Nat.pred => "fun n -> Big.max Big.zero (Big.pred n)".
Extract Constant Nat.sub => "fun n m -> Big.max Big.zero (Big.sub n m)".
Extract Constant Nat.max => "Big.max".
Extract Constant Nat.min => "Big.min".
Extract Constant Nat.div => "fun n m -> if Big.eq m Big.zero then Big.zero else Big.div n m".
Extract Constant Nat.modulo => "fun n m -> if Big.eq m Big.zero then Big.zero else Big.modulo n m".

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant Cache.eviction_state  => "unit".
Extract Inlined Constant Cache.eviction_init   => "()".
Extract Inlined Constant Cache.eviction_update => "(fun state addr -> state)".
Extract Inlined Constant Cache.eviction_choose => "(fun state -> (Word.wzero Prog.addrlen, state))".
Extract Constant FS.cachesize => "(Big.of_int 10000)".

Cd "../codegen".
Recursive Extraction Library FS.
Recursive Extraction Library Testprog.
