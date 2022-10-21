Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.
Require Import AsyncFS.
Require DirName.

Extraction Language OCaml.

(* Avoid conflicts with existing Ocaml module names. *)
Extraction Blacklist String List Nat Array Bytes Int.

(* Optimize away some noop-like wrappers. *)
Extraction Inline Prog.pair_args_helper.

(* Variables are just integers in the interpreter. *)
Extract Inlined Constant Prog.vartype => "int".
Extract Inlined Constant Prog.vartype_eq_dec => "(=)".

(* Help eliminate the axiom (not used in executable code) *)
Extract Constant AsyncDisk.hash_fwd => "(fun _ _ -> assert false)".
Extract Constant AsyncDisk.default_hash => "(fun _ -> assert false)".
Extract Constant AsyncDisk.hashmap_get => "(fun _ _ -> assert false)".

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

(* Integer parsing *)
Require HexString.
Extract Inlined Constant HexString.to_nat => "(fun l -> Z.of_string (String.of_seq (List.to_seq l)))".

(* tail recursive list functions *)
Extract Inlined Constant Datatypes.app => "List_extra.append".
Extract Inlined Constant List.repeat => "List_extra.repeat".

(* Hook up our untrusted replacement policy. *)
Extract Inlined Constant Cache.eviction_state  => "Evict.eviction_state".
Extract Inlined Constant Cache.eviction_init   => "Evict.eviction_init".
Extract Inlined Constant Cache.eviction_update => "Evict.eviction_update".
Extract Inlined Constant Cache.eviction_choose => "Evict.eviction_choose".

Extract Inlined Constant Log.should_flushall => "false".

Cd "../codegen".
Recursive Extraction Library DirName.
Recursive Extraction Library AsyncFS.
