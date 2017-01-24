Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import ExtrOcamlNatBigInt.
Require Import ExtrOcamlZBigInt.

Require Import Coq.Program.Basics.

Require Import PeanoNat.
Require Import ZArith.

Extraction Language Ocaml.

(* Avoid conflicts with existing Ocaml module names. *)
Extraction Blacklist String List Nat Array Bytes.

(* Work around bug in Coq's ExtrOcamlZBigInt *)
Require Import ZArith.
Extract Constant Pos.compare_cont => "fun c x y -> Big.compare_case c Lt Gt x y".

Require Import GoExtracted.
Require Import GoSemantics.

Cd "../codegen".

Separate Extraction GoExtracted GoSemantics.