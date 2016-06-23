Require Import ExtrHaskellBasic.
Require Import ExtrHaskellNatInteger.
Require Import ExtrHaskellZInteger.
Require Import ExtrHaskellString.

Require Import Coq.Program.Basics.

Require Import PeanoNat.
Require Import ZArith.

Extract Inlined Constant Bool.bool_dec => "(Prelude.==)".
Extract Inlined Constant id => "(Prelude.id)".
Extract Inlined Constant app => "(Prelude.++)".
Extract Inlined Constant fst => "Prelude.fst".
Extract Inlined Constant snd => "Prelude.snd".

Extract Constant PeanoNat.Nat.pred => "(\n -> Prelude.max 0 (Prelude.pred n))".
Extract Constant PeanoNat.Nat.sub => "(\n m -> Prelude.max 0 (n Prelude.- m))".
Extract Constant PeanoNat.Nat.modulo =>
  "(\n m -> if m Prelude.== 0 then 0 else Prelude.mod n m)".
Extract Constant PeanoNat.Nat.even => "Prelude.even".
Extract Constant PeanoNat.Nat.odd => "Prelude.odd".

Extract Inductive comparison => "Prelude.Ordering"
  [ "Prelude.EQ" "Prelude.LT" "Prelude.GT" ].

Extract Inlined Constant Nat.compare => "Prelude.compare".
Extract Inlined Constant Z.compare => "Prelude.compare".
