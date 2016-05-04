Require Export Mem.
Require Import Word.
Require Import Basics.

Set Implicit Arguments.

Existing Class DecEq.

Instance word_dec : forall n, DecEq (word n) := weq.
Instance nat_dec : DecEq nat := PeanoNat.Nat.eq_dec.

Instance unit_dec : DecEq unit.
Proof.
  left.
  destruct a, b; auto.
Defined.

Definition single_mem V := @mem unit _ (const V).

Definition singleton V (v:V) : single_mem V :=
  fun _ => Some v.

Module Example.

  Definition addrlen := 64.
  Notation addr := (word addrlen).

  Definition addr_mem := @mem addr _ (fun _ => unit).
  Definition nat_mem := @mem nat _ (fun _ => unit).
End Example.
