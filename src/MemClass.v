Require Export Mem.
Require Import Word.
Require Import Basics.

Set Implicit Arguments.
Set Universe Polymorphism.

Existing Class DecEq.

Instance word_dec@{i} : forall n, DecEq@{i} (word n) := weq.
Instance nat_dec@{i} : DecEq@{i} nat := PeanoNat.Nat.eq_dec.

Instance unit_dec@{i} : DecEq@{i} unit.
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