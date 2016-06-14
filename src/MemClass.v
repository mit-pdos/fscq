Require Export Mem.
Require Import Word.
Require Import Basics.

Set Implicit Arguments.

Existing Class EqDec.

Instance word_dec : forall n, EqDec (word n) := weq.
Instance nat_dec : EqDec nat := PeanoNat.Nat.eq_dec.

Instance unit_dec : EqDec unit.
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

Instance pair_dec : forall A B, EqDec A -> EqDec B -> EqDec (A*B).
Proof.
  unfold EqDec; intros A B AEQ BEQ.
  destruct a as [a0 b0], b as [a1 b1].
  destruct (AEQ a0 a1), (BEQ b0 b1);
    left + right;
    congruence.
Defined.