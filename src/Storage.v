Require Import List.
Require Import Arith.
Import ListNotations.
Require Import FsTactics.
Require Import FunctionalExtensionality.

Definition value := nat.
Definition addr := nat.
Definition block := nat.

Section Storage.

(* Storage *)

Definition storage := block -> value.
Definition st_init : storage := fun _ => 0.
Definition st_read (s:storage) (b:block) : value := s b.
Definition st_write (s:storage) (b:block) (v:value) : storage :=
  fun b' => if eq_nat_dec b' b then v else s b'.

(** A quick useful list lemma *)
Lemma app_comm_cons : forall A (ls1 : list A) x ls2,
  ls1 ++ x :: ls2 = (ls1 ++ x :: nil) ++ ls2.
Proof.
  intros.
  apply (app_assoc ls1 [x] ls2).
Qed.

(** There's no point in two consecutive writes to the same address. *)
Lemma st_write_eq : forall d b v v',
  st_write (st_write d b v) b v' = st_write d b v'.
Proof.
  unfold st_write; intros; extensionality b'; t.
Qed.

Hint Rewrite st_write_eq.

(** Writes to unequal addresses commute. *)
Lemma st_write_neq : forall d b b' v v',
  b <> b' ->
  st_write (st_write d b v) b' v' = st_write (st_write d b' v') b v.
Proof.
  unfold st_write; intros; extensionality b''; t.
Qed.

End Storage.

