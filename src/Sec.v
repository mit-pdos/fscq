Require Import List.
Require Import Mem Pred.
Require Import Omega.
Require Import PeanoNat.
Require Import Nat.
Require Export ProgAuto.

Set Implicit Arguments.

Definition op_secure pr o :=
  match o with
  | Chd t' _ =>  can_access pr t'
  | Uns t' => can_access pr t'
  end.

Fixpoint trace_secure pr tr :=
  match tr with
  |nil => True
  |h::t => op_secure pr h /\
          trace_secure pr t
  end.

Lemma trace_secure_app:
  forall pr tr1 tr2,
    trace_secure pr tr1 ->
    trace_secure pr tr2 ->
    trace_secure pr (tr1++tr2).
Proof.
  induction tr1; simpl in *; intuition.
Qed.

Lemma trace_secure_app_split:
  forall pr tr1 tr2,
    trace_secure pr (tr1++tr2) ->
    trace_secure pr tr1 /\
    trace_secure pr tr2.
Proof.
  induction tr1; simpl in *; intuition.
  all: apply IHtr1 in H1; intuition.
Qed.

  Fixpoint only_public_operations tr :=
    match tr with
    | nil => True
    | op::tr' =>
      match op with
      | Uns t => t = Public
      | Chd t _ => t = Public
      end /\ only_public_operations tr'
    end.

  Lemma only_public_operations_app:
    forall tr1 tr2,
      only_public_operations (tr1++tr2) ->
      only_public_operations tr1 /\ only_public_operations tr2.
  Proof.
    induction tr1; simpl; intuition;
    specialize IHtr1 with (1:= H1); cleanup; auto.
  Qed.

  Lemma only_public_operations_app_merge:
    forall tr1 tr2,
      only_public_operations tr1 ->
      only_public_operations tr2 ->
      only_public_operations (tr1++tr2).
  Proof.
    induction tr1; simpl; intuition;
    specialize IHtr1 with (1:= H1); cleanup; auto.
  Qed.

  Lemma only_public_operations_to_trace_secure:
    forall tr,
      only_public_operations tr ->
      forall pr, trace_secure pr tr.
  Proof.
    induction tr; simpl; intuition.
    destruct a; subst; simpl; auto.
  Qed.
