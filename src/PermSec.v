Require Import List.
Require Import Mem Pred.
Require Import Omega.
Require Import PeanoNat.
Require Import Nat.
Require Export PermProgAuto.

Set Implicit Arguments.

(* Axiom finite_map : forall A AEQ V (m : @mem A AEQ V), exists a, m a = None. *)

Definition op_secure pr o :=
  match o with
  | Sea t' =>  can_access pr t'
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