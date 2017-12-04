Require Export PermProgAuto.
Require Export List.
Require Export Mem Pred.
Require Import Omega.
Require Import PeanoNat.
Require Import Nat.

Set Implicit Arguments.

Axiom finite_map : forall A AEQ V (m : @mem A AEQ V), exists a, m a = None.

Definition permitted (pr pr': perm) :=
  match pr' with
  | None => True
  | Some o' =>
    match pr with
    | None => False
    | Some o => o = o'
    end
  end.


Definition can_access (pr: perm) t :=
  match pr with
  | None =>
    match t with
    | Private _ => False
    | _ => True
    end
  | Some o =>
    match t with
    | Private o' => o = o'
    | _ => True
    end
  end.


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

(* adding state allows simpler bind *)
Definition permission_secure {T} d bm hm pr (p: prog T) :=
  forall tr tr' r,
    exec pr tr d bm hm p r (tr'++tr) ->
    trace_secure pr tr'.

Lemma can_access_trans:
  forall t pr pr',
    can_access pr' t ->
    permitted pr pr' ->
    can_access pr t.
Proof.
  intros; destruct pr, pr'.
  simpl in *; subst; assumption.
  destruct t; auto;
  simpl in *; intuition.
  intuition.
  assumption.
Qed.

Lemma op_secure_not_escalating:
  forall o pr pr',
    op_secure pr' o ->
    permitted pr pr' ->
    op_secure pr o.
Proof.
  intros.
  destruct pr; try congruence.
  destruct pr'; simpl in *; try congruence.
  unfold op_secure in *; intuition; try congruence.
  destruct o; intuition.
  eapply can_access_trans; eauto.
  eapply can_access_trans; eauto.
  destruct pr'; try congruence.  
  intuition.
Qed.

Lemma trace_app:
  forall  T (p: prog T) pr d bm hm tr r tr',
    exec pr tr d bm hm p r tr' ->
    exists tr'', tr' = tr''++tr.
Proof.
  induction 1; intuition; repeat inv_exec_perm; try solve [exists nil; eauto].
  exists (Sea t::nil); eauto.
  exists (Uns (fst tb)::nil); eauto.
  cleanup; eexists; rewrite <- app_assoc; eauto.
Qed.

Lemma trace_secure_app:
  forall pr tr1 tr2,
    trace_secure pr tr1 ->
    trace_secure pr tr2 ->
    trace_secure pr (tr1++tr2).
Proof.
  induction tr1; simpl in *; intuition.
Qed.

Lemma trace_secure_permitted:
  forall pr1 pr2 tr,
    trace_secure pr1 tr ->
    permitted pr2 pr1 ->
    trace_secure pr2 tr.
Proof.
  induction tr; simpl in *; intuition.
  eapply op_secure_not_escalating; eauto.
Qed.

Fixpoint trace_match (tr1 tr2: trace):=
  match tr1, tr2 with
    | nil, nil => True
    | h1::t1, h2::t2 => h1 = h2 /\ trace_match t1 t2
    | _, _ => False
  end.


Lemma trace_match_refl:
  forall tr, trace_match tr tr.
Proof.
  induction tr; intuition; simpl; auto.
Qed.

Lemma permitted_trans:
  forall pr1 pr2 : perm,
    permitted pr2 pr1 -> forall x0 : perm, permitted pr1 x0 -> permitted pr2 x0.
Proof.
  intros pr1 pr2 H x0 H1.
  destruct pr1; simpl in *.
  destruct pr2; subst; intuition.
  destruct x0; intuition.
Qed.

Lemma trace_secure_match:
  forall (pr1 pr2 : perm) (x : list op),
    permitted pr2 pr1 ->
    forall tr' : list op, trace_match x tr' -> trace_secure pr1 x -> trace_secure pr2 tr'.
Proof.
  induction x; intuition; simpl in *;
  destruct tr'; intuition.
  subst; simpl; intuition.
  eapply op_secure_not_escalating; eauto.
Qed.