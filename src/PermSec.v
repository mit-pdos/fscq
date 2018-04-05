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

(* adding state allows simpler bind *)
(* Not in use anymore *)
Fixpoint permission_secure {T} d bm hm pr (p: prog T) :=
match p with
| Seal t _ => can_access pr t
| Unseal h => forall tb, bm h = Some tb -> can_access pr (fst tb)
| Bind p1 p2 => permission_secure d bm hm pr p1 /\
                (forall d' bm' hm' r tr tr',
                exec pr tr d bm hm p1 (Finished d' bm' hm' r) tr' ->
                permission_secure d' bm' hm' pr (p2 r))
| _ => True
end.

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

Lemma trace_secure_app_split:
  forall pr tr1 tr2,
    trace_secure pr (tr1++tr2) ->
    trace_secure pr tr1 /\
    trace_secure pr tr2.
Proof.
  induction tr1; simpl in *; intuition.
  all: apply IHtr1 in H1; intuition.
Qed.