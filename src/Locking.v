Require Import CoopConcur.
Require Import OrderedTypeEx.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import PeanoNat.

Module Map := FMapAVL.Make(Nat_as_OT).
Module MapFacts := WFacts_fun Nat_as_OT Map.

Set Implicit Arguments.

Section Locking.

Inductive BusyFlag : Set := Open | Locked.

Definition is_locked l :
  {l = Locked} + {l = Open}.
Proof.
  destruct l; intuition.
Defined.

Inductive BusyFlagOwner : Set := NoOwner | Owned (id:TID).

Definition BusyFlag_dec : forall x y:BusyFlag, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition BusyFlagOwner_dec : forall x y:BusyFlagOwner, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition Flags := Map.t BusyFlag.

Definition get_lock (l:Flags) (a:nat) :=
  match Map.find a l with
  | Some o => o
  | None => Open
  end.

Definition free_lock (l:Flags) (a:nat) : Flags :=
  Map.remove a l.

Definition set_locked (l:Flags) (a:nat) : Flags :=
  Map.add a Locked l.

Definition is_open (a:nat) (l:Flags) :
  {get_lock l a = Open} + {get_lock l a <> Open}.
Proof.
  destruct (get_lock l a); auto.
  right; inversion 1.
Defined.

Section FreeSetTheorems.

  Hint Unfold get_lock set_locked free_lock : locks.
  Hint Rewrite MapFacts.add_eq_o using (solve [ auto ]) : locks.
  Hint Rewrite MapFacts.add_neq_o using (solve [ auto ]) : locks.
  Hint Rewrite MapFacts.remove_eq_o using (solve [ auto ]) : locks.
  Hint Rewrite MapFacts.remove_neq_o using (solve [ auto ]) : locks.

  Ltac t := autounfold with locks;
      intros;
      subst;
      autorewrite with locks;
      auto.

  Notation proof := ltac:(t) (only parsing).

  Definition free_lock_eq : forall l a a',
      a = a' ->
      get_lock (free_lock l a) a' = _ := proof.

  Definition free_lock_neq : forall l a a',
      a <> a' ->
      get_lock (free_lock l a) a' = get_lock l a' := proof.

  Definition set_locked_eq : forall l a a',
      a = a' ->
      get_lock (set_locked l a) a' = _ := proof.

  Definition set_locked_neq : forall l a a',
      a <> a' ->
      get_lock (set_locked l a) a' = get_lock l a' := proof.

End FreeSetTheorems.

Definition Locks AT (AEQ: EqDec AT) := AT -> BusyFlagOwner.

Arguments Locks AT {AEQ}.

Section AbstractLocks.

  Variable AT:Type.
  Variable AEQ: EqDec AT.

  Definition upd_lock (l: @Locks AT AEQ) a0 o' :=
    fun a => if AEQ a0 a then o' else l a.

  Ltac t :=
    unfold upd_lock; intros;
    match goal with
    | [ a: AT, a': AT |- _ ] =>
      destruct (AEQ a a');
        try congruence
    end;
    auto.

  Theorem upd_lock_eq : forall l a a' o',
      a = a' ->
      upd_lock l a o' a' = o'.
  Proof. t. Qed.

  Theorem upd_lock_neq : forall l a a' o',
      a <> a' ->
      upd_lock l a o' a' = l a'.
  Proof. t. Qed.

End AbstractLocks.

Inductive lock_rep : BusyFlag -> BusyFlagOwner -> Prop :=
| LockOpen : lock_rep Open NoOwner
| LockOwned : forall tid, lock_rep Locked (Owned tid).

Theorem lock_rep_open : forall o,
    lock_rep Open o ->
    o = NoOwner.
Proof.
  inversion 1; auto.
Qed.

Definition locks_rep AT (AEQ: EqDec AT) (flags: AT -> BusyFlag) (locks: Locks AT) :=
  forall a, lock_rep (flags a) (locks a).

Inductive lock_transition tid : BusyFlagOwner -> BusyFlagOwner -> Prop :=
| Transition_NoChange : forall o o', o = o' -> lock_transition tid o o'
| Transition_OwnerAcquire : lock_transition tid NoOwner (Owned tid)
| Transition_OwnerRelease : lock_transition tid (Owned tid) NoOwner.

Hint Constructors lock_transition.

Theorem lock_transition_preorder : forall tid,
    PreOrder (lock_transition tid).
Proof.
  constructor; hnf; intros;
    repeat match goal with
           | [ H: lock_transition _ _ _ |- _ ] =>
             inversion H; subst; clear H
           end; eauto.
Qed.

Definition lock_protocol AT (AEQ: EqDec AT) tid (locks locks': Locks AT) :=
  forall a, lock_transition tid (locks a) (locks' a).

Theorem lock_protocol_refl : forall AT (AEQ: EqDec AT) tid (locks: Locks AT),
    lock_protocol tid locks locks.
Proof.
  unfold lock_protocol;
    eauto using lock_transition_preorder.
Qed.

End Locking.

Hint Constructors lock_transition.

Arguments Locks AT {AEQ}.
