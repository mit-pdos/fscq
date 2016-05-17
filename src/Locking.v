Require Import EventCSL.

Set Implicit Arguments.

Section Locking.

Variable Sigma:State.
Variable delta : Protocol Sigma.

Inductive BusyFlag := Open | Locked.

Definition is_locked l :
  {l = Locked} + {l = Open}.
Proof.
  destruct l; intuition eauto.
Defined.

Inductive BusyFlagOwner : Set :=
| NoOwner
| Owned (id:TID).

Definition BusyFlag_dec : forall x y:BusyFlag, {x = y} + {x <> y}.
Proof.
  decide equality.
Defined.

Definition BusyFlagOwner_dec : forall x y:BusyFlagOwner, {x = y} + {x <> y}.
Proof.
  decide equality.
  decide equality.
Defined.

(** given a lock variable and some other variable v, generate a
relation for tid that makes the variable read-only for non-owners. *)
Definition lock_protects (lvar : abstraction Sigma -> BusyFlagOwner)
           {tv} (v : abstraction Sigma -> tv) tid (s s': abstraction Sigma) :=
  forall owner_tid,
    lvar s = Owned owner_tid ->
    tid <> owner_tid ->
    v s' = v s.

Inductive lock_transition tid : BusyFlagOwner -> BusyFlagOwner -> Prop :=
| Transition_NoChange : forall o o', o = o' -> lock_transition tid o o'
| Transition_OwnerAcquire : forall o o', o = NoOwner ->
                                o' = Owned tid ->
                                lock_transition tid o o'
| Transition_OwnerRelease : forall o o', o = Owned tid ->
                                o' = NoOwner ->
                                lock_transition tid o o'.

Hint Constructors lock_transition.

Definition lock_protocol (lvar : abstraction Sigma -> BusyFlagOwner) (tid : TID) :
  abstraction Sigma -> abstraction Sigma -> Prop :=
  fun s s' => lock_transition tid (lvar s) (lvar s').

Theorem lock_protects_trans : forall lvar tv (v: _ -> tv) tid s s' s'',
  lock_protects lvar v tid s s' ->
  lock_protects lvar v tid s' s'' ->
  lock_protocol lvar tid s s' ->
  lock_protects lvar v tid s s''.
Proof.
  unfold lock_protects; intros.
  eapply eq_trans with (y := v s'); eauto.
  specialize (H owner_tid); intuition.
  eapply H0; eauto.
  inversion H1; subst; congruence.
Qed.

Lemma lock_protects_locked : forall lvar tv (v: _ -> tv) tid s s',
    lvar s = Owned tid ->
    lock_protects lvar v tid s s'.
Proof.
  unfold lock_protects.
  congruence.
Qed.

Lemma lock_protects_unchanged : forall lvar tv (v: _ -> tv) tid s s',
    v s = v s' ->
    lock_protects lvar v tid s s'.
Proof.
  unfold lock_protects.
  eauto.
Qed.

Lemma lock_protects_indifference : forall lvar tv (v: _ -> tv) tid
  s0 s0' s1 s1',
    lock_protects lvar v tid s0 s1 ->
    lvar s0 = lvar s0' ->
    v s0 = v s0' ->
    v s1 = v s1' ->
    lock_protects lvar v tid s0' s1'.
Proof.
  unfold lock_protects.
  intros.
  rewrite H0 in *.
  rewrite H1 in *.
  rewrite H2 in *.
  eauto.
Qed.

Hint Extern 1 (_ = _) => congruence.

Theorem lock_transition_trans : forall tid o o' o'',
  lock_transition tid o o' ->
  lock_transition tid o' o'' ->
  lock_transition tid o o''.
Proof.
  intros.
  repeat match goal with
  | [ H: lock_transition _ _ _ |- _ ] =>
    inversion H; subst; clear H
  end; eauto.
Qed.

Corollary lock_protocol_trans : forall lvar tid s s' s'',
  lock_protocol lvar tid s s' ->
  lock_protocol lvar tid s' s'' ->
  lock_protocol lvar tid s s''.
Proof.
  unfold lock_protocol; eauto using lock_transition_trans.
Qed.

Theorem lock_protocol_indifference : forall lvar tid s0 s1 s0' s1',
    lock_protocol lvar tid s0 s1 ->
    lvar s0 = lvar s0' ->
    lvar s1 = lvar s1' ->
    lock_protocol lvar tid s0' s1'.
Proof.
  unfold lock_protocol; intros.
  inversion H; subst; eauto.
Qed.

Inductive ghost_lock_invariant :
  BusyFlag -> BusyFlagOwner -> Prop :=
| LockOpen : ghost_lock_invariant Open NoOwner
| LockOwned : forall tid, ghost_lock_invariant Locked (Owned tid).

Lemma ghost_lock_owned : forall lvar glvar tid,
    ghost_lock_invariant lvar glvar ->
    glvar = Owned tid ->
    lvar = Locked.
Proof.
  inversion 1; congruence.
Qed.

Lemma ghost_lock_free : forall lvar glvar,
    ghost_lock_invariant lvar glvar ->
    glvar = NoOwner ->
    lvar = Open.
Proof.
  inversion 1; congruence.
Qed.

Lemma mem_lock_owned : forall lvar glvar,
    ghost_lock_invariant lvar glvar ->
    lvar = Locked ->
    exists tid, glvar = Owned tid.
Proof.
  inversion 1; try congruence; eauto.
Qed.

Lemma mem_lock_free : forall lvar glvar,
    ghost_lock_invariant lvar glvar ->
    lvar = Open ->
    glvar = NoOwner.
Proof.
  inversion 1; congruence.
Qed.

Theorem lock_inv_still_held : forall lvar tid tid' s s',
  lock_protocol lvar tid' s s' ->
  tid <> tid' ->
  lvar s = Owned tid ->
  lvar s' = Owned tid.
Proof.
  inversion 1; congruence.
Qed.

End Locking.

Hint Resolve ghost_lock_owned
             lock_inv_still_held.
Hint Constructors lock_transition.