Require Import EventCSL.

Set Implicit Arguments.

Section Locking.

Variable Mcontents : list Type.
Variable Scontents : list Type.

Inductive BusyFlagOwner : Set :=
| NoOwner
| Owned (id:ID).

(** given a lock variable and some other variable v, generate a
relation for tid that makes the variable read-only for non-owners. *)
Definition lock_protects (lvar : S Scontents -> BusyFlagOwner)
           {tv} (v : S Scontents -> tv) tid (s s': S Scontents) :=
  forall owner_tid,
    lvar s = Owned owner_tid ->
    tid <> owner_tid ->
    v s' = v s.

Inductive lock_protocol (lvar : S Scontents -> BusyFlagOwner) (tid : ID) :
  S Scontents -> S Scontents -> Prop :=
| NoChange : forall s s', lvar s  = lvar s' ->
                     lock_protocol lvar tid s s'
| OwnerRelease : forall s s', lvar s = Owned tid ->
                         lvar s' = NoOwner ->
                         lock_protocol lvar tid s s'
| OwnerAcquire : forall s s', lvar s = NoOwner ->
                         lvar s' = Owned tid ->
                         lock_protocol lvar tid s s'.

Hint Constructors lock_protocol.

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

Hint Extern 1 (_ = _) => congruence.

Theorem lock_protocol_trans : forall lvar tid s s' s'',
  lock_protocol lvar tid s s' ->
  lock_protocol lvar tid s' s'' ->
  lock_protocol lvar tid s s''.
Proof.
  intros.
  repeat match goal with
    | [ H: lock_protocol _ _ _ _ |- _ ] =>
      inversion H; subst; clear H
    end; eauto.
Qed.

Inductive ghost_lock_invariant
  (lvar: BusyFlag) (glvar: BusyFlagOwner) : Prop :=
| LockOpen : lvar = Open -> glvar = NoOwner ->
             ghost_lock_invariant lvar glvar
| LockOwned : forall tid, lvar = Locked -> glvar = Owned tid ->
                     ghost_lock_invariant lvar glvar.

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