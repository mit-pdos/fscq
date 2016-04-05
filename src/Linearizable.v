Require Import Mem.
Require Import Pred.
Require Import Locking.
Require Import EventCSL.
Require Import FunctionalExtensionality.
Import Morphisms.

Section Linearizability.

  Variable A:Type.
  Variable AEQ:DecEq A.
  Variable V:A -> Type.

  Definition A':Type := A * BusyFlagOwner.
  Definition AEQ' : DecEq A'.
  Proof.
    unfold DecEq.
    decide equality.
    decide equality.
    decide equality.
  Defined.

  Definition V' : A' -> Type := fun ao =>
                                 V (fst ao).

  Definition linear_mem := @mem A' AEQ' V'.

  Definition view owner (m: linear_mem) : @mem A AEQ V :=
    fun a => m (a, owner).

  Definition lin_pred owner (F: @pred A AEQ V) : @pred A' AEQ' V' :=
    fun m => F (view owner m).

  Theorem lin_pred_star : forall (F1 F2: @pred A AEQ V) owner,
    lin_pred owner (F1 * F2) <=p=> lin_pred owner F1 * lin_pred owner F2.
  Proof.
    unfold lin_pred.
    split; unfold pimpl; intros.
    - unfold_sep_star in H.
      unfold_sep_star; repeat deex.
      exists (fun a =>
        if (BusyFlagOwner_dec (snd a) owner) then
        (if m1 (fst a) then m a else None) else
        m a).
      exists (fun a =>
        if (BusyFlagOwner_dec (snd a) owner) then
        (if m2 (fst a) then m a else None) else
        None).
      intuition.

      unfold mem_union in *.
      extensionality a.
      destruct a; cbn.
      apply equal_f_dep with a in H0.
      unfold view in H0.
      destruct (BusyFlagOwner_dec b owner); subst.
      destruct (m1 a).
      rewrite H0; auto.
      rewrite H0.
      destruct (m2 a); auto.
      destruct (m (a, b)); auto.

      unfold mem_disjoint; intro; repeat deex.
      destruct a; cbn in *.
      destruct (BusyFlagOwner_dec b owner); subst; try congruence.
      let H := fresh in
      let H' := fresh in
      destruct (m1 a) eqn:H; destruct (m2 a) eqn:H';
        try congruence.
      eapply H; eauto.

      match goal with
      | [ |- F1 ?m ] => assert (m = m1)
      end.
      extensionality a.
      unfold view; cbn.
      destruct (BusyFlagOwner_dec owner owner); try congruence.
      apply equal_f_dep with a in H0.
      unfold view, mem_union in H0.
      let H := fresh in
      destruct (m1 a) eqn:H; auto.
      congruence.

      match goal with
      | [ |- F2 ?m ] => assert (m = m2)
      end.
      extensionality a.
      rewrite mem_union_comm in H0; auto.
      unfold view; cbn.
      destruct (BusyFlagOwner_dec owner owner); try congruence.
      apply equal_f_dep with a in H0.
      unfold view, mem_union in H0.
      let H := fresh in
      destruct (m2 a) eqn:H; auto.
      congruence.
    - unfold_sep_star in H.
      unfold_sep_star.
      repeat deex.
      exists (view owner m1), (view owner m2).
      intuition.
      unfold mem_disjoint, view in *.
      intro; repeat deex.
      apply H.
      exists (a, owner), v1, v2; intuition.
  Qed.

End Linearizability.

Instance lin_pred_pimpl : forall A AEQ V owner,
  Proper (pimpl ==> pimpl) (@lin_pred A AEQ V owner).
Proof.
  firstorder.
Qed.

Instance lin_pred_piff : forall A AEQ V owner,
  Proper (piff ==> piff) (@lin_pred A AEQ V owner).
Proof.
  firstorder.
Qed.

(* specialize to DISK to help typeclass search *)
Instance lin_pred_piff_disk_respectful : forall owner,
  Proper (piff ==> piff) (@lin_pred addr (@weq addrlen) (const wr_set) owner).
Proof.
  firstorder.
Qed.

Instance A'_dec : forall A `(DecEq A), DecEq (A' A).
Proof.
  unfold DecEq; intros.
  decide equality.
  decide equality.
  decide equality.
Defined.

Arguments linear_mem {A AEQ V}.

  Notation "'linearized' mt" :=
    ltac:(
      match mt with
      | @mem ?AT ?AEQ ?V =>
        exact (@linear_mem AT AEQ V)
      | _ => match eval unfold mt in mt with
        | @mem ?AT ?AEQ ?V =>
          exact (@linear_mem AT AEQ V)
        end
      | _ => idtac "linearized" mt "failed; not a mem"
      end) (at level 50, only parsing).

Definition linearized_consistent A AEQ V (m: @linear_mem A AEQ V) (locks: _ -> BusyFlagOwner) : Prop :=
  forall a, match locks a with
       | Owned tid => forall tid',
           tid <> tid' ->
           m (a, Owned tid') = m (a, NoOwner)
       | NoOwner => forall tid,
           m (a, Owned tid) = m (a, NoOwner)
       end.

Theorem linearized_consistent_upd : forall A AEQ V (m: @linear_mem A AEQ V)
  locks tid a v,
    locks a = Owned tid ->
    linearized_consistent m locks ->
    linearized_consistent (upd m (a, Owned tid) v) locks.
Proof.
  Ltac upd_different :=
    match goal with
    | [ |- context[upd _ ?a _ ?a'] ] =>
      assert (a <> a') by (inversion 1; congruence);
        autorewrite with upd
    end.
  unfold linearized_consistent; intros.
  specialize (H0 a0).
  destruct (AEQ a a0); subst.
  rewrite H; intros.
  repeat upd_different.
  rewrite H in H0.
  eauto.

  destruct (locks a0); intros;
    repeat upd_different;
    eauto.
Qed.

Definition linear_rel A AEQ V tid (locks locks': A -> BusyFlagOwner)
  (m m': @linear_mem A AEQ V) :=
  forall a, (locks a <> Owned tid ->
    forall o, m' (a, o) = m (a, o)) /\
  (locks a = Owned tid ->
  locks' a = Owned tid ->
    m' (a, NoOwner) = m (a, NoOwner)) /\
  (forall tid', tid <> tid' ->
    (m' (a, Owned tid') = m (a, Owned tid'))) /\
  (locks a = Owned tid ->
    locks' a = NoOwner ->
    forall o, m' (a, o) = m (a, NoOwner)).

Require Import Automation ForwardChaining.

Ltac specialize_t t :=
  repeat match goal with
  | [ H: forall (_:t), _, x:t |- _ ] =>
    specialize (H x)
  end.

Ltac learn_all_t t :=
  repeat match goal with
  | [ H: forall (_:t), _, x:t |- _ ] =>
    learn that (H x)
  end.

Theorem linear_rel_preserves_consistency : forall A AEQ V tid
  (locks locks': A -> BusyFlagOwner) (m m': @linear_mem A AEQ V),
  linearized_consistent m locks ->
  (forall a, lock_transition tid (locks a) (locks' a)) ->
  linear_rel tid locks locks' m m' ->
  linearized_consistent m' locks'.
Proof.
  unfold linearized_consistent, linear_rel; intros.
  specialize_t A.
  intuition.
  inversion H0; subst; repeat simpl_match; intros.
  - replace (locks a) in *.
    let H := fresh in
    destruct (locks' a) eqn:H; intros.
    intuition (try congruence).
    learn_all_t ID;
    repeat match goal with
    | [ H: (?a = ?a -> False) -> _ |- _ ] => clear H
    end.
    destruct (PeanoNat.Nat.eq_dec id tid);
      subst; intuition congruence.
  - replace (locks a) in *.
    replace (locks' a) in *.
    learn_all_t ID;
    repeat match goal with
    | [ H: (?a = ?a -> False) -> _ |- _ ] => clear H
    end.
    intuition congruence.
  - replace (locks a) in *.
    replace (locks' a) in *.
    learn_all_t ID;
    repeat match goal with
    | [ H: (?a = ?a -> False) -> _ |- _ ] => clear H
    end.
    intuition congruence.
Qed.

Local Definition linearized_consistent' A AEQ V (m: @linear_mem A AEQ V) (locks: A -> BusyFlagOwner) : Prop :=
  forall a tid,
  locks a <> Owned tid ->
  m (a, Owned tid) = m (a, NoOwner).

Local Theorem linearized_consistent'_equivalent : forall A AEQ V (m: @linear_mem A AEQ V) locks,
    linearized_consistent m locks <-> linearized_consistent' m locks.
Proof.
  unfold linearized_consistent, linearized_consistent';
  split; intros;
  specialize (H a).
  - destruct (locks a); eauto.
  - destruct (locks a); intros; eauto.
    eapply H; congruence.
    eapply H; congruence.
Qed.