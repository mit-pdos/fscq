Require Import Mem.
Require Import Pred.

Set Implicit Arguments.

(**
 * Rely-guarantee logic, based on the "Local Rely-Guarantee Reasoning" paper.
 * In particular, see Figures 6, 8, and 9.
 *)

Section RGDef.

  Variable AT : Type.
  Variable AEQ : DecEq AT.
  Variable V : Type.

  Definition action := @mem AT AEQ V -> @mem AT AEQ V -> Prop.

  Definition act_bow (p q : @pred AT AEQ V) : action :=
    fun m1 m2 => p m1 /\ q m2.

  Definition act_id_pred (p : @pred AT AEQ V) : action :=
    fun m1 m2 => p m1 /\ m1 = m2.

  Definition act_star (a b : action) : action :=
    fun m1 m2 => exists m1a m1b m2a m2b,
      a m1a m2a /\ b m1b m2b /\
      mem_disjoint m1a m1b /\ m1 = mem_union m1a m1b /\
      mem_disjoint m2a m2b /\ m2 = mem_union m2a m2b.

  Definition act_exis {T} (x : T) (a : T -> action) : action :=
    fun m1 m2 => exists x, (a x) m1 m2.

  Definition act_emp := act_id_pred emp.
  Definition act_id_any := act_id_pred any.
  Definition act_any : action := fun _ _ => True.

  Definition act_impl (a b : action) : Prop :=
    forall m1 m2, a m1 m2 -> b m1 m2.
  Definition act_iff (a b : action) : Prop :=
    act_impl a b /\ act_impl b a.

  Definition stable (p : @pred AT AEQ V) (a : action) : Prop :=
    forall m1 m2, p m1 -> a m1 m2 -> p m2.

End RGDef.

Arguments action {AT AEQ V}.
Arguments act_bow {AT AEQ V} _ _ _ _.
Arguments act_id_pred {AT AEQ V} _ _ _.
Arguments act_star {AT AEQ V} _ _ _ _.
Arguments act_exis {AT AEQ V T} _ _ _ _.
Arguments act_emp {AT AEQ V} _ _.
Arguments act_id_any {AT AEQ V} _ _.
Arguments act_any {AT AEQ V} _ _.
Arguments stable {AT AEQ V} _ _.

Infix "*" := act_star : act_scope.
Bind Scope act_scope with action.
Delimit Scope act_scope with act.

Notation "p ~> q" := (act_bow p%pred q%pred) (at level 80) : act_scope.
Notation "[ p ]" := (act_id_pred p%pred) : act_scope.

Notation "a =a=> b" := (act_impl a%act b%act) (at level 90).
Notation "a <=a=> b" := (act_iff a%act b%act) (at level 90).

Section RGThm.

  Variable AT : Type.
  Variable AEQ : DecEq AT.
  Variable V : Type.

  Ltac act_unfold :=
    unfold act_emp, act_any, act_id_any,
           act_iff, act_impl, act_bow, act_id_pred, act_exis.

  Theorem act_impl_id_bow : forall (p : @pred AT AEQ V),
    [p] =a=> p ~> p.
  Proof.
    act_unfold; intuition congruence.
  Qed.

  Theorem act_impl_id_pred_id_any : forall (p : @pred AT AEQ V),
    [p] =a=> act_id_any.
  Proof.
    act_unfold; unfold any; intuition.
  Qed.

  Theorem act_impl_any : forall (a : @action AT AEQ V),
    a =a=> act_any.
  Proof.
    act_unfold; intuition.
  Qed.

  Theorem act_star_comm' : forall (a b : @action AT AEQ V),
    a * b =a=> b * a.
  Proof.
    act_unfold; unfold act_star; intros.
    repeat deex.
    do 4 eexists.
    apply mem_disjoint_comm in H1 as H1'.
    apply mem_disjoint_comm in H3 as H3'.
    split; eauto.
    split; eauto.
    intuition; rewrite mem_union_comm; auto.
  Qed.

  Theorem act_star_comm : forall (a b : @action AT AEQ V),
    a * b <=a=> b * a.
  Proof.
    split; apply act_star_comm'.
  Qed.

  Hint Resolve mem_disjoint_assoc_1.
  Hint Resolve mem_disjoint_assoc_2.
  Hint Resolve mem_union_assoc.
  Hint Resolve mem_disjoint_union.
  Hint Resolve mem_disjoint_union_2.

  Theorem act_star_assoc_1 : forall (a b c : @action AT AEQ V),
    a * b * c =a=> a * (b * c).
  Proof.
    act_unfold; unfold act_star; intros.
    repeat deex.
    do 4 eexists.
    split; eauto.
    split.
    do 4 eexists.
    intuition eauto.
    intuition eauto.
  Qed.

  Theorem act_star_assoc_2 : forall (a b c : @action AT AEQ V),
    a * (b * c) =a=> a * b * c.
  Proof.
    act_unfold; unfold act_star; intros.
    repeat deex.
    do 4 eexists.
    split.
    do 4 eexists.
    split; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    intuition eauto.
    rewrite mem_union_assoc by eauto. auto.
    rewrite mem_union_assoc by eauto. auto.
  Qed.

  Theorem act_star_assoc : forall (a b c : @action AT AEQ V),
    a * b * c <=a=> a * (b * c).
  Proof.
    split.
    apply act_star_assoc_1.
    apply act_star_assoc_2.
  Qed.

  Hint Resolve emp_empty_mem.
  Hint Resolve mem_disjoint_empty_mem.

  Theorem act_star_emp : forall (a : @action AT AEQ V),
    act_emp * a <=a=> a.
  Proof.
    act_unfold; unfold act_star; split; intros.
    - repeat deex.
      apply emp_empty_mem_only in H; subst.
      repeat rewrite mem_union_empty_mem.
      auto.
    - exists empty_mem. exists m1. exists empty_mem. exists m2.
      intuition eauto.
  Qed.

  Theorem act_impl_star : forall (a a' b b' : @action AT AEQ V),
    a =a=> a' ->
    b =a=> b' ->
    a * b =a=> a' * b'.
  Proof.
    act_unfold; unfold act_star; intros.
    repeat deex.
    do 4 eexists.
    intuition eauto.
  Qed.

  Theorem act_impl_bow : forall (p p' q q' : @pred AT AEQ V),
    p =p=> p' ->
    q =p=> q' ->
    p ~> q =a=> p' ~> q'.
  Proof.
    act_unfold; intuition.
  Qed.

  Theorem act_bow_star_dist' : forall (p p' q q' : @pred AT AEQ V),
    (p * q) ~> (p' * q') =a=> (p ~> p') * (q ~> q').
  Proof.
    act_unfold; unfold act_star; unfold_sep_star; intros.
    intuition; repeat deex.
    do 4 eexists.
    intuition eauto.
  Qed.

  Theorem act_star_bow_dist' : forall (p p' q q' : @pred AT AEQ V),
    (p ~> p') * (q ~> q') =a=> (p * q) ~> (p' * q').
  Proof.
    act_unfold; unfold act_star; unfold_sep_star; intros.
    repeat deex; do 2 eexists; intuition eauto.
  Qed.

  Theorem act_star_bow : forall (p p' q q' : @pred AT AEQ V),
    (p * q) ~> (p' * q') <=a=> (p ~> p') * (q ~> q').
  Proof.
    split.
    apply act_bow_star_dist'.
    apply act_star_bow_dist'.
  Qed.

  Example lrg_lemma_5_4_b : forall (p q r : @pred AT AEQ V),
    (p --* r) * q =p=> r ->
    stable r ((p ~> q) * act_id_any)%act.
    (**
     * XXX had to add "* act_id_any" since our separation logic always fully
     * specifies every memory; there's no implicit frame.
     *)
  Proof.
    unfold stable, septract. act_unfold. unfold act_star. unfold_sep_star. intros.
    repeat deex.
    apply H.
    exists m2b. exists m2a.
    intuition eauto.
    rewrite mem_union_comm; auto.
    apply mem_disjoint_comm; auto.
    exists m1a.
    intuition.
    apply mem_disjoint_comm; auto.
    rewrite mem_union_comm; auto.
    apply mem_disjoint_comm; auto.
  Qed.

  Example lrg_lemma_5_4_c : forall (p q r : @pred AT AEQ V),
    stable r ((p ~> q) * act_id_any)%act ->
    (p --* r) * q =p=> r.
  Proof.
    unfold stable, septract, pimpl. act_unfold. unfold act_star. unfold_sep_star. intros.
    repeat deex.
    eapply H.
    eauto.
    do 4 eexists.
    split; eauto.
    split. unfold any; eauto.
    split. apply mem_disjoint_comm; eauto.
    intuition.
    rewrite mem_union_comm; auto.
    apply mem_disjoint_comm; auto.
    rewrite mem_union_comm; auto.
  Qed.

End RGThm.
