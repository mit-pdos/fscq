Require Import Mem.
Require Import Pred.
Require Import Morphisms.

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

  Definition act_or (a b : action) : action :=
    fun m1 m2 => a m1 m2 \/ b m1 m2.

  Definition act_emp := act_id_pred emp.
  Definition act_id_any := act_id_pred any.
  Definition act_any : action := fun _ _ => True.

  Definition act_impl (a b : action) : Prop :=
    forall m1 m2, a m1 m2 -> b m1 m2.
  Definition act_iff (a b : action) : Prop :=
    act_impl a b /\ act_impl b a.

  Definition stable (p : @pred AT AEQ V) (a : action) : Prop :=
    forall m1 m2, p m1 -> a m1 m2 -> p m2.

  Definition fence (i : @pred AT AEQ V) (a : action) : Prop :=
    act_impl (act_id_pred i) a /\
    act_impl a (act_bow i i) /\
    precise i.

End RGDef.

Arguments action {AT AEQ V}.
Arguments act_bow {AT AEQ V} _ _ _ _.
Arguments act_id_pred {AT AEQ V} _ _ _.
Arguments act_star {AT AEQ V} _ _ _ _.
Arguments act_exis {AT AEQ V T} _ _ _ _.
Arguments act_or {AT AEQ V} _ _ _ _.
Arguments act_emp {AT AEQ V} _ _.
Arguments act_id_any {AT AEQ V} _ _.
Arguments act_any {AT AEQ V} _ _.
Arguments act_impl {AT AEQ V} _ _.
Arguments act_iff {AT AEQ V} _ _.
Arguments stable {AT AEQ V} _ _.
Arguments fence {AT AEQ V} _ _.

Infix "*" := act_star : act_scope.
Bind Scope act_scope with action.
Delimit Scope act_scope with act.

Notation "p ~> q" := (act_bow p%pred q%pred) (at level 80) : act_scope.
Notation "[ p ]" := (act_id_pred p%pred) : act_scope.
Infix "\/" := act_or : act_scope.

Notation "a =a=> b" := (act_impl a%act b%act) (at level 90).
Notation "a <=a=> b" := (act_iff a%act b%act) (at level 90).
Notation "i |> a" := (fence i%pred a%act) (at level 90).

Section RGThm.

  Variable AT : Type.
  Variable AEQ : DecEq AT.
  Variable V : Type.

  Ltac act_unfold :=
    unfold fence, stable, act_emp, act_any, act_id_any,
           act_iff, act_impl, act_or, act_bow, act_id_pred, act_exis.

  Theorem act_impl_refl : forall (a : @action AT AEQ V),
    a =a=> a.
  Proof.
    act_unfold; intuition.
  Qed.

  Theorem act_impl_trans : forall (a b c : @action AT AEQ V),
    a =a=> b ->
    b =a=> c ->
    a =a=> c.
  Proof.
    act_unfold; intuition.
  Qed.

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

  Theorem act_id_any_eq_iff : forall (m1 m2 : @mem AT AEQ V),
    act_id_any m1 m2 <-> m1 = m2.
  Proof.
    act_unfold; intros; intuition.
    unfold any.
    auto.
  Qed.

  Theorem act_id_any_refl : forall (m : @mem AT AEQ V),
    act_id_any m m.
  Proof.
    intros.
    apply act_id_any_eq_iff; auto.
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

  Theorem act_bow_pimpl : forall (p p' q q' : @pred AT AEQ V),
    p =p=> p' ->
    q =p=> q' ->
    (p ~> q) =a=> (p' ~> q').
  Proof.
    act_unfold; intuition.
  Qed.

  Theorem act_or_bow_dist_l_1 : forall (p p' q : @pred AT AEQ V),
    (p \/ p') ~> q =a=> (p ~> q) \/ (p' ~> q).
  Proof.
    act_unfold; unfold or; intuition.
  Qed.

  Theorem act_or_bow_dist_l_2 : forall (p p' q : @pred AT AEQ V),
    (p ~> q) \/ (p' ~> q) =a=> (p \/ p') ~> q.
  Proof.
    act_unfold; unfold or; intuition.
  Qed.

  Theorem act_or_bow_dist_l : forall (p p' q : @pred AT AEQ V),
    (p \/ p') ~> q <=a=> (p ~> q) \/ (p' ~> q).
  Proof.
    split.
    apply act_or_bow_dist_l_1.
    apply act_or_bow_dist_l_2.
  Qed.

  Theorem act_or_bow_dist_r_1 : forall (p q q' : @pred AT AEQ V),
    p ~> (q \/ q') =a=> (p ~> q) \/ (p ~> q').
  Proof.
    act_unfold; unfold or; intuition.
  Qed.

  Theorem act_or_bow_dist_r_2 : forall (p q q' : @pred AT AEQ V),
    (p ~> q) \/ (p ~> q') =a=> p ~> (q \/ q').
  Proof.
    act_unfold; unfold or; intuition.
  Qed.

  Theorem act_or_bow_dist_r : forall (p q q' : @pred AT AEQ V),
    p ~> (q \/ q') <=a=> (p ~> q) \/ (p ~> q').
  Proof.
    split.
    apply act_or_bow_dist_r_1.
    apply act_or_bow_dist_r_2.
  Qed.

  Example lrg_lemma_5_4_a : forall (p q r : @pred AT AEQ V),
    stable r (p ~> q) <-> ((p --* r) /\ emp) * q =p=> r.
  Proof.
    split.
    - act_unfold; unfold_sep_star; unfold pimpl, and, septract; intros.
      repeat deex.
      apply emp_empty_mem_only in H5; subst.
      rewrite mem_union_empty_mem in *.
      eapply H; eauto.
    - act_unfold; unfold_sep_star; unfold pimpl, and, septract; intros.
      eapply H.
      exists empty_mem.
      exists m2.
      intuition.
      exists m1.
      rewrite mem_union_empty_mem.
      intuition.
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

  Theorem fenced_id_pred : forall (i : @pred AT AEQ V),
    precise i -> i |> [i].
  Proof.
    act_unfold; intuition congruence.
  Qed.

  Theorem fenced_bow : forall (i : @pred AT AEQ V),
    precise i -> i |> (i ~> i).
  Proof.
    act_unfold; intuition congruence.
  Qed.

  Theorem fenced_or : forall (i : @pred AT AEQ V) a b,
    i |> a ->
    i |> b ->
    i |> a \/ b.
  Proof.
    act_unfold; intuition.
    apply H0 in H6; intuition.
    apply H0 in H6; intuition.
    apply H2 in H6; intuition.
    apply H2 in H6; intuition.
  Qed.

  Lemma fence_action_l : forall (i : @pred AT AEQ V) a m1 m2,
    i |> a ->
    a m1 m2 ->
    i m1.
  Proof.
    act_unfold; intuition.
    apply H in H0.
    intuition.
  Qed.

  Lemma fence_action_r : forall (i : @pred AT AEQ V) a m1 m2,
    i |> a ->
    a m1 m2 ->
    i m2.
  Proof.
    act_unfold; intuition.
    apply H in H0.
    intuition.
  Qed.

  Hint Resolve sep_star_precise.

  Theorem fenced_star : forall (i j : @pred AT AEQ V) a b,
    i |> a ->
    j |> b ->
    i * j |> a * b.
  Proof.
    act_unfold; intuition;
      unfold sep_star in *; rewrite sep_star_is in *; unfold sep_star_impl in *;
      unfold act_star in *;
      repeat deex.
    - do 4 eexists.
      split; eauto.
      split; eauto.
    - do 2 eexists.
      edestruct H0; eauto.
      edestruct H2; eauto.
    - do 2 eexists.
      edestruct H0; eauto.
      edestruct H2; eauto.
  Qed.

  Example lrg_lemma_5_8 : forall (a a' : @action AT AEQ V)
      (i : @pred AT AEQ V) m1 m2 m',
    mem_disjoint m1 m2 ->
    (a * a')%act (mem_union m1 m2) m' ->
    i m1 ->
    i |> a ->
    exists ! m1' m2', mem_disjoint m1' m2' /\ m' = mem_union m1' m2' /\
                      a m1 m1' /\ a' m2 m2'.
  Proof.
    unfold act_star; intros; repeat deex.
    inversion H2.
    inversion H8; clear H8.
    unfold precise in H10.
    assert (m1a = m1).
    eapply H10; eauto.
    eapply fence_action_l; eauto.
    subst.
    assert (m1b = m2).
    eapply mem_disjoint_union_cancel; eauto.
    subst.
    eexists; split; [eexists; split |]; [|intros|intros].
    (* the automation gets a little too excited with the default
       intuition auto with *. *)
    intuition idtac.
    auto.
    intuition.
    eapply mem_disjoint_union_cancel; eauto.
    inversion H8 as [m2' ?].
    inversion H11; clear H11.
    inversion H12; clear H12.
    inversion H14; clear H14.
    inversion H15; clear H15.
    eapply H10; eauto.
    eapply fence_action_r; eauto.
    eapply fence_action_r; eauto.
  Qed.

  Example lrg_corollary_5_9 : forall (a : @action AT AEQ V) (i : @pred AT AEQ V) m1 m2 m',
    mem_disjoint m1 m2 ->
    (a * act_id_any)%act (mem_union m1 m2) m' ->
    i m1 ->
    i |> a ->
    exists m1', mem_disjoint m1' m2 /\
      m' = mem_union m1' m2 /\
      a m1 m1'.
  Proof.
    intros.
    assert (Hlemma := lrg_lemma_5_8 H H0 H1 H2).
    apply exists_unique_incl_exists in Hlemma.
    inversion Hlemma.
    exists x.
    inversion H3.
    inversion H4.
    intuition.
    apply act_id_any_eq_iff in H10.
    subst m2; auto.
    apply act_id_any_eq_iff in H10.
    subst m2; auto.
  Qed.

  Example lrg_lemma_5_10 : forall (p p' : @pred AT AEQ V) a a' i,
    stable p a ->
    stable p' a' ->
    p =p=> i ->
    i |> a ->
    stable (p*p') (a*a').
  Proof.
    act_unfold; unfold pimpl; unfold_sep_star; unfold act_star; unfold precise; intros.
    repeat deex.
    exists m2a.
    exists m2b.
    (* re-fold fence *)
    assert (i |> a).
    act_unfold; auto.
    assert (m1a = m1).
    eapply H7; eauto.
    eapply fence_action_l; eauto.
    subst.
    assert (m1b = m2).
    eapply mem_disjoint_union_cancel; eauto.
    subst.
    intuition eauto.
  Qed.

End RGThm.

Hint Resolve act_impl_refl.

(** Some morphism instances for <=a=>.

Enables some rewriting, though more instances might be needed in other
circumstances. *)

Instance act_iff_impl_subrelation {AT AEQ V} :
  subrelation (@act_iff AT AEQ V) (@act_impl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance act_iff_equiv {AT AEQ V} :
  Equivalence (@act_iff AT AEQ V).
Proof.
  firstorder.
Qed.

Instance act_iff_proper {AT AEQ V} :
  Proper (act_iff ==> act_iff ==> Basics.flip Basics.impl) (@act_impl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance act_impl_impl_proper1 {AT AEQ V} :
  Proper (act_impl ==> Basics.flip act_impl ==> Basics.flip Basics.impl) (@act_impl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance act_impl_impl_proper2 {AT AEQ V} :
  Proper (Basics.flip act_impl ==> act_impl ==> Basics.impl) (@act_impl AT AEQ V).
Proof.
  firstorder.
Qed.

Lemma act_ptsto_stable_under_id : forall AT AEQ V a v,
  @stable AT AEQ V (a |-> v)%pred (act_id_pred (a |->?)).
Proof.
  unfold act_id_pred, stable.
  intuition congruence.
Qed.

Lemma act_star_stable_invariants : forall AT AEQ V F1 F2 p q,
  F1 =a=> p ~> p ->
  F2 =a=> q ~> q ->
  @stable AT AEQ V (p*q) (F1*F2).
Proof.
  unfold_sep_star; unfold stable.
  intros.
  unfold act_impl in *.
  unfold act_star in *.
  repeat deex.
  repeat match goal with
  | [ Himpl: context[?F _ _ -> _], H: ?F _ _ |- _ ] => apply Himpl in H
  end.
  unfold act_bow in *.
  do 2 eexists; intuition eauto.
Qed.

Section Coprecise.

Definition coprecise_l AT AEQ V (p: @pred AT AEQ V) (F: action) :=
  forall m1 m2 m1' m m',
  F m1 m2 ->
  p m1' ->
  mem_disjoint m1 m ->
  mem_disjoint m1' m' ->
  mem_union m1 m = mem_union m1' m' ->
  m1 = m1'.

Example ptsto_coprecise : forall AT AEQ V a v,
  @coprecise_l AT AEQ V (a |-> v) (act_id_pred (a |->?)).
Proof.
  intros.
  unfold coprecise_l.
  unfold act_id_pred.
  intros.
  intuition.
  subst m2.
  assert ((a |->?)%pred m1').
  eexists; eauto.
  eapply (@ptsto_any_precise AT AEQ V a); eauto.
Qed.

Definition preserves AT AEQ V F (p: @pred AT AEQ V) :=
  coprecise_l p F /\ stable p F.

Example ptsto_preserves : forall AT AEQ V a v,
  @preserves AT AEQ V (act_id_pred (a |->?)) (a |-> v).
Proof.
  intros.
  split.
  apply ptsto_coprecise.
  unfold stable.
  apply act_ptsto_stable_under_id.
Qed.

Theorem act_impl_preserves_invariant : forall AT AEQ V F p,
  F =a=> p ~> p ->
  precise p ->
  @preserves AT AEQ V F p.
Proof.
  unfold act_bow, preserves, coprecise_l, stable.
  intros.
  split; intros; match goal with
  | [ H : ?F =a=> _, H' : ?F _ _  |- _] => apply H in H'
  end; intuition.

  (* coprecise_l *)
  eapply H0; eauto.
Qed.

Lemma disjoint_union_comm_eq : forall AT AEQ V
  (m1a m1b m2a m2b : @mem AT AEQ V),
  mem_union m1a m1b = mem_union m2a m2b ->
  mem_disjoint m1a m1b ->
  mem_disjoint m2a m2b ->
  mem_union m1b m1a = mem_union m2b m2a.
Proof.
  intros.
  rewrite mem_union_comm with (m1 := m1b).
  rewrite mem_union_comm with (m1 := m2b).
  auto.
  rewrite mem_disjoint_comm; auto.
  rewrite mem_disjoint_comm; auto.
Qed.

(* TODO: make this more general and use it in Pred.v *)
Ltac solve_disjoint_union :=
  match goal with
  | [ |- mem_disjoint _ _ ] =>
     now ( eauto ||rewrite mem_disjoint_comm; eauto)
  | [ H: mem_union ?m1a ?m1b = mem_union ?m2a ?m2b |-
        mem_union ?m1b ?m1a = mem_union ?m2b ?m2a ] =>
    now (apply disjoint_union_comm_eq; eauto)
  end.

Lemma act_star_stable_invariant_preserves : forall AT AEQ V
  F1 F2 p q (m1 m2: @mem AT AEQ V),
  F1 =a=> p ~> p ->
  preserves F2 q ->
  @stable AT AEQ V (p * q) (F1*F2).
Proof.
  unfold_sep_star; unfold act_impl, act_star.
  unfold preserves, stable.
  intros.
  repeat deex.
  match goal with
  | [ Hcoprec: context[coprecise_l ?p ?F],
        H: ?F ?m1 _, H': ?p ?m1' |- _ ] =>
        assert (m1 = m1') by (eapply Hcoprec; eauto; solve_disjoint_union)
  end.
  subst.
  do 2 eexists; intuition eauto.
  eapply H; eauto.
Qed.

End Coprecise.

Lemma act_id_dist_star : forall AT AEQ V (p q: @pred AT AEQ V),
  act_id_pred (p * q) =a=> act_id_pred p * act_id_pred q.
Proof.
  unfold act_id_pred, act_impl, act_star.
  unfold_sep_star.
  intros.
  intuition.
  repeat deex.
  repeat eexists; eauto.
Qed.

Lemma act_id_dist_star_frame : forall AT AEQ V F (p q: @pred AT AEQ V),
  F * act_id_pred (p * q) =a=> F * act_id_pred p * act_id_pred q.
Proof.
  intros.
  rewrite act_star_assoc.
  apply act_impl_star; auto.
  apply act_id_dist_star.
Qed.
