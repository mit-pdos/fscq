Require Import Mem.
Require Import ListUtils.
Require Import List Omega Ring Word Pred PredCrash.
Require Import Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.
Require Import WordAuto.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Fixpoint arrayN {V : Type} (a : addr) (vs : list V) : @pred _ addr_eq_dec _ :=
  match vs with
    | nil => emp
    | v :: vs' => a |-> v * arrayN (S a) vs'
  end%pred.

Fixpoint arrays {V : Type} (a : addr) (vs_list : list (list V)) : @pred _ addr_eq_dec _ :=
  match vs_list with
  | nil => emp
  | vs :: l' => arrayN (a + length vs) l'
  end.

Lemma arrayN_unify : forall A (a b : list A) s,
  a = b -> arrayN s a =p=> arrayN s b.
Proof.
  intros; subst; auto.
Qed.

Lemma isolateN_fwd' : forall V vs i a (default : V),
  i < length vs
  -> arrayN a vs =p=> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i default
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 + 0) with (a0) by omega.
  replace (a0 + 1) with (S a0) by omega.
  cancel.

  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] | ]; clear IHvs.
  instantiate (1 := i); omega.
  simpl.
  replace (S (a0 + i)) with (a0 + S i) by omega.
  replace (S (a0 + i + 1)) with (a0 + S i + 1) by omega.
  cancel.
Qed.

Theorem isolateN_fwd : forall V (default : V) a i vs,
  i < length vs
  -> arrayN a vs =p=> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i default
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  intros.
  eapply pimpl_trans; [ apply isolateN_fwd' | ].
  eassumption.
  apply pimpl_refl.
Qed.

Lemma isolateN_bwd' : forall V vs i a (default : V),
  i < length vs
  -> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i default
     * arrayN (a + i + 1) (skipn (S i) vs)
  =p=> arrayN a vs.
Proof.
  induction vs; simpl; intuition.

  inversion H.

  destruct i; simpl.

  replace (a0 + 0) with (a0) by omega.
  replace (a0 + 1) with (S a0) by omega.
  cancel.

  eapply pimpl_trans; [ | apply pimpl_sep_star; [ apply pimpl_refl | apply IHvs ] ]; clear IHvs.
  2: instantiate (1 := i); omega.
  simpl.
  replace (a0 + S i) with (S (a0 + i)) by omega.
  cancel.
Qed.

Theorem isolateN_bwd : forall V (default : V) a i vs,
  i < length vs
  -> arrayN a (firstn i vs)
     * (a + i) |-> selN vs i default
     * arrayN (a + i + 1) (skipn (S i) vs)
  =p=> arrayN a vs.
Proof.
  intros.
  eapply pimpl_trans; [ | apply isolateN_bwd' ].
  2: eassumption.
  apply pimpl_refl.
Qed.

Theorem arrayN_isolate : forall V (default : V) a i vs,
  i < length vs
  -> arrayN a vs <=p=>
     arrayN a (firstn i vs)
     * (a + i) |-> selN vs i default
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  unfold piff; split.
  apply isolateN_fwd; auto.
  apply isolateN_bwd; auto.
Qed.

Theorem isolate_fwd_upd : forall V (v : V) a i vs,
  i < length vs
  -> arrayN a (updN vs i v) <=p=>
     arrayN a (firstn i vs)
     * (a + i) |-> v
     * arrayN (a + i + 1) (skipn (S i) vs).
Proof.
  intros.
  erewrite arrayN_isolate with (vs:=updN vs i v) (i:=i) (default:=v);
    autorewrite with lists; auto.
  unfold piff; split.
  cancel; autorewrite with lists; cancel.
  cancel; autorewrite with lists; cancel.
Qed.

Theorem isolateN_bwd_upd : forall V (v : V) a i vs,
  i < length vs
  -> arrayN a (firstn i vs)
     * (a + i) |-> v
     * arrayN (a + i + 1) (skipn (S i) vs)
     =p=> arrayN a (updN vs i v).
Proof.
  intros.
  erewrite <- isolateN_bwd with (vs:=updN vs i v) (i:=i) (default:=v).
  rewrite selN_updN_eq by auto.
  rewrite firstn_updN_oob by auto.
  rewrite skipN_updN' by auto.
  cancel.
  rewrite length_updN.
  auto.
Qed.

Lemma arrayN_oob': forall A (l : list A) a i m,
  i >= length l
  -> arrayN a l m
  -> m (a + i) = None.
Proof.
  induction l; intros; auto; simpl in *.
  destruct (eq_nat_dec i 0); auto.
  subst; simpl in *; omega.

  unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
  repeat deex.
  unfold mem_union.
  unfold ptsto in H2; destruct H2; rewrite H2.
  pose proof (IHl (S a0) (i - 1)).
  replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
  apply H3; try omega.

  auto.
  omega.
Qed.

Lemma arrayN_oob: forall A (l : list A) i m,
  i >= length l
  -> arrayN 0 l m
  -> m i = None.
Proof.
  intros.
  replace i with (0 + i) by omega.
  eapply arrayN_oob'; eauto.
Qed.

Lemma emp_star_r: forall AT AEQ V (F:@pred AT AEQ V),
  F =p=> (F * emp)%pred.
Proof.
  intros.
  rewrite sep_star_comm.
  apply emp_star.
Qed.

Lemma arrayN_app_memupd : forall V l (v : V) m,
  arrayN 0 l m
  -> arrayN 0 (l ++ v :: nil) (Mem.upd m (length l) v).
Proof.
  intros.

  eapply isolateN_bwd with (i := (length l)) (default := v).
  rewrite app_length; simpl; omega.

  rewrite firstn_app; auto.
  rewrite selN_last; auto.
  rewrite skipn_oob; [ | rewrite app_length; simpl; omega ].
  unfold arrayN at 2; auto; apply emp_star_r.
  simpl.

  apply ptsto_upd_disjoint; auto.
  eapply arrayN_oob; eauto.
Qed.


Theorem arrayN_list_eq : forall A (vs1 vs2 : list A) s m,
  arrayN s vs1 m -> arrayN s vs2 m -> vs1 = vs2.
Proof.
  induction vs1; destruct vs2; simpl; intros; auto.
  apply ptsto_valid in H0; congruence.
  apply ptsto_valid in H; congruence.
  apply ptsto_valid in H as Hx.
  apply ptsto_valid in H0 as Hy.
  rewrite Hx in Hy; inversion Hy; subst; clear Hx Hy; f_equal.
  apply ptsto_mem_except in H.
  apply ptsto_mem_except in H0.
  eapply IHvs1; eauto.
Qed.


Definition vsupd (vs : list valuset) (i : addr) (v : valu) : list valuset :=
  updN vs i (v, vsmerge (selN vs i ($0, nil))).

Definition vssync (vs : list valuset) (i : addr) : list valuset :=
  updN vs i (fst (selN vs i ($0, nil)), nil).

Definition vsupd_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (map vsmerge (firstn n vsl))) ++ skipn n vsl.

Lemma vsupd_range_length : forall vsl l,
  length l <= length vsl ->
  length (vsupd_range vsl l) = length vsl.
Proof.
  unfold vsupd_range; intros.
  rewrite app_length.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  omega.
  rewrite map_length.
  rewrite firstn_length_l; auto.
Qed.

Lemma vsupd_range_nil : forall vsl,
  vsupd_range vsl nil = vsl.
Proof.
  unfold vsupd_range; intros.
  autorewrite with lists; simpl; auto.
Qed.

Lemma vsupd_range_progress : forall i vsl l,
  length l <= length vsl -> i < length l ->
    (vsupd (vsupd_range vsl (firstn i l)) i (selN l i $0))
  = (vsupd_range vsl ((firstn i l) ++ [ selN l i $0 ])).
Proof.
  unfold vsupd, vsmerge; intros.
  unfold vsupd_range.
  autorewrite with lists; simpl.
  repeat replace (length (firstn i l)) with i
    by (rewrite firstn_length_l by omega; auto).
  rewrite updN_app2.
  erewrite firstn_plusone_selN by omega.
  rewrite map_app.
  rewrite combine_app
    by (rewrite map_length; repeat rewrite firstn_length_l; omega).
  rewrite <- app_assoc; f_equal; simpl.
  rewrite combine_length; autorewrite with lists.
  rewrite Nat.min_l; repeat rewrite firstn_length_l; try omega.
  replace (i - i) with 0 by omega.
  rewrite updN_0_skip_1 by (rewrite skipn_length; omega).
  rewrite skipn_skipn'; f_equal; f_equal.
  rewrite selN_app2.
  rewrite combine_length; rewrite Nat.min_l;
     autorewrite with lists; repeat rewrite firstn_length_l; try omega.
  replace (i + (i - i)) with i by omega.
  unfold vsmerge; auto.
  all: rewrite combine_length_eq2; autorewrite with lists;
    repeat rewrite firstn_length_l; omega.
Qed.



Definition vssync_range (vsl : list valuset) n :=
  (List.combine (map fst (firstn n vsl)) (repeat nil n)) ++ skipn n vsl.

Lemma vssync_range_length : forall vsl n,
  n <= length vsl ->
  length (vssync_range vsl n) = length vsl.
Proof.
  unfold vssync_range; intros.
  autorewrite with lists.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  autorewrite with lists.
  rewrite firstn_length_l; omega.
  autorewrite with lists.
  rewrite firstn_length_l; omega.
Qed.

Lemma vssync_range_progress : forall vs m,
  m < length vs ->
  vssync (vssync_range vs m) m = vssync_range vs (S m).
Proof.
  unfold vssync, vssync_range; intros.
  rewrite updN_app2.
  erewrite firstn_S_selN by auto.
  rewrite map_app.
  rewrite repeat_app_tail.
  rewrite combine_app
    by (autorewrite with lists; rewrite firstn_length_l; omega).
  rewrite <- app_assoc; f_equal.
  rewrite combine_length; autorewrite with lists.
  rewrite Nat.min_l; repeat rewrite firstn_length_l; try omega.
  replace (m - m) with 0 by omega.
  rewrite updN_0_skip_1 by (rewrite skipn_length; omega).
  rewrite skipn_skipn; simpl.
  f_equal; f_equal.
  rewrite selN_app2.
  rewrite combine_length; rewrite Nat.min_l;
     autorewrite with lists; repeat rewrite firstn_length_l; try omega.
  replace (m + (m - m)) with m by omega.
  unfold vsmerge; auto.
  all: rewrite combine_length_eq2; autorewrite with lists;
    repeat rewrite firstn_length_l; omega.
Qed.

