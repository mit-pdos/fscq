Require Import Mem.
Require Import ListUtils.
Require Import List Omega Ring Word Pred PredCrash.
Require Import Prog Hoare SepAuto BasicProg.
Require Import FunctionalExtensionality.
Require Import WordAuto.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.
Set Default Proof Using "Type".


(** * A generic array predicate: a sequence of consecutive points-to facts *)

Section GenArray.

  Variable V : Type.
  Variable pts : addr -> V -> @pred addr addr_eq_dec V.

  Infix "|-?->" := pts (at level 35) : pred_scope.

  Fixpoint arrayN (a : addr) (vs : list V) : @pred _ addr_eq_dec _ :=
    match vs with
      | nil => emp
      | v :: vs' => a |-?-> v * arrayN (S a) vs'
    end%pred.

  Lemma arrayN_unify : forall (a b : list V) s,
    a = b -> arrayN s a =p=> arrayN s b.
  Proof.
    intros; subst; auto.
  Qed.

  Lemma arrayN_one: forall v,
      0 |-?-> v <=p=> arrayN 0 [v].
  Proof.
    split; cancel.
  Qed.

  Lemma isolateN_fwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
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

  Theorem isolateN_fwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs =p=> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    intros.
    eapply pimpl_trans; [ apply isolateN_fwd' | ].
    eassumption.
    apply pimpl_refl.
  Qed.

  Lemma isolateN_bwd' : forall vs i a (default : V),
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
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

  Theorem isolateN_bwd : forall (default : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs)
    =p=> arrayN a vs.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply isolateN_bwd' ].
    2: eassumption.
    apply pimpl_refl.
  Qed.

  Theorem arrayN_isolate : forall (default : V) a i vs,
    i < length vs
    -> arrayN a vs <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> selN vs i default
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    unfold piff; split.
    apply isolateN_fwd; auto.
    apply isolateN_bwd; auto.
  Qed.

  Theorem isolate_fwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (updN vs i v) <=p=>
       arrayN a (firstn i vs)
       * (a + i) |-?-> v
       * arrayN (a + i + 1) (skipn (S i) vs).
  Proof.
    intros.
    erewrite arrayN_isolate with (vs:=updN vs i v) (i:=i) (default:=v);
      autorewrite with lists; auto.
    unfold piff; split.
    cancel; autorewrite with lists; cancel.
    cancel; autorewrite with lists; cancel.
  Qed.

  Theorem isolateN_bwd_upd : forall (v : V) a i vs,
    i < length vs
    -> arrayN a (firstn i vs)
       * (a + i) |-?-> v
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

  Theorem arrayN_app : forall (a b : list V) st,
    arrayN st (a ++ b) <=p=>
    arrayN st a * arrayN (st + length a) b.
  Proof.
    induction a; split; simpl; auto.
    rewrite Nat.add_0_r; cancel.
    rewrite Nat.add_0_r; cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by omega.
    cancel.
    rewrite IHa.
    replace (S st + length a0) with (st + S (length a0)) by omega.
    cancel.
  Qed.

  Theorem arrayN_split : forall i (a : list V) st,
    arrayN st a <=p=>
    arrayN st (firstn i a) * arrayN (st + i) (skipn i a).
  Proof.
    intros.
    destruct (lt_dec i (length a)).
    erewrite arrayN_isolate; eauto.
    setoid_rewrite arrayN_isolate with (i := 0) at 4.
    rewrite skipn_skipn, skipn_selN.
    replace (st + i + 0) with (st+i) by omega.
    replace (1 + i) with (S i) by omega.
    replace (i + 0) with i by omega.
    split; cancel.
    rewrite skipn_length.
    omega.
    rewrite firstn_oob, skipn_oob by omega.
    split; cancel.
    Grab Existential Variables.
    destruct a.
    contradict l; simpl; omega.
    exact v.
  Qed.


  Lemma arrayN_ptsto_selN_0 : forall l (def : V) a,
    length l = 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def)%pred.
  Proof.
    destruct l; simpl; intros; try congruence.
    assert (length l = 0) by omega.
    apply length_nil in H0; subst; simpl; split; cancel.
  Qed.

  Lemma arrayN_isolate_hd : forall l (def : V) a,
    length l >= 1 ->
    arrayN a l <=p=> (a |-?-> selN l 0 def * arrayN (a + 1) (skipn 1 l) )%pred.
  Proof.
    destruct l; simpl; intros; try omega.
    replace (a + 1) with (S a) by omega; auto.
  Qed.


End GenArray.



Section PtstoArray.

  Variable V : Type.
  Notation pts := (@ptsto addr addr_eq_dec V).

  Lemma arrayN_oob': forall (l : list V) a i m,
    i >= length l
    -> arrayN pts a l m
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

  Lemma arrayN_oob: forall (l : list V) i m,
    i >= length l
    -> arrayN pts 0 l m
    -> m i = None.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_oob'; eauto.
  Qed.

  Lemma arrayN_oob_lt: forall (l : list V) i a m,
    arrayN pts a l m ->
    i < a ->
    m i = None.
  Proof.
    induction l; intros; auto; simpl in *.
    unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
    repeat deex.
    unfold mem_union.
    unfold ptsto in H2; destruct H2; rewrite H2.
    eapply IHl; eauto.
    omega.
  Qed.

  Lemma arrayN_updN_memupd : forall F l a i (v : V) m,
    (F * arrayN pts a l)%pred m ->
    i < length l ->
    (F * arrayN pts a (updN l i v))%pred (Mem.upd m (a + i) v).
  Proof.
    intros.
    rewrite arrayN_isolate with (i := i).
    eapply pimpl_trans; [ apply pimpl_refl | | eapply ptsto_upd ].
    rewrite selN_updN_eq by auto.
    cancel.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    pred_apply.
    rewrite arrayN_isolate by eauto.
    cancel.
    rewrite length_updN; auto.
    Grab Existential Variables. all: eauto.
  Qed.

  Lemma arrayN_app_memupd : forall l (v : V) m,
    arrayN pts 0 l m
    -> arrayN pts 0 (l ++ v :: nil) (Mem.upd m (length l) v).
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


  Theorem arrayN_list_eq : forall (vs1 vs2 : list V) s m,
    arrayN pts s vs1 m -> arrayN pts s vs2 m -> vs1 = vs2.
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

  Theorem arrayN_strictly_exact : forall (vs : list V) base,
    strictly_exact (arrayN pts base vs).
  Proof.
    induction vs; simpl; intros.
    apply emp_strictly_exact.
    apply sep_star_strictly_exact.
    apply ptsto_strictly_exact.
    eauto.
  Qed.

  Lemma arrayN_selN : forall F a st l m (def : V),
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    m a = Some (selN l (a - st) def).
  Proof.
    intros.
    eapply ptsto_valid; pred_apply.
    rewrite arrayN_isolate with (i := a - st) by omega.
    replace (st + (a - st)) with a by omega.
    clear H; cancel.
  Qed.

  Lemma arrayN_selN_exis : forall F a st (l : list V) m,
    (F * arrayN pts st l)%pred m ->
    a >= st ->
    a < st + length l ->
    exists v, m a = Some v.
  Proof.
    intros; destruct l.
    simpl in *; try omega.
    eexists; eapply arrayN_selN with (def := v); eauto; try omega.
  Qed.

  Lemma arrayN_unify' : forall a b s m (F1 F2 : pred), length a = length b ->
    (F1 * arrayN pts s a)%pred m -> (F2 * arrayN pts s b)%pred m -> a = b.
  Proof.
    induction a as [|x a']; intros.
    simpl in *.
    rewrite length_nil; auto.
    destruct b as [|y b']; simpl in *.
    inversion H.
    inversion H.
    erewrite IHa' with (s := S s); eauto.
    f_equal.
    assert (m s = Some x /\ m s = Some y); intuition.
    all : try match goal with
      | [ H : (_ * (pts ?s ?x * _))%pred ?m |- ?m ?s = Some ?x] =>
        eapply ptsto_valid;
        eapply pimpl_apply; [> | exact H]; cancel
      | [ H : (_ * (_ * arrayN _ _ ?a))%pred ?m |- (_ * arrayN _ _ ?a)%pred _] =>
        eapply pimpl_apply; [> | exact H]; cancel
    end.
    remember (m s) as r; clear Heqr; subst.
    match goal with [H: Some _ = Some _ |- _] => inversion H end; auto.
  Qed.

End PtstoArray.




Definition vsupd (vs : list valuset) (i : addr) (v : valu) : list valuset :=
  updN vs i (v, vsmerge (selN vs i ($0, nil))).

Definition vssync (vs : list valuset) (i : addr) : list valuset :=
  updN vs i (fst (selN vs i ($0, nil)), nil).

Definition vsupd_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (map vsmerge (firstn n vsl))) ++ skipn n vsl.


Lemma vsupd_length : forall vsl a v,
  length (vsupd vsl a v) = length vsl.
Proof.
  unfold vsupd; intros.
  rewrite length_updN; auto.
Qed.

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

Lemma forall_incl_refl : forall vs,
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs vs.
Proof.
  induction vs; auto.
  constructor; auto.
  apply incl_refl.
Qed.


Lemma vsupd_range_incl : forall l vs,
  length l <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs (vsupd_range vs l).
Proof.
  induction l; intros; simpl.
  rewrite vsupd_range_nil.
  apply forall_incl_refl.

  destruct vs.
  inversion H.
  cbn.
  constructor.
  apply incl_tl; apply incl_refl.
  apply IHl.
  simpl in *; omega.
Qed.


Lemma vsupd_range_selN_oob : forall vs n l,
  n >= length l ->
  length l <= length vs ->
  selN (vsupd_range vs l) n ($0, nil) = selN vs n ($0, nil).
Proof.
  unfold vsupd_range; intros.
  rewrite selN_app2.
  rewrite combine_length_eq.
  rewrite skipn_selN.
  f_equal; omega.
  rewrite map_length, firstn_length_l; omega.
  rewrite combine_length_eq; auto.
  rewrite map_length, firstn_length_l; omega.
Qed.

Lemma vsupd_range_selN_inb : forall vs n l,
  n < length l ->
  length l <= length vs ->
  selN (vsupd_range vs l) n ($0, nil) = (selN l n $0, vsmerge (selN vs n ($0, nil))).
Proof.
  unfold vsupd_range; intros.
  rewrite selN_app1.
  rewrite selN_combine.
  erewrite selN_map.
  rewrite selN_firstn; auto.
  rewrite firstn_length_l; omega.
  rewrite map_length, firstn_length_l; omega.
  rewrite combine_length_eq; auto.
  rewrite map_length, firstn_length_l; omega.
Qed.


Lemma vsupd_range_firstn_incl : forall n l vs,
  length l <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) 
            (vsupd_range vs (firstn n l)) (vsupd_range vs l).
Proof.
  induction n; intros.
  apply vsupd_range_incl; auto.
  destruct (lt_dec n (length l)).

  erewrite firstn_S_selN by auto.
  rewrite <- vsupd_range_progress by omega.
  erewrite <- updN_selN_eq with (l := (vsupd_range vs l)) (ix := n).
  apply forall2_updN; eauto.
  rewrite vsupd_range_selN_oob.
  rewrite vsupd_range_selN_inb; auto; try omega.
  apply incl_refl.
  rewrite firstn_length_l; omega.
  rewrite firstn_length_l; omega.

  rewrite firstn_oob by omega.
  apply forall_incl_refl.
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


Lemma vssync_range_incl : forall n vs,
  n <= length vs ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) (vssync_range vs n) vs.
Proof.
  induction n; simpl; intros.
  cbn.
  apply forall_incl_refl.
  rewrite <- vssync_range_progress by omega.
  rewrite <- updN_selN_eq with (ix := n) (l := vs) (default := ($0, nil)) at 2.
  apply forall2_updN.
  apply IHn; omega.

  unfold vsmerge; simpl.
  unfold vssync_range.
  rewrite selN_app2, skipn_selN.
  rewrite combine_length_eq, map_length, firstn_length_l.
  rewrite Nat.sub_diag, Nat.add_0_r.
  apply incl_cons2; apply incl_nil.
  omega.
  rewrite map_length, firstn_length_l, repeat_length; omega.
  rewrite combine_length_eq, map_length, firstn_length_l; try omega.
  rewrite map_length, firstn_length_l, repeat_length; omega.
Qed.


Definition vsupsyn_range (vsl : list valuset) (vl : list valu) :=
  let n := length vl in
  (List.combine vl (repeat nil n)) ++ skipn n vsl.

Lemma vsupsyn_range_length : forall vsl l,
  length l <= length vsl ->
  length (vsupsyn_range vsl l) = length vsl.
Proof.
  unfold vsupsyn_range; intros.
  rewrite app_length.
  rewrite combine_length.
  rewrite Nat.min_l.
  rewrite skipn_length.
  omega.
  rewrite repeat_length; auto.
Qed.

Lemma vsupsyn_range_selN : forall vsl vl i def,
  i < length vl ->
  selN (vsupsyn_range vsl vl) i (def, nil) = (selN vl i def, nil).
Proof.
  unfold vsupsyn_range; intros.
  rewrite selN_app1.
  rewrite selN_combine, repeat_selN; auto.
  rewrite repeat_length; auto.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.

Lemma vsupsyn_range_selN_oob : forall vsl vl i def,
  i >= length vl ->
  selN (vsupsyn_range vsl vl) i def = selN vsl i def.
Proof.
  unfold vsupsyn_range; intros.
  rewrite selN_app2.
  rewrite skipn_selN.
  rewrite combine_length_eq.
  rewrite le_plus_minus_r; auto.
  rewrite repeat_length; auto.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.

Lemma vsupd_range_app_tl : forall l vs v,
  length l + 1 <= length vs ->
  vsupd_range vs (l ++ [v]) = vsupd (vsupd_range vs l) (length l) v.
Proof.
  unfold vsupd_range, vsupd; intros.
  rewrite updN_app2, selN_app2; rewrite combine_length, map_length, firstn_length, Nat.min_l; auto;
  try apply Nat.min_case_strong; intros; try omega.
  rewrite Nat.sub_diag, app_length; simpl.
  erewrite firstn_plusone_selN, map_app by omega.
  rewrite combine_app by (rewrite map_length, firstn_length_l by omega; auto); simpl.
  rewrite app_assoc_reverse, updN_0_skip_1, <- cons_app by (rewrite skipn_length; omega).
  rewrite skipn_skipn', skipn_selN, Nat.add_0_r.
  reflexivity.
Qed.


(** update vsl according to (addr, valu) pairs in l. *)
Definition vsupd_vecs (vsl : list valuset) (l : list (addr * valu)) : list valuset :=
  fold_left (fun vs e => (vsupd vs (fst e) (snd e))) l vsl.


Lemma vsupd_vecs_length : forall l vs,
  length (vsupd_vecs vs l) = length vs.
Proof.
  induction l; intros; simpl; auto.
  rewrite IHl.
  unfold vsupd.
  rewrite length_updN; auto.
Qed.

Lemma vsupd_vecs_length_ok : forall l m def vs,
  Forall (fun e => fst e < length vs) l ->
  m < length l ->
  fst (selN l m def) < length (vsupd_vecs vs (firstn m l)).
Proof.
  intros.
  rewrite vsupd_vecs_length.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.

Lemma vsupd_vecs_progress : forall l m vs,
  m < length l ->
  let e := selN l m (0, $0) in
  vsupd (vsupd_vecs vs (firstn m l)) (fst e) (snd e) =
  vsupd_vecs vs (firstn (S m) l).
Proof.
  induction l; intros.
  inversion H.
  destruct m; auto.
  simpl.
  rewrite IHl; auto.
  simpl in H.
  omega.
Qed.


Lemma vsupd_comm : forall l a1 v1 a2 v2,
  a1 <> a2 ->
  vsupd (vsupd l a1 v1) a2 v2 = vsupd (vsupd l a2 v2) a1 v1.
Proof.
  unfold vsupd; intros.
  rewrite updN_comm by auto.
  repeat rewrite selN_updN_ne; auto.
Qed.

Lemma vsupd_vecs_vsupd_notin : forall av l a v,
  ~ In a (map fst av) ->
  vsupd_vecs (vsupd l a v) av = vsupd (vsupd_vecs l av) a v.
Proof.
  induction av; simpl; intros; auto.
  destruct a; simpl in *; intuition.
  rewrite <- IHav by auto.
  rewrite vsupd_comm; auto.
Qed.

Lemma vsupd_vecs_selN_not_in : forall l a d,
  ~ In a (map fst l) ->
  selN (vsupd_vecs d l) a ($0, nil) = selN d a ($0, nil).
Proof.
  induction l; intros; destruct a; simpl in *; auto; intuition.
  rewrite IHl by auto.
  unfold vsupd.
  rewrite selN_updN_ne; auto.
Qed.


Lemma vsupd_vecs_app : forall d a b,
  vsupd_vecs d (a ++ b) = vsupd_vecs (vsupd_vecs d a) b.
Proof.
  unfold vsupd_vecs; intros.
  rewrite fold_left_app; auto.
Qed.

Lemma vsupd_vecs_cons : forall l a v avl,
  vsupd_vecs l ((a, v) :: avl) = vsupd_vecs (vsupd l a v) avl.
Proof.
  auto.
Qed.


Lemma vsupd_vecs_selN_vsmerge_in' : forall a v avl l,
  In v (vsmerge (selN l a ($0, nil))) ->
  a < length l ->
  In v (vsmerge (selN (vsupd_vecs l avl) a ($0, nil))).
Proof.
  intros.
  destruct (In_dec addr_eq_dec a (map fst avl)).
  - revert H H0 i; revert avl l a v.
    induction avl; auto; intros; destruct a.
    destruct i; simpl in H0; subst.

    destruct (In_dec addr_eq_dec n (map fst avl)).
    apply IHavl; auto.
    right; unfold vsupd; simpl.
    rewrite selN_updN_eq; auto.
    unfold vsupd; rewrite length_updN; simpl in *; auto.

    rewrite vsupd_vecs_cons, vsupd_vecs_vsupd_notin by auto.
    unfold vsupd; rewrite selN_updN_eq.
    rewrite vsupd_vecs_selN_not_in; auto.
    right; auto.
    rewrite vsupd_vecs_length; auto.

    rewrite vsupd_vecs_cons.
    apply IHavl; auto; unfold vsupd.
    destruct (addr_eq_dec a0 n); subst.
    rewrite selN_updN_eq; auto.
    right; auto.
    rewrite selN_updN_ne; auto.
    rewrite length_updN; auto.
  - rewrite vsupd_vecs_selN_not_in; auto.
Qed.


Lemma vsupd_vecs_selN_vsmerge_in : forall a v avl l,
  In v (vsmerge (selN l a ($0, nil))) ->
  In v (vsmerge (selN (vsupd_vecs l avl) a ($0, nil))).
Proof.
  intros.
  destruct (lt_dec a (length l)).
  apply vsupd_vecs_selN_vsmerge_in'; auto.
  rewrite selN_oob in *; auto; try omega.
  rewrite vsupd_vecs_length; omega.
Qed.

Lemma vsupd_vecs_incl : forall l vs,
  Forall (fun e => fst e < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) vs (vsupd_vecs vs l).
Proof.
  intros.
  eapply selN_Forall2.
  rewrite vsupd_vecs_length; auto.
  intros.
  unfold incl; intros.
  apply vsupd_vecs_selN_vsmerge_in; eauto.
Qed.

Lemma vsupd_vecs_firstn_incl : forall n l vs,
  Forall (fun e => fst e < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) 
            (vsupd_vecs vs (firstn n l)) (vsupd_vecs vs l).
Proof.
  intros.
  eapply selN_Forall2 with (da := ($0, nil)) (db := ($0, nil)).
  repeat rewrite vsupd_vecs_length; auto.
  repeat rewrite vsupd_vecs_length; auto.
  intros.

  generalize dependent vs.
  generalize dependent n.
  induction l; intros.
  rewrite firstn_nil; cbn.
  apply incl_refl.
  destruct n; simpl.
  unfold incl; intros.
  apply vsupd_vecs_selN_vsmerge_in; eauto.
  cbn.
  unfold vsupd; destruct a; simpl.
  destruct (addr_eq_dec n i); subst.
  rewrite selN_updN_eq; eauto.
  rewrite selN_updN_ne; eauto.

  apply IHl.
  rewrite vsupd_length.
  eapply Forall_cons2; eauto.
  rewrite vsupd_length; auto.
Qed.


(** sync vsl for all addresses in l. *)
Definition vssync_vecs (vsl : list valuset) (l : list addr) : list valuset :=
  fold_left vssync l vsl.

Definition vssync_vecs_rev (vsl : list valuset) (l : list addr) : list valuset :=
  fold_right (fun a m => vssync m a) vsl (rev l).

Theorem vssync_vecs_rev_eq : forall l vsl,
  vssync_vecs vsl l = vssync_vecs_rev vsl l.
Proof.
  intros; unfold vssync_vecs, vssync_vecs_rev.
  rewrite fold_left_rev_right; auto.
Qed.

Lemma vssync_vecs_app : forall m l a,
  vssync_vecs m (l ++ [a]) = vssync (vssync_vecs m l) a.
Proof.
  intros.
  repeat rewrite vssync_vecs_rev_eq.
  unfold vssync_vecs_rev.
  rewrite rev_unit; reflexivity.
Qed.

Lemma vssync_vecs_length : forall l vs,
  length (vssync_vecs vs l) = length vs.
Proof.
  induction l; intros; simpl; auto.
  rewrite IHl.
  unfold vssync.
  rewrite length_updN; auto.
Qed.

Lemma vssync_vecs_length_ok : forall l m def vs,
  Forall (fun e => e < length vs) l ->
  m < length l ->
  selN l m def < length (vssync_vecs vs (firstn m l)).
Proof.
  intros.
  rewrite vssync_vecs_length.
  rewrite Forall_forall in H.
  apply H.
  apply in_selN; auto.
Qed.

Lemma vssync_vecs_progress : forall l m vs,
  m < length l ->
  vssync (vssync_vecs vs (firstn m l)) (selN l m 0) =
  vssync_vecs vs (firstn (S m) l).
Proof.
  induction l; intros.
  inversion H.
  destruct m; auto.
  simpl.
  rewrite IHl; auto.
  simpl in H.
  omega.
Qed.

Lemma vssync_vecs_vssync_comm : forall l d a,
  vssync_vecs (vssync d a) l = vssync (vssync_vecs d l) a.
Proof.
  induction l; intros; simpl; auto.
  destruct (addr_eq_dec a a0); subst; auto.
  repeat rewrite IHl.
  unfold vssync.
  repeat rewrite selN_updN_ne by auto.
  rewrite updN_comm; auto.
Qed.


Lemma vssync_synced : forall l a,
  snd (selN l a ($0, nil)) = nil ->
  vssync l a = l.
Proof.
  unfold vssync; induction l; intros; auto.
  destruct a0; simpl in *.
  destruct a; simpl in *.
  rewrite <- H; auto.
  f_equal.
  rewrite IHl; auto.
Qed.

Lemma vssync_vsupd_eq : forall l a v,
  vssync (vsupd l a v) a = updN l a (v, nil).
Proof.
  unfold vsupd, vssync, vsmerge; intros.
  rewrite updN_twice.
  destruct (lt_dec a (length l)).
  rewrite selN_updN_eq; simpl; auto.
  rewrite selN_oob.
  repeat rewrite updN_oob; auto.
  omega. omega.
  autorewrite with lists; omega.
Qed.

Lemma updN_vsupd_vecs_notin : forall av l a v,
  ~ In a (map fst av) ->
  updN (vsupd_vecs l av) a v = vsupd_vecs (updN l a v) av.
Proof.
  induction av; simpl; intros; auto.
  destruct a; simpl in *; intuition.
  rewrite IHav by auto.
  unfold vsupd, vsmerge.
  rewrite updN_comm by auto.
  rewrite selN_updN_ne; auto.
Qed.


Lemma vssync_selN_not_in : forall l i d,
  ~ In i l ->
  selN (vssync_vecs d l) i ($0, nil) = selN d i ($0, nil).
Proof.
  induction l; simpl; auto; intuition.
  rewrite IHl; auto.
  unfold vssync.
  rewrite selN_updN_ne; simpl; auto.
Qed.


Lemma vssync_vecs_selN_In : forall l i d,
  In i l ->
  i < length d ->
  selN (vssync_vecs d l) i ($0, nil) = (fst (selN d i ($0, nil)), nil).
Proof.
  induction l; intros; auto.
  inversion H.
  destruct (addr_eq_dec a i); subst; simpl.
  destruct (in_dec addr_eq_dec i l).
  rewrite IHl; unfold vssync; auto.
  rewrite selN_updN_eq; simpl; auto.
  rewrite length_updN; auto.

  rewrite vssync_selN_not_in by auto.
  unfold vssync; rewrite selN_updN_eq; simpl; auto.

  inversion H; subst; try congruence.
  rewrite IHl; unfold vssync; auto.
  rewrite selN_updN_ne; auto.
  rewrite length_updN; auto.
Qed.


Lemma vssync_vecs_incl : forall l vs,
  Forall (fun a => a < length vs) l ->
  Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) (vssync_vecs vs l) vs.
Proof.
  induction l; simpl; intros.
  apply forall_incl_refl.
  rewrite vssync_vecs_vssync_comm.
  rewrite <- updN_selN_eq with (ix := a) (l := vs) (default := ($0, nil)) at 2.
  apply forall2_updN.
  apply IHl; auto.
  eapply Forall_cons2; eauto.

  destruct (In_dec addr_eq_dec a l).
  rewrite vssync_vecs_selN_In; auto.
  unfold vsmerge; simpl.
  apply incl_cons2; apply incl_nil.
  inversion H; eauto.

  rewrite vssync_selN_not_in; auto.
  unfold vsmerge; simpl.
  apply incl_cons2; apply incl_nil.
Qed.



(* crash prediate over arrays *)
Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).

Definition possible_crash_list (l: list valuset) (l': list valu) :=
  length l = length l' /\
  forall i, i < length l -> In (selN l' i $0) (vsmerge (selN l i ($0, nil))).

Lemma synced_list_selN : forall l i def,
  selN (synced_list l) i (def, nil) = (selN l i def, nil).
Proof.
  unfold synced_list; intros.
  rewrite selN_combine.
  destruct (lt_dec i (length l)).
  rewrite repeat_selN; auto.
  setoid_rewrite selN_oob; auto.
  omega. rewrite repeat_length; omega. omega.
  rewrite repeat_length; omega.
Qed.

Lemma synced_list_map_fst : forall l,
  map fst (synced_list l) = l.
Proof.
  unfold synced_list; intros.
  rewrite map_fst_combine; auto.
  rewrite repeat_length; auto.
Qed.

Lemma vsupsyn_range_synced_list : forall a b,
  length a = length b ->
  vsupsyn_range a b = synced_list b.
Proof.
  unfold vsupsyn_range, synced_list; intros.
  rewrite skipn_oob by omega.
  rewrite app_nil_r; auto.
Qed.

Lemma possible_crash_list_length : forall l l',
  possible_crash_list l l' -> length l = length l'.
Proof.
  unfold possible_crash_list; firstorder.
Qed.

Lemma synced_list_length : forall l,
  length (synced_list l) = length l.
Proof.
  unfold synced_list; intros.
  rewrite combine_length_eq; auto.
  rewrite repeat_length; auto.
Qed.

Lemma synced_list_updN : forall l a v,
  updN (synced_list l) a (v, nil) = synced_list (updN l a v).
Proof.
  unfold synced_list; induction l; simpl; intros; auto.
  destruct a0; simpl; auto.
  rewrite IHl; auto.
Qed.

Lemma synced_list_app : forall a b,
  synced_list (a ++ b) = synced_list a ++ synced_list b.
Proof.
  induction a; simpl; auto; intros.
  unfold synced_list at 1; simpl.
  f_equal.
  apply IHa.
Qed.

Lemma synced_list_inj : forall a b, synced_list a = synced_list b -> a = b.
Proof.
  intros.
  eapply f_equal in H as HH.
  repeat rewrite synced_list_length in HH.
  generalize dependent b.
  induction a; intros; simpl in *.
  rewrite length_nil; auto.
  destruct b; simpl in *.
  inversion HH.
  unfold synced_list in *.
  simpl in *.
  inversion H; f_equal; auto.
Qed.

Lemma map_snd_synced_list_eq : forall a b,
  length a = length b ->
  map snd (synced_list a) = map snd (synced_list b).
Proof.
  unfold synced_list; intros.
  repeat rewrite map_snd_combine; autorewrite with lists; auto.
Qed.

Lemma map_snd_vsupd_vecs_not_in : forall l d a v,
  ~ In a (map fst l) ->
  NoDup (map fst l) ->
  map snd (vsupd_vecs (synced_list (updN d a v)) l) = map snd (vsupd_vecs (synced_list d) l).
Proof.
  induction l; simpl; intros.
  erewrite map_snd_synced_list_eq; eauto.
  autorewrite with lists; auto.

  destruct a; intuition; simpl in *.
  inversion H0; subst.
  setoid_rewrite vsupd_vecs_vsupd_notin; auto.
  unfold vsupd.
  repeat rewrite map_snd_updN.
  f_equal.
  apply IHl; auto.
  f_equal; f_equal; f_equal.
  rewrite <- synced_list_updN.
  rewrite <- updN_vsupd_vecs_notin by auto.
  rewrite selN_updN_ne; auto.
Qed.


Lemma possible_crash_list_updN : forall l l' a v vs,
  possible_crash_list l l' ->
  possible_crash_list (updN l a (v, vs)) (updN l' a v).
Proof.
  unfold possible_crash_list; simpl; intuition;
  autorewrite with lists in *; auto.
  destruct (Nat.eq_dec a i); subst.
  repeat rewrite selN_updN_eq; auto; omega.
  repeat rewrite selN_updN_ne; eauto.
Qed.


Lemma possible_crash_list_unique : forall a b,
  (forall n, snd (selN a n ($0, nil)) = nil) ->
  possible_crash_list a b ->
  b = map fst a.
Proof.
  unfold possible_crash_list; intuition.
  eapply list_selN_ext; auto; intros.
  rewrite map_length; auto.
  rewrite <- H1 in H0.
  specialize (H2 _ H0).
  inversion H2.

  erewrite selN_map; eauto.
  rewrite H in H3.
  inversion H3.
Qed.

Lemma possible_crash_list_synced_list_eq : forall a b,
  possible_crash_list (synced_list a) b -> a = b.
Proof.
  unfold possible_crash_list; intuition.
  rewrite synced_list_length in *.
  eapply list_selN_ext; auto; intros.
  specialize (H1 _ H).
  inversion H1.

  generalize H2.
  unfold synced_list; rewrite selN_combine; eauto.
  rewrite repeat_length; auto.

  generalize H2.
  unfold synced_list; rewrite selN_combine; simpl.
  rewrite repeat_selN by auto.
  intro Hx; inversion Hx.
  rewrite repeat_length; auto.
Qed.

Lemma possible_crash_list_synced_list : forall l,
  possible_crash_list (synced_list l) l.
Proof.
  unfold possible_crash_list; intuition.
  rewrite synced_list_length; auto.
  unfold synced_list; constructor.
  rewrite selN_combine; auto.
  rewrite repeat_length; auto.
Qed.

Lemma possible_crash_list_cons : forall vsl vl v vs,
  possible_crash_list vsl vl ->
  In v (vsmerge vs) ->
  possible_crash_list (vs :: vsl) (v :: vl).
Proof.
  unfold possible_crash_list; intuition.
  simpl; omega.
  destruct i, vs, vsl; firstorder.
Qed.

Theorem possible_crash_list_vssync : forall l l' a,
  possible_crash_list (vssync l a) l' ->
  possible_crash_list l l'.
Proof.
  unfold possible_crash_list, vssync; intuition; rewrite length_updN in *; auto.
  specialize (H1 _ H).
  destruct (addr_eq_dec i a); subst.
  erewrite selN_updN_eq in H1 by auto; simpl in *. intuition.
  erewrite selN_updN_ne in H1 by auto; eauto.
Qed.



Section ArrayCrashXform.

  Notation pts := (@ptsto addr addr_eq_dec valuset).

  Lemma crash_xform_arrayN: forall l st,
    crash_xform (arrayN pts st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN pts st (synced_list l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto. auto.

    xform.
    rewrite IHl.
    cancel; [ instantiate (1 := v' :: l') | .. ]; simpl; auto; try cancel;
    destruct i; simpl; auto;
    destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN pts st (synced_list l) =p=> crash_xform (arrayN pts st l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_r with (v := a) by (apply H1'; omega).
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. omega.
  Qed.

  Lemma crash_xform_synced_arrayN: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN pts st l) =p=> arrayN pts st l.
  Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H1.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma crash_xform_arrayN_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN pts st (List.combine l (repeat nil (length l)))) =p=>
    arrayN pts st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_synced: forall (l : list valu) st,
    crash_xform (arrayN pts st (synced_list l)) =p=>
    arrayN pts st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

End ArrayCrashXform.



Section SubsetArray.

  Theorem sync_invariant_arrayN_subset : forall vs a,
    sync_invariant (arrayN ptsto_subset a vs).
  Proof.
    induction vs; simpl; auto.
  Qed.

  Lemma arrayN_subset_oob': forall l a i m,
    i >= length l
    -> arrayN ptsto_subset a l m
    -> m (a + i) = None.
  Proof.
    induction l; intros; auto; simpl in *.
    destruct (eq_nat_dec i 0); auto.
    subst; simpl in *; omega.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto_subset in H2.
    destruct_lift H2.
    unfold ptsto in H1; destruct H1.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
    destruct (m1 (a0 + i)) eqn:?.
    contradict Heqo.
    rewrite H2; try congruence.
    omega.
    apply H3.
    omega.
    auto.
  Qed.

  Lemma arrayN_subset_oob: forall l i m,
    i >= length l
    -> arrayN ptsto_subset 0 l m
    -> m i = None.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_subset_oob'; eauto.
  Qed.

  Lemma arrayN_selN_subset : forall F a st l m def,
    (F * arrayN ptsto_subset st l)%pred m ->
    a >= st ->
    a < st + length l ->
    let vs0 := (selN l (a - st) def) in
    exists vs, m a = Some vs /\ fst vs = fst vs0 /\ incl (snd vs) (snd vs0).
  Proof.
    cbn; intros.
    rewrite arrayN_isolate with (i := a - st) in H by omega.
    unfold ptsto_subset at 2 in H; destruct_lift H; simpl in *.
    eexists; split; try split.
    eapply ptsto_valid.
    pred_apply; replace (st + (a - st)) with a by omega; cancel.
    simpl; auto.
    auto.
  Qed.

  Lemma arrayN_subset_memupd : forall F l a i v vs vs' m,
    (F * arrayN ptsto_subset a l)%pred m ->
    incl vs' vs ->
    i < length l ->
    (F * arrayN ptsto_subset a (updN l i (v, vs)))%pred (Mem.upd m (a + i) (v, vs')).
  Proof.
    intros.
    rewrite arrayN_isolate with (i := i) in H by auto.
    unfold ptsto_subset at 2 in H; destruct_lift H.
    setoid_rewrite sep_star_comm in H.
    apply sep_star_assoc in H.
    apply ptsto_upd with (v := (v, vs')) in H.
    pred_apply.
    setoid_rewrite arrayN_isolate with (i := i) at 3.
    unfold ptsto_subset at 4.
    rewrite selN_updN_eq by auto.
    cancel.
    rewrite firstn_updN_oob by auto.
    rewrite skipn_updN by auto.
    cancel.
    rewrite length_updN; auto.
    Grab Existential Variables. all: eauto.
  Qed.

  Lemma crash_xform_arrayN_subset: forall l st,
    crash_xform (arrayN ptsto_subset st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN ptsto_subset st (synced_list l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto. auto.

    xform.
    rewrite IHl.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset, synced_list.
    cancel; [ instantiate (1 := v' :: l') | .. ]; simpl; auto; try cancel;
    destruct i; simpl; auto;
    destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_subset_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN ptsto_subset st (synced_list l) =p=>
     crash_xform (arrayN ptsto_subset st l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_subset_r with (v := a) by (apply H1'; omega).
      rewrite ptsto_subset_pimpl_ptsto.
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. omega.
  Qed.

  Lemma crash_xform_synced_arrayN_subset: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN ptsto_subset st l) =p=> arrayN ptsto_subset st l.
  Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
    cancel.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H0.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma crash_xform_arrayN_subset_combine_nils: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (List.combine l (repeat nil (length l)))) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_subset_synced: forall (l : list valu) st,
    crash_xform (arrayN ptsto_subset st (synced_list l)) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

End SubsetArray.


Hint Resolve sync_invariant_arrayN_subset.
Notation arrayS := (arrayN ptsto_subset).


Section ListUpd.

  Variable V : Type.
  Notation pts := (@ptsto addr addr_eq_dec V).

  Fixpoint listupd (m : @mem _ addr_eq_dec V) base (vs : list V) :=
    match vs with
    | nil => m
    | v :: tl => listupd (upd m base v) (S base) tl
    end.

  Lemma arrayN_listupd: forall l (m : @mem _ _ V) l0 base F,
    (F * arrayN pts base l0 )%pred m ->
    length l0 = length l ->
    (F * arrayN pts base l)%pred (listupd m base l).
  Proof.
    induction l; intros; destruct l0; simpl in *; auto; try omega.
    apply sep_star_assoc.
    eapply IHl with (l0 := l0); eauto.
    setoid_rewrite sep_star_comm at 1.
    apply sep_star_assoc.
    eapply ptsto_upd.
    pred_apply; cancel.
  Qed.

  Lemma arrayN_listupd_eq : forall (l : list V) F st d,
    (F * arrayN pts st l)%pred d ->
    d = listupd d st l.
  Proof.
    induction l; simpl; intros; auto.
    erewrite <- IHl.
    rewrite upd_nop; auto.
    eapply ptsto_valid.
    pred_apply; cancel.
    rewrite upd_nop; auto.
    pred_apply; cancel.
    eapply ptsto_valid.
    pred_apply; cancel.
  Qed.

  Lemma listupd_sel_oob : forall (l : list V) a off m,
    a < off \/ a >= off + (length l) ->
    listupd m off l a = m a.
  Proof.
    induction l; simpl; intros; auto.
    rewrite IHl by (intuition omega).
    destruct (addr_eq_dec off a0); subst.
    exfalso; intuition.
    rewrite Mem.upd_ne; auto.
  Qed.

  Lemma listupd_sel_inb : forall (l : list V) a off m def,
    a >= off ->
    a < off + (length l) ->
    listupd m off l a = Some (selN l (a - off) def).
  Proof.
    induction l; simpl; intros; try omega.
    case_eq (a0 - off); intros.
    replace off with a0 in * by omega.
    rewrite listupd_sel_oob; intuition.
    apply Mem.upd_eq; auto.

    erewrite IHl; try omega.
    replace (a0 - S off) with n by omega; auto.
  Qed.

  Lemma listupd_sel_cases : forall (l : list V) a off m def,
    ((a < off \/ a >= off + (length l)) /\ listupd m off l a = m a ) \/
    (a >= off /\ a < off + (length l) /\ listupd m off l a = Some (selN l (a - off) def) ).
  Proof.
    intros.
    destruct (lt_dec a off);
    destruct (ge_dec a (off + (length l)));
    try ( left; intuition; apply listupd_sel_oob; auto ).
    right; intuition.
    apply listupd_sel_inb; omega.
  Qed.

End ListUpd.


Section ListUpdSubset.

  Lemma arrayN_listupd_subset : forall l m l0 base F,
    (F * arrayN ptsto_subset base l0 )%pred m ->
    length l0 = length l ->
    (F * arrayN ptsto_subset base l)%pred (listupd m base l).
  Proof.
    induction l; intros; destruct l0; simpl in *; auto; try omega.
    apply sep_star_assoc.
    eapply IHl with (l0 := l0); eauto.
    setoid_rewrite sep_star_comm at 1.
    apply sep_star_assoc.
    apply sep_star_comm; destruct a, p.
    eapply ptsto_subset_upd.
    pred_apply; cancel.
    apply incl_refl.
  Qed.

End ListUpdSubset.
