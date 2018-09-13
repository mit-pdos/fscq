Require Import Mem.
Require Import Pred.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import Morphisms.
Require Import Arith.

Require Export AsyncDisk.

Set Implicit Arguments.

Definition ptsto_subset {AT AEQ V} (a : AT) (vs : V * list V) : @pred AT AEQ (V * list V) :=
  (exists old, a |-> (fst vs, old) * [[ incl old (snd vs) ]])%pred.

Notation "a |=> v" := (a |-> (v, nil))%pred (at level 35) : pred_scope.
Notation "a |~> v" := (exists old, a |-> (v, old))%pred (at level 35) : pred_scope.
Notation "a |+> v" := (ptsto_subset a v) (at level 35) : pred_scope.
Notation "a |+>?" := (exists v, a |+> v)%pred (at level 35) : pred_scope.

Definition rawpred V := @pred addr addr_eq_dec (V * list V).

Definition possible_crash {AT AEQ V} (m m' : @mem AT AEQ (V * list V)) : Prop :=
  forall a,
  (m a = None /\ m' a = None) \/
  (exists vs v', m a = Some vs /\ m' a = Some (v', nil) /\ In v' (vsmerge vs)).

(* if [p] was true before a crash, then [crash_xform p] is true after a crash *)
Definition crash_xform {AT AEQ V} (p : @pred AT AEQ (V * list V)) :=
  fun m => exists m', p m' /\ possible_crash m' m.

(* if [p] was true before a sync, then [sync_xform p] is true after a sync *)
Definition sync_xform {AT AEQ V} (p : @pred AT AEQ (V * list V)) :=
  fun m => exists m', p m' /\ m = sync_mem m'.


(* Specialized relations for [@pred valuset], to deal with async IO *)

Theorem crash_xform_apply : forall {AT AEQ V} (p : @pred AT AEQ (V * list V))  m m',
    possible_crash m m'
  -> p m
  -> crash_xform p m'.
Proof.
  unfold crash_xform; eauto.
Qed.

Theorem possible_crash_mem_union : forall AT AEQ V (ma mb m' : @mem AT AEQ (V * list V)),
    possible_crash (mem_union ma mb) m'
  -> mem_disjoint ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_crash ma ma' /\ possible_crash mb mb'.
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_crash in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - unfold possible_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
  - unfold possible_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
Qed.

Theorem possible_crash_disjoint : forall AT AEQ V (ma mb ma' mb' : @mem AT AEQ (V * list V)),
  mem_disjoint  ma' mb'
  -> possible_crash ma ma'
  -> possible_crash mb mb'
  -> mem_disjoint ma mb.
Proof.
  unfold mem_disjoint, possible_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.

Theorem possible_crash_union : forall AT AEQ V (ma mb ma' mb' : @mem AT AEQ (V * list V)),
    possible_crash ma ma'
  -> possible_crash mb mb'
  -> possible_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
  unfold possible_crash, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
Qed.

Theorem possible_crash_trans : forall AT AEQ V (ma mb mc : @mem AT AEQ (V * list V)),
  possible_crash ma mb ->
  possible_crash mb mc ->
  possible_crash ma mc.
Proof.
  unfold possible_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition; repeat deex; try congruence.
  right; repeat eexists; intuition eauto.
  rewrite H0 in H1.
  inversion H1; subst; clear H1.
  inversion H3.
  simpl in H1; subst; auto.
  inversion H1.
Qed.


Lemma possible_crash_notindomain : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)) a,
  possible_crash m m' ->
  notindomain a m ->
  notindomain a m'.
Proof.
  unfold possible_crash; intuition.
  specialize (H a); intuition; repeat deex; congruence.
Qed.


Lemma possible_crash_upd : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)) a v vs,
  possible_crash m m' ->
  In v (vsmerge vs) ->
  possible_crash (upd m a vs) (upd m' a (v, nil)).
Proof.
  unfold possible_crash; intuition.
  destruct (AEQ a a0); subst.
  repeat rewrite upd_eq; auto.
  specialize (H a0); intuition; right; eexists; eauto.
  repeat rewrite upd_ne; auto.
Qed.

Lemma possible_crash_updSome : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)) a v vs,
  possible_crash m m' ->
  In v (vsmerge vs) ->
  possible_crash (updSome m a vs) (updSome m' a (v, nil)).
Proof.
  unfold possible_crash; intuition.
  pose proof (H a) as H'; intuition; repeat deex.

  - repeat rewrite updSome_none by eauto.
    intuition.

  - destruct (AEQ a a0); subst.
    + repeat erewrite updSome_eq by eauto. right. eauto.
    + repeat rewrite updSome_ne by eauto. eauto.
Qed.

Definition synced_mem {AT AEQ V} (m : @mem AT AEQ (V * list V)) :=
  forall a, m a = None \/ exists v, m a = Some (v, nil).

Lemma synced_mem_snd_nil : forall AT AEQ V (m : @mem AT AEQ (V * list V)) a vs,
  synced_mem m ->
  m a = Some vs ->
  snd vs = nil.
Proof.
  unfold synced_mem; intuition.
  specialize (H a); intuition; try congruence.
  destruct H1.
  rewrite H in H0; inversion H0; auto.
Qed.

Theorem possible_crash_synced : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)),
  possible_crash m m' ->
  synced_mem m'.
Proof.
  unfold possible_crash, synced_mem; intuition.
  specialize (H a); intuition.
  right; repeat deex.
  eexists; eauto.
Qed.

Theorem possible_crash_refl : forall AT AEQ V (m : @mem AT AEQ (V * list V)),
  synced_mem m ->
  possible_crash m m.
Proof.
  unfold synced_mem, possible_crash; intuition.
  specialize (H a); intuition.
  destruct H0; right.
  do 2 eexists; simpl; intuition eauto.
Qed.


Lemma possible_crash_emp_l : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)),
  possible_crash m m' ->
  emp m' ->
  emp m.
Proof.
  unfold possible_crash, emp; intros.
  specialize (H a); intuition; repeat deex.
  congruence.
Qed.

Lemma possible_crash_emp_r : forall AT AEQ V (m m': @mem AT AEQ (V * list V)),
  possible_crash m m' ->
  emp m ->
  emp m'.
Proof.
  unfold possible_crash, emp; intros.
  specialize (H a); intuition; repeat deex.
  congruence.
Qed.

Lemma possible_crash_ptsto_upd_incl' : forall AT AEQ V (m m': @mem AT AEQ (V * list V)) a vs vs',
  m a = Some vs ->
  possible_crash m m' ->
  incl (vsmerge vs) (vsmerge vs') ->
  possible_crash (upd m a vs') m'.
Proof.
  unfold possible_crash, vsmerge; simpl; intros.
  destruct vs, vs'; simpl in *.
  destruct (AEQ a0 a); subst.

  - specialize (H0 a); intuition.
    left; congruence.
    right; erewrite upd_eq by eauto; repeat deex; destruct vs; simpl in *.
    rewrite H in H2; inversion H2; subst.
    exists (v0, l0); exists v1; intuition.
    rewrite H in H2; inversion H2; subst.
    exists (v0, l0); exists v'; intuition.

  - rewrite upd_ne by auto.
    specialize (H0 a0); intuition.
Qed.


Lemma possible_crash_ptsto_upd_incl : forall AT AEQ V F (m m': @mem AT AEQ (V * list V)) a vs vs',
  (F * a |-> vs)%pred m ->
  possible_crash m m' ->
  incl (vsmerge vs) (vsmerge vs') ->
  possible_crash (upd m a vs') m'.
Proof.
  intros.
  eapply possible_crash_ptsto_upd_incl'; eauto.
  eapply ptsto_valid'; eauto.
Qed.

Lemma possible_crash_upd_incl : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)) a v v0,
  possible_crash (upd m a v) m' ->
  m a = Some v0 ->
  incl (vsmerge v) (vsmerge v0) ->
  possible_crash m m'.
Proof.
  unfold possible_crash, vsmerge; intuition.
  destruct (AEQ a a1); subst; simpl in *.
  - specialize (H a1); intuition; right;
    erewrite upd_eq in * by eauto; try congruence.
    repeat deex.
    destruct vs, v0; inversion H2; subst; simpl in *.
    exists (v0, l0), v; intuition.
    destruct vs, v0; inversion H2; subst; simpl in *.
    exists (v0, l0), v'; intuition.
  - specialize (H a1); intuition; rewrite upd_ne in *; auto.
Qed.

Lemma possible_crash_upd_nil : forall AT AEQ V (m m': @mem AT AEQ (V * list V)) a v0,
  possible_crash (upd m a (fst v0, nil)) m' ->
  m a = Some v0 ->
  possible_crash m m'.
Proof.
  intros.
  eapply possible_crash_upd_incl; eauto.
  unfold vsmerge; simpl.
  apply incl_cons2, incl_nil.
Qed.


Lemma possible_crash_ptsto_upd_postfix : forall AT AEQ V F (m m' : @mem AT AEQ (V * list V)) a v vs vs',
  (F * a |-> (v, vs))%pred m ->
  possible_crash m m' ->
  postfix vs vs' ->
  possible_crash (upd m a (v, vs')) m'.
Proof.
  intros.
  eapply possible_crash_ptsto_upd_incl; eauto.
  apply incl_cons2; simpl.
  unfold incl, postfix in *; destruct H1; subst; intuition.
  eapply in_skipn_in; eauto.
Qed.

Lemma possible_crash_sel_exis : forall AT AEQ V (m m' : @mem AT AEQ (V * list V)) a vs,
  possible_crash m m' ->
  m a = Some vs ->
  exists v, m' a = Some (v, nil) /\ In v (vsmerge vs).
Proof.
  unfold possible_crash; intuition.
  specialize (H a); intuition; try congruence.
  repeat deex; eexists; split; eauto.
  rewrite H0 in H1; inversion H1; subst; auto.
Qed.


Theorem crash_xform_sep_star_dist : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  crash_xform (p * q) <=p=> crash_xform p * crash_xform q.
Proof.
  unfold_sep_star; unfold crash_xform, piff, pimpl; split; intros; repeat deex.
  - edestruct possible_crash_mem_union; try eassumption; repeat deex.
    do 2 eexists; intuition; eexists; eauto.
  - eexists; split.
    do 2 eexists; intuition; [| eassumption | eassumption].
    eapply possible_crash_disjoint; eauto.
    apply possible_crash_union; eauto.
Qed.

Theorem crash_xform_or_dist : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  crash_xform (p \/ q) <=p=> crash_xform p \/ crash_xform q.
Proof.
  firstorder.
Qed.

Theorem crash_xform_lift_empty : forall AT AEQ V (P : Prop),
  @crash_xform AT AEQ V [[ P ]] <=p=> [[ P ]].
Proof.
  unfold crash_xform, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  specialize (H1 a); destruct H1; intuition.
  repeat deex; congruence.
  eexists; intuition.
Qed.

Theorem crash_xform_sep_star_apply : forall AT AEQ V (p q: @pred AT AEQ (V * list V)) (m m' : mem),
    possible_crash m m'
  -> (p * q)%pred m
  -> (crash_xform p * crash_xform q)%pred m'.
Proof.
  unfold_sep_star; intros; repeat deex.
  edestruct possible_crash_mem_union; try eassumption; repeat deex.
  do 2 eexists; repeat split; auto; unfold crash_xform; eexists; split; eauto.
Qed.

Theorem crash_xform_exists_comm : forall T AT AEQ V (p : T -> @pred AT AEQ (V * list V)),
  crash_xform (exists x, p x) <=p=> exists x, crash_xform (p x).
Proof.
  split; unfold crash_xform, exis, pimpl; intros;
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem crash_xform_forall_comm : forall T AT AEQ V (p : T -> @pred AT AEQ (V * list V)),
  crash_xform (foral x, p x) =p=> foral x, crash_xform (p x).
Proof.
  unfold crash_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem crash_xform_ptsto: forall A AEQ V (a: A) (v: V * list V),
  (crash_xform (AEQ:=AEQ)) (a |-> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |=> v'.
Proof.
  unfold crash_xform, possible_crash, ptsto, pimpl; intros.
  repeat deex; destruct (H1 a).
  intuition; congruence.
  repeat deex; rewrite H in H3; inversion H3; subst.
  repeat eexists.
  apply lift_impl.
  intros; eauto.
  split; auto.
  intros.
  destruct (H1 a').
  intuition.
  repeat deex.
  specialize (H2 a' H4).
  congruence.
Qed.

Theorem crash_xform_ptsto_r: forall A AEQ V a v vs,
  In v (vsmerge vs) ->
  a |=> v =p=> @crash_xform A AEQ V (a |-> vs).
Proof.
  unfold crash_xform, possible_crash, ptsto, pimpl; intros.
  exists (insert empty_mem a vs).
  intuition.
  rewrite insert_eq; eauto.
  rewrite insert_ne; eauto.
  destruct (AEQ a a0); subst.
  - right. rewrite insert_eq; auto. exists vs. exists v. intuition.
  - left. rewrite insert_ne; auto.
Qed.


Theorem crash_xform_ptsto_exis : forall A AEQ V a,
  @crash_xform A AEQ V ( a |->? ) =p=> a |->?.
Proof.
  intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_l; intro.
  setoid_rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  apply pimpl_exists_r.
  exists (x0, nil).
  rewrite sep_star_comm.
  apply sep_star_lift_l; intros; auto.
Qed.

Theorem crash_xform_ptsto_subset : forall A AEQ V a v,
  @crash_xform A AEQ V (a |+> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |=> v'.
Proof.
  unfold ptsto_subset; intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_l; intros.
  rewrite crash_xform_sep_star_dist, crash_xform_lift_empty.
  rewrite crash_xform_ptsto.
  apply sep_star_lift_l; intro.
  apply pimpl_exists_l; intros.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  apply pimpl_exists_r; exists x0.
  apply sep_star_lift_r'.
  apply pimpl_and_split; auto.
  unfold lift, pimpl; intros.
  cbn in *; intuition.
Qed.

Theorem crash_xform_ptsto_subset_r: forall A AEQ V a v vs,
  In v (vsmerge vs) ->
  a |=> v =p=> @crash_xform A AEQ V (a |+> vs).
Proof.
  unfold ptsto_subset; intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_r; eexists.
  rewrite crash_xform_sep_star_dist, crash_xform_lift_empty.
  rewrite <- crash_xform_ptsto_r.
  apply sep_star_lift_r.
  apply pimpl_and_split; eauto.
  unfold lift, pimpl; intros.
  cbn in *; intuition.
  eauto.
Qed.


Theorem crash_xform_pimpl : forall {AT AEQ V} (p q: @pred AT AEQ (V * list V)), p =p=>q
  -> crash_xform p =p=> crash_xform q.
Proof.
  firstorder.
Qed.


Instance crash_xform_pimpl_proper:
  forall AT AEQ V, Proper (pimpl ==> pimpl) (@crash_xform AT AEQ V).
Proof.
  firstorder.
Qed.

Instance crash_xform_flip_pimpl_proper:
  forall AT AEQ V, Proper (Basics.flip pimpl ==> Basics.flip pimpl) (@crash_xform AT AEQ V).
Proof.
  firstorder.
Qed.

Instance crash_xform_piff_proper:
  forall AT AEQ V, Proper (piff ==> piff) (@crash_xform AT AEQ V).
Proof.
  firstorder.
Qed.


Theorem crash_invariant_emp:
  forall AT AEQ V, @crash_xform AT AEQ V emp =p=> emp.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl; repeat deex; intuition; repeat deex.
  destruct (H1 a); [ intuition | repeat deex; congruence ].
Qed.

Theorem crash_invariant_emp_r:
  forall AT AEQ V, emp =p=> @crash_xform AT AEQ V emp.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl. intros.
  exists empty_mem. intuition.
Qed.

Theorem crash_invariant_ptsto: forall AT AEQ V a v,
  @crash_xform AT AEQ V (a |=> v) =p=> a |=> v.
Proof.
  unfold crash_xform, pimpl, possible_crash, ptsto; intros.
  deex; intuition eauto.
  { destruct (H1 a).
    + intuition; congruence.
    + repeat deex.
      inversion H5; subst; rewrite H in H3; inversion H3; subst; [ auto | inversion H4 ]. }
  { destruct (H1 a').
    + intuition.
    + repeat deex.
      assert (m' a' = None) by eauto; congruence.
  }
Qed.

Lemma ptsto_synced_valid:
  forall AT AEQ V a v (F : @pred AT AEQ (V * list V)) m,
  (a |=> v * F)%pred m
  -> m a = Some (v, nil).
Proof.
  intros.
  eapply ptsto_valid; eauto.
Qed.

Lemma ptsto_cur_valid:
   forall AT AEQ V a v (F : @pred AT AEQ (V * list V)) m,
  (a |~> v * F)%pred m
  -> exists l, m a = Some (v, l).
Proof.
  unfold ptsto; unfold_sep_star; intros.
  repeat deex.
  destruct H1.
  destruct H0.
  eexists.
  apply mem_union_addr; eauto.
Qed.

Lemma crash_xform_diskIs: forall AT AEQ V (m: @mem AT AEQ (V * list V)),
  crash_xform (diskIs m) =p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
Proof.
  unfold crash_xform, pimpl, diskIs.
  intros.
  destruct H; intuition; subst.
  exists m0.
  unfold_sep_star.
  exists (fun a => None).
  exists m0.
  intuition.
  unfold mem_disjoint; intuition.
  repeat deex; discriminate.
  unfold lift_empty; intuition.
Qed.

Lemma crash_xform_diskIs_r:  forall AT AEQ V (m m': @mem AT AEQ (V * list V)),
  possible_crash m m' ->
  diskIs m' =p=> crash_xform (diskIs m).
Proof.
  unfold crash_xform, pimpl, diskIs.
  intros; subst; firstorder.
Qed.

Lemma crash_xform_diskIs_piff:  forall AT AEQ V (m: @mem AT AEQ (V * list V)),
  crash_xform (diskIs m) <=p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
Proof.
  split.
  apply crash_xform_diskIs.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  apply crash_xform_diskIs_r; auto.
Qed.

Lemma possible_crash_mem_except :  forall AT AEQ V (m1 m2: @mem AT AEQ (V * list V)) a,
  possible_crash m1 m2 ->
  possible_crash (mem_except m1 a) (mem_except m2 a).
Proof.
  unfold possible_crash, mem_except; intuition.
  specialize (H a0).
  destruct (AEQ a0 a); intuition.
Qed.

Lemma mem_except_upd : forall AT AEQ V (m : @mem AT AEQ V) a v,
  mem_except m a = mem_except (upd m a v) a.
Proof.
  unfold mem_except, upd; intuition.
  apply functional_extensionality; intros.
  destruct (AEQ x a); intuition.
Qed.

Lemma possible_crash_upd_mem_except :  forall AT AEQ V (m1 m2: @mem AT AEQ (V * list V)) a v,
  possible_crash m1 (upd m2 a v) ->
  possible_crash (mem_except m1 a) (mem_except m2 a).
Proof.
  intros.
  eapply possible_crash_mem_except in H.
  rewrite <- mem_except_upd in H.
  auto.
Qed.


Lemma possible_crash_eq : forall AT AEQ V (a b c: @mem AT AEQ (V * list V)),
  possible_crash a b ->
  possible_crash b c ->
  b = c.
Proof.
  unfold possible_crash; intuition.
  apply functional_extensionality; intros.
  specialize (H x); specialize (H0 x).
  intuition; repeat deex; try congruence.

  destruct vs, vs0; subst.
  rewrite H1 in H0; inversion H0; subst.
  unfold vsmerge in *; simpl in *.
  intuition; subst; congruence.
Qed.

Lemma crash_xform_diskIs_trans :  forall AT AEQ V (d d' x : @mem AT AEQ (V * list V)),
  crash_xform (diskIs d) x ->
  crash_xform (diskIs x) d' ->
  crash_xform (diskIs x) =p=> crash_xform (diskIs d).
Proof.
  intros.
  apply crash_xform_diskIs in H.
  apply crash_xform_diskIs in H0.
  destruct H; destruct H0.
  apply sep_star_comm in H; apply sep_star_lift_apply in H.
  apply sep_star_comm in H0; apply sep_star_lift_apply in H0.
  destruct H; destruct H0.
  rewrite crash_xform_diskIs, <- crash_xform_diskIs_r by eauto.
  unfold diskIs in *; subst.
  unfold pimpl; intros; subst.
  eapply possible_crash_eq; eauto.
  destruct H.
  apply sep_star_comm in H; apply sep_star_lift_apply in H; destruct H.
  subst; auto.
Qed.


Lemma crash_xform_diskIs_eq :  forall AT AEQ V (a b: @mem AT AEQ (V * list V)) F,
  crash_xform F a ->
  crash_xform (diskIs a) b ->
  a = b.
Proof.
  unfold crash_xform, possible_crash; intuition.
  apply functional_extensionality; intros.
  repeat deex.
  specialize (H2 x); specialize (H3 x).
  intuition; repeat deex; try congruence.

  rewrite H, H2.
  unfold vsmerge, diskIs in *; destruct vs, vs0.
  simpl in *; intuition; subst; try congruence.
  rewrite H2 in H4; inversion H4; subst.
  inversion H5.
  rewrite H2 in H4; inversion H4; subst.
  inversion H5.
Qed.


Lemma crash_xform_diskIs_pred :  forall AT AEQ V (m: @mem AT AEQ (V * list V)) (F: pred),
  F m -> crash_xform (diskIs m) =p=> crash_xform F.
Proof.
  unfold crash_xform, diskIs.
  unfold pimpl; intros.
  destruct H0; intuition subst.
  eexists; eauto.
Qed.

Lemma crash_xform_ptsto_or : forall AT AEQ V a vs,
  @crash_xform AT AEQ V (a |-> vs) <=p=> crash_xform (a |-> vs \/ a |=> (fst vs)).
Proof.
  split.
  rewrite crash_xform_or_dist.
  apply pimpl_or_r; left; auto.
  rewrite crash_xform_or_dist.
  apply pimpl_or_l; auto.
  rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  rewrite crash_xform_ptsto_r; eauto.
  unfold vsmerge in *; simpl in *; intuition.
Qed.


Lemma crash_xform_ptsto_vsmerge :  forall AT AEQ V a vs v,
  @crash_xform AT AEQ V (a |-> (v, vsmerge vs)) <=p=> crash_xform (a |-> vs \/ a |-> (v, vsmerge vs)).
Proof.
  split; rewrite crash_xform_or_dist.
  apply pimpl_or_r; right; auto.
  apply pimpl_or_l; auto.
  rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  rewrite <- crash_xform_ptsto_r; eauto.
  unfold vsmerge; simpl; intuition.
Qed.


Theorem crash_xform_idem_l : forall AT AEQ V (p: @pred AT AEQ (V * list V)), 
  crash_xform (crash_xform p) =p=> crash_xform p.
Proof.
  unfold crash_xform, pimpl; intros.
  repeat deex; eexists; intuition eauto.
  eapply possible_crash_trans; eauto.
Qed.

Theorem crash_xform_idem_r : forall AT AEQ V (p: @pred AT AEQ (V * list V)),
  crash_xform p =p=> crash_xform (crash_xform p).
Proof.
  unfold crash_xform, pimpl, possible_crash; intros.
  repeat deex; eexists; intuition eauto.
  specialize (H1 a); intuition.
  repeat destruct H; destruct H1.
  right.
  do 2 eexists; intuition eauto.
  cbn; left; auto.
Qed.

Theorem crash_xform_idem : forall AT AEQ V (p: @pred AT AEQ (V * list V)),
  crash_xform (crash_xform p) <=p=> crash_xform p.
Proof.
  split.
  apply crash_xform_idem_l.
  apply crash_xform_idem_r.
Qed.

Theorem crash_xform_synced : forall AT AEQ V (p: @pred AT AEQ (V * list V)) m,
  crash_xform p m ->
  synced_mem m.
Proof.
  unfold crash_xform; intros.
  repeat deex.
  eapply possible_crash_synced; eauto.
Qed.

Theorem crash_xform_possible_crash_refl : forall AT AEQ V (p: @pred AT AEQ (V * list V)) m,
  crash_xform p m ->
  possible_crash m m.
Proof.
  intros.
  apply possible_crash_refl.
  eapply crash_xform_synced; eauto.
Qed.



Hint Rewrite crash_xform_sep_star_dist : crash_xform.
Hint Rewrite crash_xform_or_dist : crash_xform.
Hint Rewrite crash_xform_exists_comm : crash_xform.
Hint Rewrite crash_xform_forall_comm : crash_xform.
Hint Rewrite crash_xform_lift_empty : crash_xform.
Hint Rewrite crash_xform_ptsto : crash_xform.
Hint Rewrite crash_xform_diskIs : crash_xform.
Hint Rewrite crash_invariant_ptsto : crash_xform.

Hint Resolve crash_invariant_emp.

Lemma pred_apply_crash_xform : forall AT AEQ V (p: @pred AT AEQ (V * list V)) m m',
  possible_crash m m' -> p m -> (crash_xform p) m'.
Proof.
  unfold pimpl, crash_xform; eauto.
Qed.

Lemma pred_apply_crash_xform_pimpl : forall AT AEQ V (p q: @pred AT AEQ (V * list V)) m m',
  possible_crash m m' -> p m -> crash_xform p =p=> q -> q m'.
Proof.
  intros.
  apply H1.
  eapply pred_apply_crash_xform; eauto.
Qed.


Definition possible_sync AT AEQ V (m m' : @mem AT AEQ (V * list V)) :=
  forall a, (m a = None /\ m' a = None) \/
  (exists v l l', m a = Some (v, l) /\ m' a = Some (v, l') /\ incl l' l).

Theorem possible_sync_refl : forall AT AEQ V (m: @mem AT AEQ (V * list V)),
    possible_sync m m.
Proof.
  unfold possible_sync; intros.
  destruct (m a); intuition eauto 10 using incl_refl.
Qed.

Theorem possible_sync_trans : forall AT AEQ V (m1 m2 m3 : @mem AT AEQ (V * list V)),
  possible_sync m1 m2 ->
  possible_sync m2 m3 ->
  possible_sync m1 m3.
Proof.
  unfold possible_sync; intros.
  specialize (H a).
  specialize (H0 a).
  destruct (m1 a); intuition try congruence; repeat deex; try congruence.
  right.
  rewrite H0 in H1; inversion H1; subst.
  do 3 eexists; intuition eauto.
  eapply incl_tran; eauto.
Qed.

Theorem possible_sync_sync_mem : forall AT AEQ V (m : @mem AT AEQ (V * list V)),
  possible_sync m (sync_mem m).
Proof.
  unfold possible_sync, sync_mem; intros.
  destruct (m a); intuition.
  right;
  repeat eexists.
  apply incl_nil.
Qed.

Theorem possible_sync_after_sync : forall A AEQ V (m m': @mem A AEQ (V * list V)),
    possible_sync (sync_mem m) m' ->
    m' = sync_mem m.
Proof.
  unfold possible_sync, sync_mem; intros.
  extensionality a.
  specialize (H a).
  destruct (m a) as [ [] | ];
    intuition eauto;
    repeat deex;
    try congruence.
  inversion H0; subst.
  apply ListUtils.incl_in_nil in H2; subst; eauto.
Qed.

Theorem possible_sync_upd : forall AT AEQ V (m : @mem AT AEQ (V * list V)) a v l l',
  m a = Some (v, l) ->
  incl l' l ->
  possible_sync m (upd m a (v, l')).
Proof.
  unfold possible_sync; intros.
  destruct (AEQ a a0); subst.
  - right. exists v. exists l. exists l'. intuition.
    erewrite upd_eq; eauto.
  - erewrite upd_ne; eauto.
    destruct (m a0); intuition.
    right. do 3 eexists. intuition eauto. apply incl_refl.
Qed.


Ltac xform_simpl :=
  match goal with
  | [ |- pimpl (exis _) _ ] => apply pimpl_exists_l; intro
  end.
Ltac xform' := autorewrite with crash_xform; repeat xform_simpl.
Ltac xform := repeat xform'.


Definition sync_invariant {AT AEQ V} (p: @pred AT AEQ (V * list V)) :=
  (forall m m',
   possible_sync m m' ->
   p m -> p m').

Theorem sync_xform_sync_invariant : forall AT AEQ V (p: @pred AT AEQ (V * list V)),
  sync_invariant p ->
  sync_xform p =p=> p.
Proof.
  unfold sync_invariant, sync_xform, pimpl; intros.
  deex.
  eapply H; eauto.
  apply possible_sync_sync_mem.
Qed.


Theorem ptsto_pimpl_ptsto_subset : forall AT AEQ V (a : AT) vs,
  ((a |-> vs) : @pred AT AEQ (V * list V)) =p=> a |+> vs.
Proof.
  unfold pimpl, ptsto_subset; intros.
  exists (snd vs).
  apply sep_star_lift_apply'.
  destruct vs; exact H.
  firstorder.
Qed.

Theorem ptsto_subset_pimpl_ptsto_ex : forall AT AEQ V (a : AT) vs,
  ((a |+> vs) : @pred AT AEQ (V * list V)) =p=> a |->?.
Proof.
  unfold pimpl, ptsto_subset; intros.
  destruct H.
  apply sep_star_lift_apply in H; intuition.
  eexists; eauto.
Qed.

Theorem ptsto_subset_pimpl_ptsto : forall AT AEQ V (a : AT) v,
  ((a |+> (v, nil)) : @pred AT AEQ (V * list V)) <=p=> a |=> v.
Proof.
  unfold ptsto_subset; intros; split.
  apply pimpl_exists_l; intros; simpl.
  apply sep_star_lift_l; intros.
  erewrite incl_in_nil with (l := x); auto.
  apply pimpl_exists_r; intros; simpl.
  exists nil.
  apply sep_star_lift_r.
  apply pimpl_and_lift; auto.
  apply incl_nil.
Qed.

Theorem ptsto_subset_pimpl : forall AT AEQ V (a : AT) v l l',
  incl l l' ->
  ((a |+> (v, l)) : @pred AT AEQ (V * list V)) =p=> a |+> (v, l').
Proof.
  unfold pimpl, ptsto_subset; intros.
  destruct H0.
  apply sep_star_lift_apply in H0; intuition.
  eexists. apply sep_star_lift_apply'; eauto.
  eapply incl_tran; eauto.
Qed.

Theorem crash_xform_ptsto_subset' : forall AT AEQ V a v,
  @crash_xform AT AEQ V (a |+> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |+> (v', nil).
Proof.
  intros; rewrite crash_xform_ptsto_subset.
  apply pimpl_exists_l; intros.
  rewrite ptsto_pimpl_ptsto_subset.
  apply pimpl_exists_r; exists x; auto.
Qed.

Theorem ptsto_sync_mem : forall AT AEQ V a vs  v (m: @mem AT AEQ (V * list V)),
  (a |-> vs)%pred m ->
  v = fst vs ->
  (a |-> (v, nil))%pred (sync_mem m).
Proof.
  unfold sync_mem, ptsto; destruct vs; intuition; subst.
  rewrite H1; simpl; auto.
  rewrite H2 by eauto; auto.
Qed.

Theorem possible_sync_ptsto : forall AT AEQ V a v l (m m' : @mem AT AEQ (V * list V)),
  possible_sync m m' ->
  (a |-> (v, l))%pred m ->
  (exists l', a |-> (v, l') * [[ incl l' l ]])%pred m'.
Proof.
  unfold possible_sync, ptsto; intuition;
    remember H as H'; clear HeqH'; specialize (H' a); intuition; try congruence.
  repeat deex. rewrite H1 in H3. inversion H3; subst.
  eexists.
  apply sep_star_lift_apply'; eauto.
  intuition.
  specialize (H a'); intuition.
  repeat deex. rewrite H2 in H6; congruence.
Qed.


Theorem sync_invariant_ptsto_subset : forall AT AEQ V a vs,
  @sync_invariant AT AEQ V (a |+> vs)%pred.
Proof.
  unfold sync_invariant, pimpl, ptsto_subset, lift; intuition.
  destruct H0.
  apply sep_star_lift_apply in H0; intuition.
  eapply possible_sync_ptsto in H; [ | eauto ].
  destruct H.
  apply sep_star_lift_apply in H; intuition.
  eexists.
  apply sep_star_lift_apply'. eauto.
  eapply incl_tran; eauto.
Qed.

Theorem sync_invariant_ptsto_any : forall AT AEQ V a,
  @sync_invariant AT AEQ V (a |->?)%pred.
Proof.
  unfold sync_invariant, pimpl; intros.
  destruct H0; destruct x.
  eapply possible_sync_ptsto in H; [ | eauto ].
  destruct H.
  apply sep_star_lift_apply in H; intuition.
  eexists; eauto.
Qed.

Theorem sync_xform_ptsto_subset_precise : forall AT AEQ V a vs,
  @sync_xform AT AEQ V (a |+> vs) =p=> a |=> (fst vs).
Proof.
  unfold sync_xform, ptsto_subset, pimpl; intros.
  deex. destruct H0. apply sep_star_lift_apply in H; intuition.
  eapply ptsto_sync_mem; eauto.
Qed.

Theorem sync_xform_ptsto_subset_preserve : forall AT AEQ V a vs,
  @sync_xform AT AEQ V (a |+> vs) =p=> a |+> vs.
Proof.
  intros.
  rewrite sync_xform_ptsto_subset_precise.
  unfold ptsto_subset, pimpl; intros.
  exists nil.
  apply sep_star_lift_apply'; eauto.
  apply incl_nil.
Qed.

Theorem sync_invariant_ptsto_nil : forall AT AEQ V a v,
  @sync_invariant AT AEQ V (a |=> v)%pred.
Proof.
  unfold sync_invariant, pimpl; intros.
  eapply possible_sync_ptsto in H; [ | eauto ].
  destruct H. apply sep_star_lift_apply in H; intuition.
  apply incl_in_nil in H2; subst; eauto.
Qed.

Theorem sync_invariant_emp : forall AT AEQ V,
  @sync_invariant AT AEQ V emp.
Proof.
  unfold sync_invariant, possible_sync, emp, pimpl; intros.
  specialize (H0 a).
  specialize (H a).
  intuition.
  repeat deex. congruence.
Qed.

Theorem sync_xform_or_dist : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  sync_xform (p \/ q) <=p=> sync_xform p \/ sync_xform q.
Proof.
  firstorder.
Qed.

Theorem sync_xform_and_dist : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  sync_xform (p /\ q) =p=> sync_xform p /\ sync_xform q.
Proof.
  firstorder.
Qed.

Theorem sync_xform_lift_empty : forall AT AEQ V (P : Prop),
  @sync_xform AT AEQ V [[ P ]] <=p=> [[ P ]].
Proof.
  unfold sync_xform, sync_mem, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  rewrite H2; eauto.
  exists m; intuition.
  apply functional_extensionality; intros.
  rewrite H1; auto.
Qed.

Theorem sync_xform_emp : forall AT AEQ V,
  @sync_xform AT AEQ V emp <=p=> emp.
Proof.
  unfold sync_xform, sync_mem, emp; split; intro; intros; repeat deex.
  destruct (m' a) eqn:?; congruence.
  eexists; split; eauto.
  apply functional_extensionality; intros.
  destruct (m x) eqn:?; congruence.
Qed.

Lemma sync_mem_union : forall AT AEQ V (m1 m2 : @mem AT AEQ (V * list V)),
  sync_mem (mem_union m1 m2) = mem_union (sync_mem m1) (sync_mem m2).
Proof.
  unfold mem_union, sync_mem; intros.
  apply functional_extensionality; intros.
  destruct (m1 x); auto.
  destruct p; auto.
Qed.

Lemma sync_mem_disjoint1 : forall AT AEQ V (m1 m2 : @mem AT AEQ (V * list V)),
  mem_disjoint m1 m2 -> mem_disjoint (sync_mem m1) (sync_mem m2).
Proof.
  unfold mem_disjoint, sync_mem; intuition.
  apply H.
  repeat deex.
  exists a.
  destruct (m1 a); try congruence.
  destruct (m2 a); try congruence.
  eauto.
Qed.

Lemma sync_mem_disjoint2 : forall AT AEQ V (m1 m2 : @mem AT AEQ (V * list V)),
  mem_disjoint (sync_mem m1) (sync_mem m2) -> mem_disjoint m1 m2.
Proof.
  unfold mem_disjoint, sync_mem; intuition.
  apply H.
  repeat deex.
  exists a. destruct v1. destruct v2.
  rewrite H1. rewrite H2. eauto.
Qed.

Hint Resolve sync_mem_disjoint1.
Hint Resolve sync_mem_disjoint2.
Hint Resolve sync_mem_union.

Theorem sync_xform_sep_star_dist : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  sync_xform (p * q) <=p=> sync_xform p * sync_xform q.
Proof.
  unfold_sep_star; unfold sync_xform, piff, pimpl; split; intros; repeat deex.
  - exists (sync_mem m1). exists (sync_mem m2). intuition eauto.
  - exists (mem_union m'0 m'); intuition.
    do 2 eexists; intuition.
Qed.

Theorem sync_xform_exists_comm : forall AT AEQ V T (p: T -> @pred AT AEQ (V * list V)),
  sync_xform (exists x, p x) <=p=> exists x, sync_xform (p x).
Proof.
  split; unfold sync_xform, exis, pimpl; intros;
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem sync_xform_forall_comm : forall AT AEQ V T (p: T -> @pred AT AEQ (V * list V)),
  sync_xform (foral x, p x) =p=> foral x, sync_xform (p x).
Proof.
  unfold sync_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem sync_xform_pimpl : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  p =p=> q ->
  sync_xform p =p=> sync_xform q.
Proof.
  unfold sync_xform, pimpl; intros.
  deex; eauto.
Qed.


Instance sync_xform_pimpl_proper:
  forall AT AEQ V, Proper (pimpl ==> pimpl) (@sync_xform AT AEQ V).
Proof.
  firstorder.
Qed.

Instance sync_xform_flip_pimpl_proper:
  forall AT AEQ V, Proper (Basics.flip pimpl ==> Basics.flip pimpl) (@sync_xform AT AEQ V).
Proof.
  firstorder.
Qed.

Instance sync_xform_piff_proper:
  forall AT AEQ V, Proper (piff ==> piff) (@sync_xform AT AEQ V).
Proof.
  firstorder.
Qed.

Instance sync_invariant_piff_proper:
  forall AT AEQ V, Proper (piff ==> Basics.impl) (@sync_invariant AT AEQ V).
Proof.
  firstorder.
Qed.

Theorem sync_xform_diskIs:  forall AT AEQ V (m: @mem AT AEQ (V * list V)),
  sync_xform (diskIs m) =p=> diskIs (sync_mem m).
Proof.
  unfold sync_xform, diskIs, pimpl; intros.
  deex; auto.
Qed.

Theorem sync_xform_pred_apply :  forall AT AEQ V (p: @pred AT AEQ (V * list V)) m,
  p m -> (sync_xform p) (sync_mem m).
Proof.
  firstorder.
Qed.

Theorem sync_mem_idem : forall AT AEQ V (m : @mem AT AEQ (V * list V)),
  sync_mem (sync_mem m) = sync_mem m.
Proof.
  unfold sync_mem; intros.
  apply functional_extensionality; intros.
  destruct (m x); auto.
  destruct p; auto.
Qed.

Theorem sync_xform_idem :  forall AT AEQ V (p: @pred AT AEQ (V * list V)),
  sync_xform (sync_xform p) <=p=> sync_xform p.
Proof.
  unfold sync_xform, piff, pimpl; split; intros; repeat deex.
  - exists m'0; intuition. apply sync_mem_idem.
  - eexists; split.
    exists m'; intuition.
    rewrite sync_mem_idem; auto.
Qed.

Theorem sync_invariant_exists : forall AT AEQ V T (p: T -> @pred AT AEQ (V * list V)),
  (forall v, sync_invariant (p v)) ->
  sync_invariant (exists v, p v)%pred.
Proof.
  unfold sync_invariant; intros.
  destruct H1. eexists. eauto.
Qed.

Theorem possible_sync_mem_union : forall AT AEQ V (ma mb m' : @mem AT AEQ (V * list V)),
  possible_sync (mem_union ma mb) m'
  -> @mem_disjoint _ _ _ ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_sync ma ma' /\ possible_sync mb mb'.
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; apply functional_extensionality; intros.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_sync in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
  - intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
Qed.

Theorem possible_sync_disjoint : forall AT AEQ V (ma mb ma' mb' : @mem AT AEQ (V * list V)),
  @mem_disjoint _ _ _ ma' mb'
  -> possible_sync ma ma'
  -> possible_sync mb mb'
  -> @mem_disjoint _ _ _ ma mb.
Proof.
  unfold mem_disjoint; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.

Theorem possible_sync_union : forall AT AEQ V (ma mb ma' mb' : @mem AT AEQ (V * list V)),
    possible_sync ma ma'
  -> possible_sync mb mb'
  -> possible_sync (mem_union ma mb) (mem_union ma' mb').
Proof.
  unfold possible_sync, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 3 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 3 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 3 eexists. intuition.
Qed.


Theorem sync_invariant_sep_star : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p * q)%pred.
Proof.
  unfold_sep_star; unfold sync_invariant; intros; repeat deex.
  apply possible_sync_mem_union in H1; eauto; repeat deex.
  do 2 eexists. intuition eauto.
Qed.

Theorem sync_invariant_lift_empty : forall AT AEQ V P,
  @sync_invariant AT AEQ V [[ P ]]%pred.
Proof.
  unfold sync_invariant; intros.
  apply star_emp_pimpl; apply pimpl_star_emp in H0.
  apply sep_star_lift_apply in H0. apply sep_star_lift_apply'; intuition.
  eapply sync_invariant_emp; eauto.
Qed.

Theorem sync_invariant_and : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p /\ q)%pred.
Proof.
  firstorder.
Qed.

Theorem sync_invariant_or : forall AT AEQ V (p q: @pred AT AEQ (V * list V)),
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p \/ q)%pred.
Proof.
  firstorder.
Qed.

Lemma possible_sync_possible_crash_trans : forall AT AEQ V m m1 m2,
  @possible_crash AT AEQ V m m1 ->
  possible_sync m1 m2 ->
  possible_crash m m2.
Proof.
  unfold possible_sync, possible_crash; intros.
  specialize (H a); specialize (H0 a); intuition; repeat deex; try congruence.
  right.
  do 2 eexists; intuition eauto.
  rewrite H0 in H1; inversion H1; subst.
  rewrite H.
  rewrite incl_in_nil with (l := l'); eauto.
Qed.

Lemma incl_vsmerge : forall V l l' (v: V),
    incl l l' ->
    incl (vsmerge (v, l)) (vsmerge (v, l')).
Proof.
  induction l'; simpl; intros.
  - destruct l.
    apply incl_refl.
    unfold vsmerge; simpl in *; intuition.
  - unfold vsmerge; simpl.
    unfold incl; simpl in *; intros; intuition eauto.
    specialize (H a0); simpl in *; intuition eauto.
Qed.

Lemma possible_crash_possible_sync_trans : forall AT AEQ V m m1 m2,
    @possible_sync AT AEQ V m m1 ->
    possible_crash m1 m2 ->
    possible_crash m m2.
Proof.
  unfold possible_sync, possible_crash; intros.
  specialize (H a); specialize (H0 a); intuition; repeat deex; try congruence.
  right.
  do 2 eexists; intuition eauto.
  rewrite H0 in H1; inversion H1; subst.
  eapply incl_vsmerge; eauto.
Qed.

Theorem sync_invariant_crash_xform : forall AT AEQ V (F: @pred AT AEQ (V * list V)),
  sync_invariant (crash_xform F).
Proof.
  unfold sync_invariant, crash_xform; intros; deex.
  eexists; split; eauto.
  eapply possible_sync_possible_crash_trans; eauto.
Qed.


Hint Resolve sync_invariant_ptsto_subset.
Hint Resolve sync_invariant_ptsto_any.
Hint Resolve sync_invariant_ptsto_nil.
Hint Resolve sync_invariant_emp.
Hint Resolve sync_invariant_exists.
Hint Resolve sync_invariant_sep_star.
Hint Resolve sync_invariant_lift_empty.
Hint Resolve sync_invariant_and.
Hint Resolve sync_invariant_or.
Hint Resolve sync_invariant_crash_xform.

Theorem upd_sync_invariant : forall AT AEQ V (p: @pred AT AEQ (V * list V)) m a v l l',
  sync_invariant p ->
  p m ->
  m a = Some (v, l) ->
  incl l' l ->
  p (upd m a (v, l')).
Proof.
  intros.
  eapply H; eauto.
  eapply possible_sync_upd; eauto.
Qed.

Theorem ptsto_subset_valid : forall AT AEQ V a vs F (m : @mem AT AEQ (V * list V)),
  (a |+> vs * F)%pred m ->
  exists l, m a = Some (fst vs, l) /\ incl l (snd vs).
Proof.
  unfold ptsto_subset, ptsto; unfold_sep_star.
  intros; repeat deex.
  destruct H1. repeat deex.
  eexists; split.
  apply mem_union_addr; eauto.
  apply mem_union_addr; eauto.
  apply H5.
Qed.

Theorem ptsto_subset_valid' : forall AT AEQ V a vs F (m : @mem AT AEQ (V * list V)),
  (F * a |+> vs)%pred m ->
  exists l, m a = Some (fst vs, l) /\ incl l (snd vs).
Proof.
  intros.
  apply sep_star_comm in H.
  eapply ptsto_subset_valid; eauto.
Qed.

Lemma ptsto_subset_upd : forall AT AEQ V (F: @pred AT AEQ (V * list V)) v0 v a m vs vs' vs0,
  (F * a |+> (v0, vs0))%pred m ->
  incl vs' vs ->
  (F * a |+> (v, vs))%pred (upd m a (v, vs')).
Proof.
  unfold ptsto_subset; simpl in *; intros.
  apply sep_star_comm in H.
  apply pimpl_exists_r_star_r in H.
  destruct H.
  apply sep_star_assoc in H.
  eapply ptsto_upd with (v := (v, vs')) in H.
  setoid_rewrite sep_star_comm in H.
  apply sep_star_assoc in H.
  apply sep_star_lift_apply in H; destruct H.

  apply sep_star_comm.
  apply pimpl_exists_r_star.
  eapply pimpl_exists_r; eauto.
  setoid_rewrite sep_star_comm.
  apply sep_star_assoc; apply sep_star_comm.
  apply sep_star_lift_apply'; eauto.
Qed.


Lemma sync_invariant_sync_mem_apply:
 forall AT AEQ V (P: @pred AT AEQ (V * list V)) m,
    P m ->
    sync_invariant P ->
    P (sync_mem m).
Proof.
  unfold sync_invariant; intros.
  eapply H0; eauto.
  apply possible_sync_sync_mem.
Qed.


