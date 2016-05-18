Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import Morphisms.
Require Import AsyncDisk.
Require Import Arith.

Set Implicit Arguments.


Definition ptsto_subset {AT AEQ} (a : AT) (vs : valuset) : @pred AT AEQ valuset :=
  (exists old, a |-> (fst vs, old) /\ [ incl old (snd vs) ])%pred.

Notation "a |=> v" := (a |-> ((v, nil) : valuset))%pred (at level 35) : pred_scope.
Notation "a |~> v" := (exists old, a |-> ((v, old) : valuset))%pred (at level 35) : pred_scope.
Notation "a |+> v" := (ptsto_subset a v) (at level 35) : pred_scope.


Definition rawpred := @pred addr addr_eq_dec valuset.


(* if [p] was true before a crash, then [crash_xform p] is true after a crash *)
Definition crash_xform (p : rawpred) : rawpred :=
  fun m => exists m', p m' /\ possible_crash m' m.

(* if [p] was true before a sync, then [sync_xform p] is true after a sync *)
Definition sync_xform (p : rawpred) : rawpred :=
  fun m => exists m', p m' /\ m = sync_mem m'.


(* Specialized relations for [@pred valuset], to deal with async IO *)

Theorem crash_xform_apply : forall (p : rawpred) (m m' : rawdisk), possible_crash m m'
  -> p m
  -> crash_xform p m'.
Proof.
  unfold crash_xform; eauto.
Qed.

Theorem possible_crash_mem_union : forall (ma mb m' : rawdisk), possible_crash (mem_union ma mb) m'
  -> @mem_disjoint _ addr_eq_dec _ ma mb
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

Theorem possible_crash_disjoint : forall (ma mb ma' mb' : rawdisk),
  @mem_disjoint _ addr_eq_dec _ ma' mb'
  -> possible_crash ma ma'
  -> possible_crash mb mb'
  -> @mem_disjoint _ addr_eq_dec _ ma mb.
Proof.
  unfold mem_disjoint, possible_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.

Theorem possible_crash_union : forall (ma mb ma' mb' : rawdisk), possible_crash ma ma'
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

Theorem possible_crash_trans : forall (ma mb mc : rawdisk),
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


Lemma possible_crash_notindomain : forall AEQ (m m' : @mem _ AEQ _) a,
  possible_crash m m' ->
  notindomain a m ->
  notindomain a m'.
Proof.
  unfold possible_crash; intuition.
  specialize (H a); intuition; repeat deex; congruence.
Qed.


Lemma possible_crash_upd : forall m m' a v vs,
  possible_crash m m' ->
  In v (vsmerge vs) ->
  possible_crash (upd m a vs) (upd m' a (v, nil)).
Proof.
  unfold possible_crash; intuition.
  destruct (addr_eq_dec a a0); subst.
  repeat rewrite upd_eq; auto.
  specialize (H a0); intuition; right; eexists; eauto.
  repeat rewrite upd_ne; auto.
Qed.

Definition synced_mem (m : rawdisk) :=
  forall a, m a = None \/ exists v, m a = Some (v, nil).

Lemma synced_mem_snd_nil : forall m a vs,
  synced_mem m ->
  m a = Some vs ->
  snd vs = nil.
Proof.
  unfold synced_mem; intuition.
  specialize (H a); intuition; try congruence.
  destruct H1.
  rewrite H in H0; inversion H0; auto.
Qed.

Theorem possible_crash_synced : forall m m',
  possible_crash m m' ->
  synced_mem m'.
Proof.
  unfold possible_crash, synced_mem; intuition.
  specialize (H a); intuition.
  right; repeat deex.
  eexists; eauto.
Qed.

Theorem possible_crash_refl : forall m,
  synced_mem m ->
  possible_crash m m.
Proof.
  unfold synced_mem, possible_crash; intuition.
  specialize (H a); intuition.
  destruct H0; right.
  do 2 eexists; simpl; intuition eauto.
Qed.


Lemma possible_crash_emp_l : forall (m m' : @mem _ addr_eq_dec _),
  possible_crash m m' ->
  emp m' ->
  emp m.
Proof.
  unfold possible_crash, emp; intros.
  specialize (H a); intuition; repeat deex.
  congruence.
Qed.

Lemma possible_crash_emp_r : forall (m m' : @mem _ addr_eq_dec _),
  possible_crash m m' ->
  emp m ->
  emp m'.
Proof.
  unfold possible_crash, emp; intros.
  specialize (H a); intuition; repeat deex.
  congruence.
Qed.

Lemma possible_crash_ptsto_upd_incl : forall F m m' a vs vs',
  (F * a |-> vs)%pred m ->
  possible_crash m m' ->
  incl (vsmerge vs) (vsmerge vs') ->
  possible_crash (upd m a vs') m'.
Proof.
  unfold possible_crash, vsmerge; simpl; intros.
  apply ptsto_valid' in H.
  destruct vs, vs'; simpl in *.
  destruct (addr_eq_dec a0 a); subst.

  - specialize (H0 a); intuition.
    left; congruence.
    right; rewrite upd_eq by auto; repeat deex; destruct vs; simpl in *.
    rewrite H in H2; inversion H2; subst.
    exists (w0, l0); exists w1; intuition.
    rewrite H in H2; inversion H2; subst.
    exists (w0, l0); exists v'; intuition.

  - rewrite upd_ne by auto.
    specialize (H0 a0); intuition.
Qed.

Lemma possible_crash_upd_incl : forall m m' a v v0,
  possible_crash (upd m a v) m' ->
  m a = Some v0 ->
  incl (vsmerge v) (vsmerge v0) ->
  possible_crash m m'.
Proof.
  unfold possible_crash, vsmerge; intuition.
  destruct (addr_eq_dec a a1); subst; simpl in *.
  - specialize (H a1); intuition; right;
    rewrite upd_eq in *; try congruence.
    repeat deex.
    destruct vs, v0; inversion H2; subst; simpl in *.
    exists (w0, l0), w; intuition.
    destruct vs, v0; inversion H2; subst; simpl in *.
    exists (w0, l0), v'; intuition.
  - specialize (H a1); intuition; rewrite upd_ne in *; auto.
Qed.

Lemma possible_crash_upd_nil : forall m m' a v0,
  possible_crash (upd m a (fst v0, nil)) m' ->
  m a = Some v0 ->
  possible_crash m m'.
Proof.
  intros.
  eapply possible_crash_upd_incl; eauto.
  unfold vsmerge; simpl.
  apply incl_cons2, incl_nil.
Qed.


Lemma possible_crash_ptsto_upd_postfix : forall F m m' a v vs vs',
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

Theorem crash_xform_sep_star_dist : forall (p q : rawpred),
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

Theorem crash_xform_or_dist : forall (p q : rawpred),
  crash_xform (p \/ q) <=p=> crash_xform p \/ crash_xform q.
Proof.
  firstorder.
Qed.

Theorem crash_xform_lift_empty : forall (P : Prop),
  @crash_xform [[ P ]] <=p=> [[ P ]].
Proof.
  unfold crash_xform, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  specialize (H1 a); destruct H1; intuition.
  repeat deex; congruence.
  eexists; intuition.
Qed.

Theorem crash_xform_sep_star_apply : forall (p q : rawpred) (m m' : mem), possible_crash m m'
  -> (p * q)%pred m
  -> (crash_xform p * crash_xform q)%pred m'.
Proof.
  unfold_sep_star; intros; repeat deex.
  edestruct possible_crash_mem_union; try eassumption; repeat deex.
  do 2 eexists; repeat split; auto; unfold crash_xform; eexists; split; eauto.
Qed.

Theorem crash_xform_exists_comm : forall T (p : T -> rawpred),
  crash_xform (exists x, p x) <=p=> exists x, crash_xform (p x).
Proof.
  split; unfold crash_xform, exis, pimpl; intros;
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem crash_xform_forall_comm : forall T (p : T -> rawpred),
  crash_xform (foral x, p x) =p=> foral x, crash_xform (p x).
Proof.
  unfold crash_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem crash_xform_ptsto: forall a v,
  crash_xform (a |-> v) =p=> exists v', [[ In v' (vsmerge v) ]] * a |=> v'.
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

Theorem crash_xform_ptsto_r: forall a v vs,
  In v (vsmerge vs) ->
  a |=> v =p=> crash_xform (a |-> vs).
Proof.
  unfold crash_xform, possible_crash, ptsto, pimpl; intros.
  exists (upd empty_mem a vs).
  intuition.
  rewrite upd_eq; auto.
  rewrite upd_ne; auto.
  destruct (eq_nat_dec a a0); subst.
  - right. rewrite upd_eq; auto. exists vs. exists v. intuition.
  - left. rewrite upd_ne; auto.
Qed.


Theorem crash_xform_ptsto_exis : forall a,
  crash_xform ( a |->? ) =p=> a |->?.
Proof.
  intros.
  rewrite crash_xform_exists_comm.
  apply pimpl_exists_l; intro.
  rewrite crash_xform_ptsto.
  apply pimpl_exists_l; intro.
  apply pimpl_exists_r.
  exists (x0, nil).
  rewrite sep_star_comm.
  apply sep_star_lift_l; intros; auto.
Qed.


Theorem crash_xform_pimpl : forall (p q : rawpred), p =p=>q
  -> crash_xform p =p=> crash_xform q.
Proof.
  firstorder.
Qed.

Instance crash_xform_pimpl_proper:
  Proper (pimpl ==> pimpl) crash_xform.
Proof.
  firstorder.
Qed.

Instance crash_xform_flip_pimpl_proper:
  Proper (Basics.flip pimpl ==> Basics.flip pimpl) crash_xform.
Proof.
  firstorder.
Qed.

Instance crash_xform_piff_proper:
  Proper (piff ==> piff) crash_xform.
Proof.
  firstorder.
Qed.

Theorem crash_invariant_emp:
  crash_xform emp =p=> emp.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl; repeat deex; intuition; repeat deex.
  destruct (H1 a); [ intuition | repeat deex; congruence ].
Qed.

Theorem crash_invariant_emp_r:
  emp =p=> crash_xform emp.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl. intros.
  exists empty_mem. intuition.
Qed.

Theorem crash_invariant_ptsto: forall a v,
  crash_xform (a |=> v) =p=> a |=> v.
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
  forall a v (F : rawpred) m,
  (a |=> v * F)%pred m
  -> m a = Some (v, nil).
Proof.
  intros.
  eapply ptsto_valid; eauto.
Qed.

Lemma ptsto_cur_valid:
  forall a v (F : rawpred) m,
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

Lemma crash_xform_diskIs: forall m,
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

Lemma crash_xform_diskIs_r: forall m m',
  possible_crash m m' ->
  diskIs m' =p=> crash_xform (diskIs m).
Proof.
  unfold crash_xform, pimpl, diskIs.
  intros; subst; firstorder.
Qed.

Lemma crash_xform_diskIs_piff: forall m,
  crash_xform (diskIs m) <=p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
Proof.
  split.
  apply crash_xform_diskIs.
  apply pimpl_exists_l; intro.
  rewrite sep_star_comm.
  apply sep_star_lift_l; intro.
  apply crash_xform_diskIs_r; auto.
Qed.

Lemma possible_crash_mem_except : forall m1 m2 a,
  possible_crash m1 m2 ->
  possible_crash (mem_except m1 a) (mem_except m2 a).
Proof.
  unfold possible_crash, mem_except; intuition.
  specialize (H a0).
  destruct (addr_eq_dec a0 a); intuition.
Qed.

Lemma mem_except_upd : forall AT AEQ V (m : @mem AT AEQ V) a v,
  mem_except m a = mem_except (upd m a v) a.
Proof.
  unfold mem_except, upd; intuition.
  apply functional_extensionality; intros.
  destruct (AEQ x a); intuition.
Qed.

Lemma possible_crash_upd_mem_except : forall m1 m2 a v,
  possible_crash m1 (upd m2 a v) ->
  possible_crash (mem_except m1 a) (mem_except m2 a).
Proof.
  intros.
  eapply possible_crash_mem_except in H.
  rewrite <- mem_except_upd in H.
  auto.
Qed.


Lemma possible_crash_eq : forall a b c,
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

Lemma crash_xform_diskIs_trans : forall d x d',
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


Lemma crash_xform_diskIs_eq : forall F a b,
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


Lemma crash_xform_diskIs_pred : forall (F : pred) m,
  F m -> crash_xform (diskIs m) =p=> crash_xform F.
Proof.
  unfold crash_xform, diskIs.
  unfold pimpl; intros.
  destruct H0; intuition subst.
  eexists; eauto.
Qed.

Lemma crash_xform_ptsto_or : forall (a : addr) (vs : valuset),
  crash_xform (a |-> vs) <=p=> crash_xform (a |-> vs \/ a |=> (fst vs)).
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


Lemma crash_xform_ptsto_vsmerge :  forall (a : addr) (vs : valuset) (v : valu),
  crash_xform (a |-> (v, vsmerge vs)) <=p=> crash_xform (a |-> vs \/ a |-> (v, vsmerge vs)).
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


Theorem crash_xform_idem_l : forall (p : rawpred), 
  crash_xform (crash_xform p) =p=> crash_xform p.
Proof.
  unfold crash_xform, pimpl; intros.
  repeat deex; eexists; intuition eauto.
  eapply possible_crash_trans; eauto.
Qed.

Theorem crash_xform_idem_r : forall (p : rawpred),
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

Theorem crash_xform_idem : forall (p : rawpred),
  crash_xform (crash_xform p) <=p=> crash_xform p.
Proof.
  split.
  apply crash_xform_idem_l.
  apply crash_xform_idem_r.
Qed.

Theorem crash_xform_synced : forall p m,
  crash_xform p m ->
  synced_mem m.
Proof.
  unfold crash_xform; intros.
  repeat deex.
  eapply possible_crash_synced; eauto.
Qed.

Theorem crash_xform_possible_crash_refl : forall p m,
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

Lemma pred_apply_crash_xform : forall (p : rawpred) m m',
  possible_crash m m' -> p m -> (crash_xform p) m'.
Proof.
  unfold pimpl, crash_xform; eauto.
Qed.

Lemma pred_apply_crash_xform_pimpl : forall (p q : rawpred) m m',
  possible_crash m m' -> p m -> crash_xform p =p=> q -> q m'.
Proof.
  intros.
  apply H1.
  eapply pred_apply_crash_xform; eauto.
Qed.


Ltac xform_simpl :=
  match goal with
  | [ |- pimpl (exis _) _ ] => apply pimpl_exists_l; intro
  end.
Ltac xform' := autorewrite with crash_xform; repeat xform_simpl.
Ltac xform := repeat xform'.


Definition sync_invariant p : Prop := sync_xform p =p=> p.

Theorem ptsto_pimpl_ptsto_subset : forall AT AEQ (a : AT) vs,
  ((a |-> vs) : @pred AT AEQ _) =p=> a |+> vs.
Proof.
  unfold pimpl, ptsto_subset; intros.
  exists (snd vs).
  split.
  destruct vs; exact H.
  firstorder.
Qed.

Theorem ptsto_sync_mem : forall (a : addr) (vs : valuset) v m,
  (a |-> vs)%pred m ->
  v = fst vs ->
  (a |-> (v, nil) : @pred _ addr_eq_dec _)%pred (sync_mem m).
Proof.
  unfold sync_mem, ptsto; destruct vs; intuition; subst.
  rewrite H1; simpl; auto.
  rewrite H2 by eauto; auto.
Qed.

Theorem sync_xform_ptsto_subset_preserve : forall a vs,
  sync_invariant (a |+> vs)%pred.
Proof.
  unfold sync_invariant, pimpl, sync_xform, ptsto_subset; intros.
  deex. destruct H0. destruct H.
  exists nil.
  split.
  eapply ptsto_sync_mem; eauto.
  intro; intros.
  inversion H1.
Qed.

Theorem sync_xform_ptsto_any : forall a,
  sync_invariant (a |->?)%pred.
Proof.
  unfold sync_invariant, pimpl, sync_xform; intros; deex.
  destruct H0. eexists.
  eapply ptsto_sync_mem; eauto.
Qed.

Theorem sync_xform_ptsto_subset_precise : forall a vs,
  sync_xform (a |+> vs) =p=> a |=> (fst vs).
Proof.
  unfold sync_xform, ptsto_subset, pimpl; intros.
  deex. destruct H0. destruct H.
  eapply ptsto_sync_mem; eauto.
Qed.

Theorem sync_xform_ptsto_nil : forall a v,
  sync_invariant (a |=> v)%pred.
Proof.
  unfold sync_invariant, sync_xform, pimpl; intros; deex.
  eapply ptsto_sync_mem; eauto.
Qed.

Theorem sync_xform_emp :
  sync_invariant emp.
Proof.
  unfold sync_invariant, sync_xform, sync_mem, emp, pimpl; intros; deex.
  rewrite H0; auto.
Qed.

Theorem sync_xform_or_dist : forall p q,
  sync_xform (p \/ q) <=p=> sync_xform p \/ sync_xform q.
Proof.
  firstorder.
Qed.

Theorem sync_xform_lift_empty : forall (P : Prop),
  @sync_xform [[ P ]] <=p=> [[ P ]].
Proof.
  unfold sync_xform, sync_mem, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  rewrite H2; eauto.
  exists m; intuition.
  apply functional_extensionality; intros.
  rewrite H1; auto.
Qed.

Lemma sync_mem_union : forall AT AEQ (m1 m2 : @mem AT AEQ _),
  sync_mem (mem_union m1 m2) = mem_union (sync_mem m1) (sync_mem m2).
Proof.
  unfold mem_union, sync_mem; intros.
  apply functional_extensionality; intros.
  destruct (m1 x); auto.
  destruct p; auto.
Qed.

Lemma sync_mem_disjoint1 : forall AT AEQ (m1 m2 : @mem AT AEQ _),
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

Lemma sync_mem_disjoint2 : forall AT AEQ (m1 m2 : @mem AT AEQ _),
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

Theorem sync_xform_sep_star_dist : forall (p q : rawpred),
  sync_xform (p * q) <=p=> sync_xform p * sync_xform q.
Proof.
  unfold_sep_star; unfold sync_xform, piff, pimpl; split; intros; repeat deex.
  - exists (sync_mem m1). exists (sync_mem m2). intuition eauto.
  - exists (mem_union m'0 m'); intuition.
    do 2 eexists; intuition.
Qed.

Theorem sync_xform_exists_comm : forall T (p : T -> rawpred),
  sync_xform (exists x, p x) <=p=> exists x, sync_xform (p x).
Proof.
  split; unfold sync_xform, exis, pimpl; intros;
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem sync_xform_forall_comm : forall T (p : T -> rawpred),
  sync_xform (foral x, p x) =p=> foral x, sync_xform (p x).
Proof.
  unfold sync_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem sync_xform_pimpl : forall p q,
  p =p=> q ->
  sync_xform p =p=> sync_xform q.
Proof.
  unfold sync_xform, pimpl; intros.
  deex; eauto.
Qed.

Instance sync_xform_pimpl_proper:
  Proper (pimpl ==> pimpl) sync_xform.
Proof.
  firstorder.
Qed.

Instance sync_xform_flip_pimpl_proper:
  Proper (Basics.flip pimpl ==> Basics.flip pimpl) sync_xform.
Proof.
  firstorder.
Qed.

Instance sync_xform_piff_proper:
  Proper (piff ==> piff) sync_xform.
Proof.
  firstorder.
Qed.

Theorem sync_xform_diskIs: forall m,
  sync_xform (diskIs m) =p=> diskIs (sync_mem m).
Proof.
  unfold sync_xform, diskIs, pimpl; intros.
  deex; auto.
Qed.

Theorem sync_xform_pred_apply : forall (p : rawpred) m,
  p m -> (sync_xform p) (sync_mem m).
Proof.
  firstorder.
Qed.

Theorem sync_mem_idem : forall AT AEQ (m : @mem AT AEQ _),
  sync_mem (sync_mem m) = sync_mem m.
Proof.
  unfold sync_mem; intros.
  apply functional_extensionality; intros.
  destruct (m x); auto.
  destruct p; auto.
Qed.

Theorem sync_xform_idem : forall p,
  sync_xform (sync_xform p) <=p=> sync_xform p.
Proof.
  unfold sync_xform, piff, pimpl; split; intros; repeat deex.
  - exists m'0; intuition. apply sync_mem_idem.
  - eexists; split.
    exists m'; intuition.
    rewrite sync_mem_idem; auto.
Qed.

Theorem sync_invariant_exists : forall T (p : T -> rawpred),
  (forall v, sync_invariant (p v)) ->
  sync_invariant (exists v, p v)%pred.
Proof.
  unfold sync_invariant; intros.
  rewrite sync_xform_exists_comm.
  apply pimpl_exists_l; intros.
  rewrite H.
  exists x; eauto.
Qed.

Theorem sync_invariant_sep_star : forall p q,
  sync_invariant p ->
  sync_invariant q ->
  sync_invariant (p * q)%pred.
Proof.
  unfold sync_invariant; intros.
  rewrite sync_xform_sep_star_dist.
  rewrite H.
  rewrite H0.
  auto.
Qed.

Theorem sync_invariant_lift_empty : forall P,
  sync_invariant [[ P ]]%pred.
Proof.
  unfold sync_invariant; intros.
  rewrite sync_xform_lift_empty.
  auto.
Qed.
