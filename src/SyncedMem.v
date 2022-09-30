Require Import FunctionalExtensionality.
Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Pred.
Require Import Mem.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import Array.
Require Import ListUtils.
Require Import LogReplay.
Require Import GenSepN.
Require Import ListPred.

Import ListNotations.

Definition syncedmem := @Mem.mem _ addr_eq_dec bool.

Definition sm_vs_valid (sm : @Mem.mem _ addr_eq_dec _) vs :=
  forall a, a < length vs -> sm a <> None /\ (sm a = Some true -> vs_synced a vs).

Definition sm_ds_valid (sm : @Mem.mem _ addr_eq_dec _) ds :=
  Forall (sm_vs_valid sm) (fst ds :: snd ds).

Lemma sm_ds_valid_pushd_iff: forall sm ds d,
  sm_ds_valid sm ds /\ sm_vs_valid sm d <-> sm_ds_valid sm (pushd d ds).
Proof.
  unfold pushd, sm_ds_valid, ds_synced.
  split; intuition; cbn in *.
  all: repeat apply Forall_cons.
  all: try solve [eapply Forall_inv; eauto | eapply Forall_cons2; eauto].
  repeat (eapply Forall_cons2; eauto).
  eapply Forall_inv.
  eapply Forall_cons2; eauto.
Qed.

Lemma sm_ds_valid_pushd: forall sm ds d,
  sm_vs_valid sm d ->
  sm_ds_valid sm ds -> sm_ds_valid sm (pushd d ds).
Proof.
  intros.
  apply sm_ds_valid_pushd_iff.
  auto.
Qed.

Lemma sm_ds_valid_pushd_r: forall sm ds d,
  sm_ds_valid sm (pushd d ds) ->
  sm_ds_valid sm ds.
Proof.
  intros.
  rewrite <- sm_ds_valid_pushd_iff in H.
  intuition.
Qed.

Lemma sm_ds_valid_pushd_l: forall sm ds d,
  sm_ds_valid sm (pushd d ds) ->
  sm_vs_valid sm d.
Proof.
  intros.
  rewrite <- sm_ds_valid_pushd_iff in H.
  intuition.
Qed.

Lemma vs_synced_updN_synced: forall a d i v,
  vs_synced a d ->
  vs_synced a (updN d i (v, nil)).
Proof.
  unfold vs_synced, vssync.
  intros.
  destruct (lt_dec i (length d)).
  destruct (addr_eq_dec i a); subst.
  rewrite selN_updN_eq; auto.
  rewrite selN_updN_ne; auto.
  rewrite updN_oob by omega; auto.
Qed.

Lemma sm_vs_valid_upd_unsynced: forall sm d a v,
  sm_vs_valid sm d ->
  sm_vs_valid (Mem.upd sm a false) (updN d a v).
Proof.
  unfold sm_vs_valid, Mem.upd, vsupd.
  intros.
  rewrite length_updN in *.
  intuition.
  destruct addr_eq_dec; subst.
  congruence.
  eapply H; eauto.
  destruct addr_eq_dec.
  congruence.
  unfold vs_synced.
  rewrite selN_updN_ne; auto.
  eapply H; eauto.
Qed.

Lemma sm_vs_valid_upd_synced: forall sm i d v,
  sm_vs_valid sm d ->
  sm_vs_valid (Mem.upd sm i true) (updN d i (v, nil)).
Proof.
  unfold sm_vs_valid, Mem.upd; cbn.
  intros.
  rewrite length_updN in *.
  intuition.
  destruct addr_eq_dec; subst.
  congruence.
  eapply H; eauto.
  destruct addr_eq_dec; subst.
  unfold vs_synced.
  rewrite selN_updN_eq; auto.
  apply vs_synced_updN_synced.
  eapply H; eauto.
Qed.

Lemma sm_vs_valid_same_upd_synced: forall sm i d v,
  sm_vs_valid sm d ->
  sm_vs_valid sm (updN d i (v, nil)).
Proof.
  unfold sm_vs_valid, Mem.upd; cbn.
  intros.
  rewrite length_updN in *.
  intuition.
  - eapply H; eauto.
  - destruct (addr_eq_dec a i); subst.
    + unfold vs_synced.
      rewrite selN_updN_eq; auto.
    + apply vs_synced_updN_synced.
      eapply H; eauto.
Qed.

Lemma sm_vs_valid_vssync': forall sm vs a,
  sm_vs_valid sm vs -> sm_vs_valid sm (vssync vs a).
Proof.
  unfold sm_vs_valid, vssync; intros.
  rewrite length_updN in *.
  intuition.
  eapply H; eauto.
  eapply H in H1; auto.
  eapply vs_synced_updN_synced.
  auto.
Qed.

Lemma sm_vs_valid_vs_synced: forall sm vs a,
  sm_vs_valid sm vs -> sm a = Some true ->
  vs_synced a vs.
Proof.
  unfold vs_synced, sm_vs_valid.
  intros.
  destruct (lt_dec a (length vs)) as [Hl|Hl].
  apply H in Hl; intuition.
  rewrite selN_oob by omega.
  auto.
Qed.


Lemma sm_ds_valid_dsupd: forall sm ds a v,
  a < length (ds!!) ->
  sm_ds_valid sm ds ->
  sm_ds_valid (Mem.upd sm a false) (dsupd ds a v).
Proof.
  unfold sm_ds_valid.
  intros.
  constructor.
  rewrite dsupd_fst.
  eapply sm_vs_valid_upd_unsynced.
  eapply Forall_inv; eauto.
  unfold dsupd; cbn.
  rewrite <- Forall_map.
  rewrite Forall_forall in *.
  intros.
  cbn in *.
  eapply sm_vs_valid_upd_unsynced; auto.
Qed.

Lemma sm_ds_valid_latest: forall sm ds,
  sm_ds_valid sm ds ->
  sm_vs_valid sm ds!!.
Proof.
  unfold latest, sm_ds_valid; cbn.
  intros.
  inversion H; subst.
  destruct (snd ds) eqn:?; cbn; eauto.
  eapply Forall_inv; eauto.
Qed.

Lemma sm_ds_valid_synced: forall sm d,
  sm_vs_valid sm d ->
  sm_ds_valid sm (d, nil).
Proof.
  unfold sm_ds_valid.
  cbn; intros.
  repeat (constructor; auto).
Qed.

Lemma sm_ds_valid_dssync: forall sm ds a,
  sm_ds_valid sm ds ->
  sm_ds_valid (Mem.upd sm a true) (dssync ds a).
Proof.
  unfold sm_ds_valid.
  intros.
  constructor.
  setoid_rewrite d_map_fst.
  unfold vssync.
  destruct (selN) eqn:?; cbn.
  apply sm_vs_valid_upd_synced.
  eapply Forall_inv; eauto.
  unfold dssync; cbn.
  rewrite <- Forall_map.
  inversion H; subst.
  rewrite Forall_forall in *.
  intros.
  eapply sm_vs_valid_upd_synced; auto.
Qed.

Lemma sm_ds_valid_dssync': forall sm ds a,
  sm_ds_valid sm ds -> sm_ds_valid sm (dssync ds a).
Proof.
  unfold sm_ds_valid; cbn; intros.
  inversion H; subst; constructor.
  eapply sm_vs_valid_vssync'; auto.
  rewrite <- Forall_map.
  rewrite Forall_forall in *.
  intros x; specialize (H x); intuition.
  eapply sm_vs_valid_vssync'; auto.
Qed.

Lemma sm_ds_valid_dssync_vecs': forall sm ds al,
  sm_ds_valid sm ds -> sm_ds_valid sm (dssync_vecs ds al).
Proof.
  induction al; cbn; intros.
  rewrite dssync_vecs_nop by constructor.
  auto.
  rewrite dssync_vecs_cons.
  rewrite dssync_vecs_dssync_comm.
  eapply sm_ds_valid_dssync'; auto.
Qed.

Lemma sm_ds_valid_ds_synced: forall sm ds a,
  sm_ds_valid sm ds -> sm a = Some true ->
  ds_synced a ds.
Proof.
  unfold ds_synced, sm_ds_valid.
  intros.
  rewrite Forall_forall in *.
  intros x; specialize (H x); intuition.
  eapply sm_vs_valid_vs_synced; eauto.
Qed.


Lemma sm_ds_valid_pushd_latest: forall sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid sm (pushd ds!! ds).
Proof.
  intros.
  auto using sm_ds_valid_pushd, sm_ds_valid_latest.
Qed.

Lemma sm_ds_valid_d_in: forall sm ds d,
  sm_ds_valid sm ds ->
  d_in d ds ->
  sm_vs_valid sm d.
Proof.
  unfold d_in, sm_ds_valid.
  intros.
  inversion H; clear H; rewrite Forall_forall in *; subst.
  intuition; subst.
  auto.
Qed.

Lemma sm_ds_valid_nthd: forall n sm ds,
  sm_ds_valid sm ds ->
  sm_vs_valid sm (nthd n ds).
Proof.
  intros.
  eapply sm_ds_valid_d_in; eauto.
  eapply nthd_in_ds.
Qed.

Lemma sm_vs_valid_all_synced: forall sm d d',
  sm_vs_valid sm d ->
  length d = length d' ->
  Forall (fun v => snd v = []) d' ->
  sm_vs_valid sm d'.
Proof.
  unfold sm_vs_valid.
  intros.
  rewrite Forall_forall in *.
  rewrite H0 in *.
  intuition.
  eapply H; eauto.
  unfold vs_synced.
  eauto using in_selN.
Qed.

Definition sm_disk_exact (d : diskstate) :=
  list2nmem (map (fun v => match (snd v) with [] => true | _ => false end) d).

Lemma sm_vs_valid_disk_exact: forall d,
  sm_vs_valid (sm_disk_exact d) d.
Proof.
  unfold sm_vs_valid, sm_disk_exact, list2nmem.
  intros.
  rewrite map_map.
  erewrite selN_map by auto.
  intuition.
  congruence.
  unfold vs_synced.
  inversion H0.
  destruct selN as [? l] eqn:H'.
  rewrite H' in *.
  destruct l; cbn in *; congruence.
Qed.

Definition sm_unsynced : syncedmem := fun _ => Some false.
Definition sm_synced : syncedmem := fun _ => Some true.
Definition sm_sync_all (sm : syncedmem) : syncedmem := fun a =>
  match sm a with
  | None => None
  | Some _ => Some true
  end.

Definition sm_sync_invariant (p : pred) : Prop := forall sm, p sm -> p (sm_sync_all sm).

Lemma sm_vs_valid_sm_unsynced: forall d,
  sm_vs_valid sm_unsynced d.
Proof.
  unfold sm_vs_valid; firstorder. discriminate.
  unfold sm_unsynced in *. congruence.
Qed.
Local Hint Resolve sm_vs_valid_sm_unsynced.

Lemma sm_ds_valid_sm_unsynced: forall ds,
  sm_ds_valid sm_unsynced ds.
Proof.
  unfold sm_ds_valid; intros.
  induction (fst ds :: snd ds); constructor; auto.
Qed.

Definition sm_set_vecs (b : bool) (sm : syncedmem) (a : list addr) :=
  fold_left (fun sm a => @Mem.upd _ _ addr_eq_dec sm a b) a sm.

Definition sm_upd_vecs sm (a : list (_ * valu)) := sm_set_vecs false sm (map fst a).
Definition sm_sync_vecs := sm_set_vecs true.

Lemma sm_set_vecs_cons: forall a sm x b,
  sm_set_vecs b sm (x :: a) = Mem.upd (sm_set_vecs b sm a) x b.
Proof.
  unfold sm_set_vecs.
  induction a; cbn; intros.
  auto.
  rewrite <- IHa.
  cbn.
  destruct (Nat.eq_dec a x).
  congruence.
  rewrite Mem.upd_comm; auto.
Qed.

Lemma sm_set_vecs_cons_inside: forall a sm x b,
  sm_set_vecs b sm (x :: a) = sm_set_vecs b (Mem.upd sm x b) a.
Proof.
  unfold sm_set_vecs.
  induction a; cbn; intros.
  auto.
  rewrite <- IHa.
  cbn.
  destruct (Nat.eq_dec a x).
  congruence.
  rewrite Mem.upd_comm; auto.
Qed.

Lemma sm_upd_vecs_cons: forall a sm x,
  sm_upd_vecs sm (x :: a) = Mem.upd (sm_upd_vecs sm a) (fst x) false.
Proof.
  eauto using sm_set_vecs_cons.
Qed.

Lemma sm_sync_vecs_cons: forall a sm x,
  sm_sync_vecs sm (x :: a) = Mem.upd (sm_sync_vecs sm a) x true.
Proof.
  eauto using sm_set_vecs_cons.
Qed.

Lemma sm_upd_vecs_cons_inside: forall a sm x,
  sm_upd_vecs sm (x :: a) = sm_upd_vecs (Mem.upd sm (fst x) false) a.
Proof.
  eauto using sm_set_vecs_cons_inside.
Qed.

Lemma sm_sync_vecs_cons_inside: forall a sm x,
  sm_sync_vecs sm (x :: a) = sm_sync_vecs (Mem.upd sm x true) a.
Proof.
  eauto using sm_set_vecs_cons_inside.
Qed.

Lemma sm_vs_valid_vsupd_vecs: forall a sm v,
  sm_vs_valid sm v ->
  sm_vs_valid (sm_upd_vecs sm a) (vsupd_vecs v a).
Proof.
  induction a; intros.
  auto.
  destruct a.
  rewrite vsupd_vecs_cons, sm_upd_vecs_cons_inside.
  cbn.
  eapply IHa.
  eapply sm_vs_valid_upd_unsynced.
  auto.
Qed.

Lemma sm_vs_valid_vssync_vecs: forall a sm v,
  sm_vs_valid sm v ->
  sm_vs_valid (sm_sync_vecs sm a) (vssync_vecs v a).
Proof.
  induction a; intros.
  auto.
  rewrite vssync_vecs_cons, sm_sync_vecs_cons_inside.
  eapply IHa.
  eapply sm_vs_valid_upd_synced.
  auto.
Qed.

Lemma sm_vs_valid_ds_valid: forall sm ds,
  Forall (sm_vs_valid sm) (fst ds :: snd ds) ->
  sm_ds_valid sm ds.
Proof.
  intros.
  unfold sm_ds_valid; auto.
Qed.

Lemma sm_ds_valid_dsupd_vecs: forall a sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid (sm_upd_vecs sm a) (dsupd_vecs ds a).
Proof.
  intros.
  apply sm_vs_valid_ds_valid.
  rewrite Forall_forall; intros.
  unfold dsupd_vecs, d_map in *.
  cbn in *.
  intuition subst.
  eapply sm_vs_valid_vsupd_vecs.
  inversion H; auto.
  rewrite in_map_iff in *.
  deex.
  eapply sm_vs_valid_vsupd_vecs.
  inversion H; subst.
  rewrite Forall_forall in *.
  auto.
Qed.

Lemma sm_ds_valid_dssync_vecs: forall a sm ds,
  sm_ds_valid sm ds ->
  sm_ds_valid (sm_sync_vecs sm a) (dssync_vecs ds a).
Proof.
  intros.
  apply sm_vs_valid_ds_valid.
  rewrite Forall_forall; intros.
  unfold dssync_vecs, d_map in *.
  cbn in *.
  intuition subst.
  eapply sm_vs_valid_vssync_vecs.
  inversion H; auto.
  rewrite in_map_iff in *.
  deex.
  eapply sm_vs_valid_vssync_vecs.
  inversion H; subst.
  rewrite Forall_forall in *.
  auto.
Qed.

Lemma sm_sync_all_mem_union: forall AEQ m1 m2,
  @mem_union _ AEQ _ (sm_sync_all m1) (sm_sync_all m2) = sm_sync_all (mem_union m1 m2).
Proof.
  unfold mem_union, sm_sync_all.
  intros.
  apply functional_extensionality.
  intros.
  destruct m1, m2; auto.
Qed.

Lemma sm_sync_all_mem_disjoint: forall m1 m2 AEQ,
  mem_disjoint m1 m2 -> @mem_disjoint _ AEQ _ (sm_sync_all m1) (sm_sync_all m2).
Proof.
  unfold mem_disjoint, sm_sync_all.
  intuition repeat deex.
  destruct m1 eqn:?, m2 eqn:?; try congruence.
  apply H; eauto.
Qed.

Lemma sm_sync_invariant_sep_star: forall (p q : pred),
  sm_sync_invariant p -> sm_sync_invariant q ->
  sm_sync_invariant (p * q).
Proof.
  unfold_sep_star.
  unfold sm_sync_invariant.
  intuition repeat deex.
  repeat eexists.
  rewrite sm_sync_all_mem_union; eauto.
  eauto using sm_sync_all_mem_disjoint.
  all: auto.
Qed.

Lemma sm_sync_all_sep_star_swap: forall AEQ (p p' q q' : @pred _ AEQ _) sm,
  (p * q)%pred sm ->
  (forall m, p m -> p' (sm_sync_all m)) ->
  (forall m, q m -> q' (sm_sync_all m)) ->
  (p' * q')%pred (sm_sync_all sm).
Proof.
  unfold_sep_star.
  intuition repeat deex.
  repeat eexists.
  rewrite sm_sync_all_mem_union.
  reflexivity.
  apply sm_sync_all_mem_disjoint; auto.
  all: auto.
Qed.

Lemma sm_sync_all_sep_star_swap_l: forall (p p' q : pred) sm,
  (p * q)%pred sm ->
  (forall m, p m -> p' (sm_sync_all m)) ->
  sm_sync_invariant q ->
  (p' * q)%pred (sm_sync_all sm).
Proof.
  eauto using sm_sync_all_sep_star_swap.
Qed.

Lemma sm_sync_all_sep_star_swap_r: forall (p q q' : pred) sm,
  (p * q)%pred sm ->
  (forall m, q m -> q' (sm_sync_all m)) ->
  sm_sync_invariant p ->
  (p * q')%pred (sm_sync_all sm).
Proof.
  eauto using sm_sync_all_sep_star_swap.
Qed.

Lemma sm_sync_invariant_lift_empty: forall P,
  sm_sync_invariant (lift_empty P).
Proof.
  unfold sm_sync_invariant, sm_sync_all, lift_empty.
  intuition.
  rewrite H1; auto.
Qed.

Lemma sm_sync_all_ptsto: forall AEQ a b (m : syncedmem),
  (@ptsto _ AEQ _ a b)%pred m ->
  (@ptsto _ AEQ _ a true)%pred (sm_sync_all m).
Proof.
  unfold ptsto, sm_sync_all.
  intuition.
  rewrite H0; auto.
  rewrite H1; auto.
Qed.

Lemma sm_sync_invariant_exis_ptsto: forall a,
  sm_sync_invariant (a |->?)%pred.
Proof.
  unfold sm_sync_invariant, sm_sync_all, ptsto.
  intros.
  destruct H as [x ?].
  intuition.
  exists true.
  destruct sm; try congruence.
  intuition.
  rewrite H1; auto.
Qed.

Lemma sm_sync_invariant_emp:
  sm_sync_invariant emp.
Proof.
  unfold sm_sync_invariant, sm_sync_all, emp.
  intuition.
  rewrite H.
  auto.
Qed.

Lemma sm_sync_invariant_listpred: forall T prd (l : list T),
  (forall x, In x l -> sm_sync_invariant (prd x)) ->
  sm_sync_invariant (listpred prd l).
Proof.
  induction l; cbn; intros.
  apply sm_sync_invariant_emp.
  apply sm_sync_invariant_sep_star; auto.
Qed.

Lemma sm_sync_all_listpred_swap: forall T AEQ (prd prd' : T -> @pred _ AEQ _) (l : list T) sm,
  (forall sm x, In x l -> prd x sm -> prd' x (sm_sync_all sm)) ->
  listpred prd l sm ->
  listpred prd' l (sm_sync_all sm).
Proof.
  induction l; cbn; intros.
  apply sm_sync_invariant_emp; auto.
  eapply sm_sync_all_sep_star_swap; eauto.
Qed.

Lemma sm_sync_all_arrayN_swap: forall T AEQ (prd prd' : nat -> T -> @pred _ AEQ _) d (l : list T) i sm,
  (forall sm  i' x, i' < length l -> selN l i' d = x -> prd (i + i') x sm -> prd' (i + i') x (sm_sync_all sm)) ->
  arrayN prd i l sm ->
  arrayN prd' i l (sm_sync_all sm).
Proof.
  induction l; cbn; intros.
  apply sm_sync_invariant_emp; auto.
  eapply sm_sync_all_sep_star_swap; eauto.
  intros.
  specialize (H m 0).
  rewrite Nat.add_0_r in *.
  apply H; auto.
  omega.
  intros.
  eapply IHl; auto.
  intros.
  rewrite plus_Snm_nSm in *.
  apply H; auto.
  omega.
Qed.

Lemma sm_sync_invariant_piff: forall (p q : pred),
  piff p q -> sm_sync_invariant p <-> sm_sync_invariant q.
Proof.
  unfold sm_sync_invariant.
  intros.
  intuition.
  all : do 3 match goal with H: _ |- _ => apply H end; auto.
Qed.

Hint Resolve sm_sync_invariant_sep_star.
Hint Resolve sm_sync_invariant_exis_ptsto.
Hint Resolve sm_sync_invariant_emp.
Hint Resolve sm_sync_invariant_lift_empty.
Hint Resolve sm_sync_invariant_listpred.

Hint Resolve sm_sync_all_ptsto.

Definition mem_except_mem {AT AEQ V} (m ex : @Mem.mem AT AEQ V) : @Mem.mem AT AEQ V := fun a =>
  match ex a with
  | Some _ => None
  | None => m a
  end.

Lemma mem_except_mem_disjoint: forall AT AEQ V (m ex : @Mem.mem AT AEQ V),
  mem_disjoint (mem_except_mem m ex) ex.
Proof.
  unfold mem_disjoint, mem_except_mem.
  intuition repeat deex.
  destruct ex; congruence.
Qed.

Lemma mem_except_mem_union: forall AT AEQ V (m ex : @Mem.mem AT AEQ V),
  mem_union (mem_except_mem m ex) ex = (mem_union ex m).
Proof.
  intros.
  unfold mem_union, mem_except_mem.
  eapply functional_extensionality.
  intros.
  destruct ex; auto.
  destruct m; auto.
Qed.

Lemma sm_sync_all_mem_union_sm_synced: forall m m1 m2,
  sm_sync_all m = mem_union m1 m2 ->
  mem_disjoint m1 m2 ->
  sm_synced = mem_union m2 sm_synced.
Proof.
  unfold sm_sync_all, mem_union, sm_synced.
  intros.
  eapply functional_extensionality.
  intros a.
  eapply equal_f in H.
  instantiate (1 := a) in H.
  destruct m eqn:?, m1 eqn:?; inversion H; subst.
  destruct m2 eqn:?; auto.
  match goal with Hm: mem_disjoint _ _ |- _ =>
    exfalso; apply Hm end.
  all: eauto.
Qed.

Lemma sm_synced_sep_star_l: forall AEQ (p q : @pred _ AEQ _) m,
  (p * q)%pred (sm_sync_all m) ->
  (any * q)%pred sm_synced.
Proof.
  unfold_sep_star.
  intuition repeat deex.
  repeat eexists.
  3: eassumption.
  2: apply mem_except_mem_disjoint.
  rewrite mem_except_mem_union.
  eapply sm_sync_all_mem_union_sm_synced; eauto.
Qed.

Lemma sm_synced_sep_star_r: forall AEQ (p q : @pred _ AEQ _) m,
  (p * q)%pred (sm_sync_all m) ->
  (p * any)%pred sm_synced.
Proof.
  intros.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eauto using sm_synced_sep_star_l.
Qed.
