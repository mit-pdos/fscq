Require Import Arith.
Require Import Omega.
Require Import Bool.
Require Import List.
Require Import ListUtils.
Require Import Word.
Require Import Array.
Require Import LogReplay.
Require Import NEList.
Require Import AsyncDisk.
Require Import LogReplay.
Require Import DiskLogHash.
Require Import Pred.
Require Import Morphisms.
Require Import GenSepN.

Import ListNotations.
Import LogReplay.

Set Implicit Arguments.


(**
  diskset, like valuset, represents a non-empty sequence of disk states.
  the fst part is the oldest disk, and the snd part is a list of subsequent disks.
  Unlike valuset, the snd list should be ordered, and a new diskstate is always
  prepended to the head of the list.
    (disk_0, dist_n :: [... ; disk 1] )
*)

Definition diskset  := nelist diskstate.

Definition dsupd (ds : diskset) a v := 
  d_map (fun x => updN x a v) ds.

Definition dssync (ds : diskset) a := 
  d_map (fun x => vssync x a) ds.

Definition dsupd_vecs (ds : diskset) av := 
  d_map (fun x => vsupd_vecs x av) ds.

Definition dssync_vecs (ds : diskset) al := 
  d_map (fun x => vssync_vecs x al) ds.

Definition ds_synced a (ds : diskset) :=
  Forall (vs_synced a) (fst ds :: snd ds).

Lemma dsupd_latest : forall ds a v,
  latest (dsupd ds a v) = updN (latest ds) a v.
Proof.
  unfold dsupd; intros.
  rewrite d_map_latest; auto.
Qed.

Lemma dsupd_fst : forall ds a v,
  fst (dsupd ds a v) = updN (fst ds) a v.
Proof.
  unfold dsupd; intros.
  rewrite d_map_fst; auto.
Qed.

Lemma dsupd_nthd : forall ds a v n,
  nthd n (dsupd ds a v) = updN (nthd n ds) a v.
Proof.
  unfold dsupd; intros.
  rewrite d_map_nthd; auto.
Qed.

Lemma dssync_latest : forall ds a,
  latest (dssync ds a) = vssync (latest ds) a.
Proof.
  unfold dssync; intros.
  rewrite d_map_latest; auto.
Qed.

Lemma dssync_nthd : forall ds a n,
  nthd n (dssync ds a) = vssync (nthd n ds) a.
Proof.
  unfold dssync; intros.
  rewrite d_map_nthd; auto.
Qed.

Lemma dsupd_vecs_latest : forall ds avl,
  latest (dsupd_vecs ds avl) = vsupd_vecs (latest ds) avl.
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_latest; auto.
Qed.

Lemma dsupd_vecs_nthd : forall ds avl n,
  nthd n (dsupd_vecs ds avl) = vsupd_vecs (nthd n ds) avl.
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.

Lemma dsupd_vecs_fst : forall ds avl,
  fst (dsupd_vecs ds avl) = vsupd_vecs (fst ds) avl.
Proof.
  unfold dsupd_vecs; intros.
  simpl; auto.
Qed.

Lemma dssync_vecs_latest : forall ds al,
  latest (dssync_vecs ds al) = vssync_vecs (latest ds) al.
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_latest; auto.
Qed.

Lemma dssync_vecs_nthd : forall ds al n,
  nthd n (dssync_vecs ds al) = vssync_vecs (nthd n ds) al.
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_nthd; auto.
Qed.

Lemma dssync_latest_length : forall ds a,
  length (latest (dssync ds a)) = length (latest ds).
Proof.
  intros; rewrite dssync_latest.
  unfold vssync; rewrite length_updN; auto.
Qed.

Lemma dsupd_latest_length : forall ds a v,
  length (latest (dsupd ds a v)) = length (latest ds).
Proof.
  intros; rewrite dsupd_latest.
  rewrite length_updN; auto.
Qed.

Lemma dsupd_vecs_latest_length : forall ds avl,
  length (latest (dsupd_vecs ds avl)) = length (latest ds).
Proof.
  intros; rewrite dsupd_vecs_latest.
  rewrite vsupd_vecs_length; auto.
Qed.

Lemma dssync_vecs_latest_length : forall ds al,
  length (latest (dssync_vecs ds al)) = length (latest ds).
Proof.
  intros; rewrite dssync_vecs_latest.
  rewrite vssync_vecs_length; auto.
Qed.

Lemma nthd_cons_inb : forall T d0 ds (d : T) n,
  n <= length ds ->
  nthd n (d0, d :: ds) = nthd n (d0, ds).
Proof.
  unfold nthd; intuition; simpl.
  destruct n.
  rewrite Nat.sub_0_r; auto.
  destruct (length ds - n) eqn:?.
  omega.
  replace (length ds - S n) with n0 by omega; auto.
Qed.

Lemma dssync_vecs_nop: forall vs l,
  Forall (fun a => ds_synced a vs) l ->
  dssync_vecs vs l = vs.
Proof.
  unfold dssync_vecs, d_map.
  intros.
  destruct vs; cbn; f_equal.
  eapply vssync_vecs_nop.
  rewrite Forall_forall in *.
  intuition.
  unfold ds_synced in *.
  specialize (H x); intuition.
  inversion H1; auto.
  rewrite <- map_id.
  eapply map_ext_in.
  rewrite Forall_forall in *.
  unfold ds_synced in *.
  intuition; cbn in *.
  eapply vssync_vecs_nop.
  rewrite Forall_forall.
  intros x; specialize (H x); intuition.
  rewrite Forall_forall in *.
  cbn in *; intuition.
Qed.

Lemma dssync_comm: forall d a b,
  dssync (dssync d a) b = dssync (dssync d b) a.
Proof.
  unfold dssync, d_map.
  destruct d; cbn -[vssync]; intros.
  f_equal.
  rewrite vssync_comm.
  auto.
  repeat rewrite map_map.
  eapply map_ext_in; intros.
  rewrite vssync_comm; auto.
Qed.

Lemma dssync_vecs_cons: forall l vs x,
  dssync_vecs vs (x :: l) = dssync_vecs (dssync vs x) l.
Proof.
  unfold dssync_vecs, dssync.
  intros.
  cbn.
  destruct vs; unfold d_map; cbn.
  f_equal.
  rewrite map_map.
  auto.
Qed.

Lemma dssync_vecs_dssync_comm: forall l x vs,
  dssync_vecs (dssync vs x) l = dssync (dssync_vecs vs l) x.
Proof.
  induction l; cbn; intros.
  repeat rewrite dssync_vecs_nop by constructor.
  auto.
  repeat rewrite dssync_vecs_cons.
  rewrite dssync_comm.
  rewrite IHl.
  auto.
Qed.

Lemma dssync_vecs_app: forall vs l l',
  dssync_vecs vs (l ++ l') = dssync_vecs (dssync_vecs vs l) l'.
Proof.
  induction l; cbn.
  rewrite dssync_vecs_nop; auto.
  constructor.
  intros.
  repeat rewrite dssync_vecs_cons.
  repeat rewrite dssync_vecs_dssync_comm.
  congruence.
Qed.

Lemma dssync_vecs_permutation: forall ds l l',
  Permutation.Permutation l l' ->
  dssync_vecs ds l = dssync_vecs ds l'.
Proof.
  intros.
  induction H; cbn; auto.
  repeat rewrite ?dssync_vecs_cons, ?dssync_vecs_dssync_comm.
  f_equal; auto.
  repeat rewrite ?dssync_vecs_cons.
  rewrite dssync_comm.
  reflexivity.
  congruence.
Qed.

Module SyncedMem.

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

  Definition sm_disk_synced (d : diskstate) :=
    list2nmem (repeat true (length d)).

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

  Definition sm_disk_unsynced : syncedmem := fun _ => Some false.

  Lemma sm_vs_valid_disk_unsynced: forall d,
    sm_vs_valid sm_disk_unsynced d.
  Proof.
    unfold sm_vs_valid; firstorder. discriminate.
  Qed.
  Local Hint Resolve sm_vs_valid_disk_unsynced.

  Lemma sm_ds_valid_disk_unsynced: forall ds,
    sm_ds_valid sm_disk_unsynced ds.
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


End SyncedMem.

(* list of transactions *)
Definition txnlist  := list DLog.contents.

Module ReplaySeq.

  (** ReplaySeq: any prefix of a diskset is the result of replaying 
   *  the corresponding prefix of transactions
   *)
  Inductive ReplaySeq : diskset -> txnlist -> Prop :=
    | RSeqNil  : forall d0, ReplaySeq (d0, nil) nil
    | RSeqCons : forall d0 d t ds ts,
          d = replay_disk t (hd d0 ds) ->
          ReplaySeq (d0, ds) ts -> 
          ReplaySeq (d0, (d :: ds)) (t :: ts).

  Lemma replay_seq_length : forall ds ts,
    ReplaySeq ds ts -> length (snd ds) = length ts.
  Proof.
    induction 1; simpl; firstorder.
  Qed.

  Lemma repaly_seq_latest : forall ds ts,
    ReplaySeq ds ts ->
    latest ds = fold_right replay_disk (fst ds) ts.
  Proof.
    induction 1; simpl in *; intros; firstorder.
    rewrite <- IHReplaySeq; firstorder.
  Qed.

  Lemma replay_seq_selN : forall n ds ts,
    ReplaySeq ds ts ->
    n < length (snd ds) ->
    selN (snd ds) n (fst ds) = fold_right replay_disk (fst ds) (skipn n ts).
  Proof.
    induction n; simpl; intros; auto.
    destruct ds.
    apply repaly_seq_latest in H; rewrite <- H.
    destruct l; intuition.
    pose proof (replay_seq_length H).
    inversion H; auto; subst; simpl in *.
    specialize (IHn (d0, ds0)).
    apply IHn; simpl; auto; omega.
  Qed.

  Lemma replay_seq_nthd : forall n ds ts,
    ReplaySeq ds ts ->
    nthd n ds = fold_right replay_disk (fst ds) (skipn (length ts - n) ts).
  Proof.
    unfold nthd; intros.
    destruct n; simpl.
    rewrite selN_oob, skipn_oob by omega; auto.
    erewrite <- replay_seq_length by eauto.
    destruct (lt_dec (length (snd ds)) (S n)).
    replace (length (snd ds) - S n) with 0 by omega; simpl.
    rewrite <- repaly_seq_latest by auto.
    unfold latest; destruct ds; simpl.
    destruct l0; firstorder.
    apply replay_seq_selN; auto; omega.
  Qed.

  Lemma fold_right_replay_disk_length : forall l d,
    length (fold_right replay_disk d l) = length d.
  Proof.
    induction l; simpl; auto; intros.
    rewrite replay_disk_length; auto.
  Qed.

  Lemma replay_seq_latest_length : forall ds ts,
    ReplaySeq ds ts ->
    length (latest ds) = length (fst ds).
  Proof.
    intros.
    erewrite repaly_seq_latest; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.

  Lemma replay_seq_nthd_length : forall ds ts n,
    ReplaySeq ds ts ->
    length (nthd n ds) = length (fst ds).
  Proof.
    intros.
    erewrite replay_seq_nthd; eauto.
    rewrite fold_right_replay_disk_length; auto.
  Qed.

  Lemma replay_seq_dsupd_notin : forall ds ts a v,
    ReplaySeq ds ts ->
    Forall (fun e => ~ In a (map fst e)) ts ->
    ReplaySeq (dsupd ds a v) ts.
  Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dsupd, d_map; simpl.
    constructor.
    rewrite <- replay_disk_updN_comm by auto.
    destruct ds; auto.
    apply IHReplaySeq; auto.
  Qed.

  Local Hint Resolve ents_remove_not_in.
  Lemma replay_seq_dsupd_ents_remove : forall ds ts a v,
    ReplaySeq ds ts ->
    ReplaySeq (dsupd ds a v) (map (ents_remove a) ts).
  Proof.
    induction 1; simpl; subst.
    constructor.
    unfold dsupd, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; simpl;
    rewrite replay_disk_updN_comm by auto;
    rewrite replay_disk_ents_remove_updN; auto.
  Qed.

  Lemma replay_seq_dssync_notin : forall ds ts a,
    ReplaySeq ds ts ->
    ReplaySeq (dssync ds a) ts.
  Proof.
    induction 1; intros.
    constructor.
    unfold dssync, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; subst; simpl;
    rewrite replay_disk_vssync_comm_list; auto.
  Qed.

  Lemma replay_seq_dsupd_vecs_disjoint : forall ds ts avl,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint (map fst avl) (map fst e)) ts ->
    ReplaySeq (dsupd_vecs ds avl) ts.
  Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dsupd_vecs, d_map; simpl.
    constructor; auto.
    rewrite replay_disk_vsupd_vecs_disjoint by auto.
    destruct ds; auto.
  Qed.

  Lemma replay_seq_dssync_vecs_disjoint : forall ds ts al,
    ReplaySeq ds ts ->
    Forall (fun e => disjoint al (map fst e)) ts ->
    ReplaySeq (dssync_vecs ds al) ts.
  Proof.
    induction 1; intros.
    constructor.
    inversion H1; subst.
    unfold dssync_vecs, d_map; simpl.
    constructor; auto.
    rewrite replay_disk_vssync_vecs_disjoint by auto.
    destruct ds; auto.
  Qed.

  Lemma replay_seq_dssync_vecs_ents : forall ds ts al,
    ReplaySeq ds ts ->
    ReplaySeq (dssync_vecs ds al) ts.
  Proof.
    induction 1; simpl; subst.
    constructor.
    unfold dssync_vecs, d_map; simpl.
    constructor.
    2: apply IHReplaySeq; auto.
    destruct ds; simpl;
    rewrite <- replay_disk_vssync_vecs_comm_list; auto.
  Qed.


End ReplaySeq.


Definition diskset_pred  V (p : @pred _ _ V) ds :=
  forall d, d_in d ds -> p (list2nmem d).


Instance diskset_pred_pimpl_eq_impl {V} :
  Proper (pimpl ==> eq ==> Basics.impl) (@diskset_pred V).
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  unfold diskset_pred in *; subst; eauto.
Qed.

Instance diskset_pred_flip_pimpl_eq_flip_impl {V} :
  Proper (Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  unfold diskset_pred in *; subst; eauto.
Qed.


Instance diskset_pred_piff_eq_impl {V} :
  Proper (piff ==> eq ==> Basics.impl) (@diskset_pred V).
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  inversion Hp.
  unfold diskset_pred in *; subst; eauto.
Qed.

Instance diskset_pred_piff_eq_flip_impl {V} :
  Proper (piff ==> eq ==> Basics.flip Basics.impl) (@diskset_pred V).
Proof.
  intros p p' Hp ds ds' Hds Hpd.
  inversion Hp.
  unfold diskset_pred in *; subst; eauto.
Qed.


Lemma diskset_pred_d_map : forall V (p1 p2 : @pred _ _ V) f ds,
  diskset_pred p1 ds ->
  (forall d, p1 (list2nmem d) -> p2 (list2nmem (f d))) ->
  diskset_pred p2 (d_map f ds).
Proof.
  unfold diskset_pred; intros.
  apply d_in_d_map in H1; deex.
  eauto.
Qed.


Export NEList.
