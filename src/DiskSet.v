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
Require Import DiskLog.

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

Definition dsupd_vecs (ds : diskset) av := 
  d_map (fun x => vsupd_vecs x av) ds.

Definition dssync_vecs (ds : diskset) al := 
  d_map (fun x => vssync_vecs x al) ds.

Lemma dsupd_latest : forall ds a v,
  latest (dsupd ds a v) = updN (latest ds) a v.
Proof.
  unfold dsupd; intros.
  rewrite d_map_latest; auto.
Qed.

Lemma dsupd_vecs_latest : forall ds avl,
  latest (dsupd_vecs ds avl) = vsupd_vecs (latest ds) avl.
Proof.
  unfold dsupd_vecs; intros.
  rewrite d_map_latest; auto.
Qed.

Lemma dssync_vecs_latest : forall ds al,
  latest (dssync_vecs ds al) = vssync_vecs (latest ds) al.
Proof.
  unfold dssync_vecs; intros.
  rewrite d_map_latest; auto.
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

End ReplaySeq.


Export NEList.
