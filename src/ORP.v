Require Import Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import PermDirCache.
Require Import PermGenSepN.
Require Import ListPred.
Require Import PermInode.
Require Import List ListUtils.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.
Require Import SuperBlock.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import PermBFile.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeInodes.
Require Import DirTreeSafe.
Require Import DirTreeNames.
Require Import DirTree.
Require Import AsyncFS AsyncFSPost AsyncFSProg.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import AsyncFSDiskSec.

Set Implicit Arguments.
Import DIRTREE.
Import AFS.
Import ListNotations.

Notation MSLL := BFILE.MSLL.
Notation MSAllocC := BFILE.MSAllocC.
Notation MSIAllocC := BFILE.MSIAllocC.
Notation MSICache := BFILE.MSICache.
Notation MSAlloc := BFILE.MSAlloc.
Notation MSDBlocks := BFILE.MSDBlocks.


Lemma LOG_begin_orp:
  forall pr a b d bm hm,
    only_reads_permitted pr (LOG.begin a b) d bm hm.
Proof.
  intros.
  Transparent LOG.begin.
  unfold LOG.begin; simpl; auto.
Qed.

Lemma writeback_orp:
  forall pr a b d bm hm,
    only_reads_permitted pr (writeback a b) d bm hm.
Proof.
  unfold writeback; simpl; intros.
  destruct (MapUtils.AddrMap.Map.find a (CSMap b)); simpl; auto.
  destruct p; simpl; auto.
  destruct b0; simpl; auto.
Qed.

Hint Resolve LOG_begin_orp writeback_orp.

Lemma maybe_evict_orp:
  forall pr a d bm hm,
    only_reads_permitted pr (maybe_evict a) d bm hm.
Proof.
  unfold maybe_evict; simpl; intros.
  destruct (lt_dec (CSCount a) (CSMaxCount a)); simpl; auto.
  destruct (MapUtils.AddrMap.Map.find 0 (CSMap a)); simpl; auto.
  intuition; simpl.
  destruct (MapUtils.AddrMap.Map.find 0 (CSMap r)); simpl; auto.
  destruct (MapUtils.AddrMap.Map.elements (CSMap a)); simpl; auto.
  destruct p; simpl; auto.
  intuition.
  destruct (MapUtils.AddrMap.Map.find k (CSMap r)); simpl; auto.
Qed.

Hint Resolve maybe_evict_orp.



Lemma PermCacheDef_read_orp:
  forall Fr pr a cs dx d bm hm v,
    (Fr * [[ sync_invariant Fr ]] * PermCacheDef.rep cs dx bm)%pred d ->
    can_access pr (fst (fst v)) ->
    dx a = Some v ->
    only_reads_permitted pr (PermCacheDef.read a cs) d bm hm.
Proof.
  intros; unfold PermCacheDef.read; simpl.
  destruct (MapUtils.AddrMap.Map.find a (CSMap cs)) eqn:D; simpl; auto.
  destruct p; simpl; auto.
  intuition; simpl.   
  pose proof (maybe_evict_post H H2) as Hspec.
  destruct_lift Hspec.
  specialize H8 with (1:=D).
  unfold PermCacheDef.rep in *.
  rewrite mem_pred_extract in H4; eauto.
  unfold cachepred at 2 in H4.
  rewrite H8 in H4.
  repeat rewrite sep_star_assoc in H4.
  apply sep_star_assoc in H4.
  apply sep_star_assoc in H4.
  apply sep_star_assoc in H4.
  eapply ptsto_subset_valid' in H4.
  simpl in *; cleanup; eauto.
Qed.



Lemma MLog_read_orp:
  forall vs F pr d bm hm Fr a ms na xp ds,
    (Fr * [[ sync_invariant Fr ]] *
     exists raw, PermCacheDef.rep (snd ms) raw bm *
     [[ (F * MLog.rep xp (MLog.Synced na ds) (fst ms) bm hm)%pred raw ]] *
     [[[ ds ::: exists F', (F' * a |-> vs) ]]])%pred d ->
    can_access pr (fst (fst vs)) ->
    only_reads_permitted pr (MLog.read xp a ms) d bm hm.
Proof.
  intros; unfold MLog.read.
  destruct (MapUtils.AddrMap.Map.find a (MLog.MSInLog ms)) eqn:D; simpl; auto.
  intuition.
  destruct_lift H.
  denote MLog.rep as Hx; unfold MLog.rep, MLog.synced_rep in Hx.
  destruct_lift Hx.
  unfold LogReplay.map_replay in *.
  eapply map_find_In_elements_none in D.
  cleanup.
  eapply LogReplay.replay_disk_none_selN in D.
  2: pred_apply' H5; cancel.
  apply sep_star_comm in H1.
  apply sep_star_assoc in H1.
  eapply arrayN_selN_subset in H1.
  cleanup.
  eapply PermCacheDef_read_orp; eauto.
  pred_apply; cancel.
  setoid_rewrite H3.
  rewrite minus_plus.
  rewrite D; simpl; auto.
  omega.
  apply list2nmem_inbound in H5.
  rewrite LogReplay.replay_disk_length in H5.
  omega.
  Unshelve.
  exact valuset0.
Qed.

Lemma GLog_read_orp:
    forall vs F pr d bm hm Fr a ms xp ds,
    (Fr * [[ sync_invariant Fr ]] *
     exists raw, PermCacheDef.rep (snd ms) raw bm *
     [[ (F * GLog.rep xp (GLog.Cached ds) (fst ms) bm hm)%pred raw ]] *
     [[[ ds!! ::: exists F', (F' * a |-> vs) ]]])%pred d ->
    can_access pr (fst (fst vs)) ->
    only_reads_permitted pr (GLog.read xp a ms) d bm hm.
  Proof.
    intros; unfold GLog.read.
    destruct (MapUtils.AddrMap.Map.find a (GLog.MSVMap (fst ms))) eqn:D.
    simpl; auto.
    simpl; intuition.
    denote GLog.rep as Hx.
    unfold GLog.rep in Hx; destruct_lift Hx.
    eapply list2nmem_inbound in H5 as Hlen.
    erewrite <- GLog.latest_effective in H5; eauto.
    eapply GLog.diskset_vmap_find_none in D as Hx; eauto.
    erewrite GLog.dset_match_nthd_effective_fst in H2; eauto.
    eapply MLog_read_orp; eauto.
    pred_apply; cancel.
    eexists.
    apply list2nmem_array_pick.
    eapply GLog.diskset_ptsto_bound_effective; eauto.
    erewrite <- GLog.latest_effective; eauto.
    setoid_rewrite Hx; simpl; auto.
  Qed.


Lemma LOG_read_orp:
  forall pr d bm hm lxp a Fr ds sm ms Ftop vs,
    (Fr * [[ sync_invariant Fr ]] *
     LOG.rep lxp Ftop (LOG.ActiveTxn ds ds !!) ms sm bm hm *
     [[[ ds!! ::: exists F', (F' * a |-> vs) ]]])%pred d ->
    can_access pr (fst (fst vs)) ->
    only_reads_permitted pr (LOG.read lxp a ms) d bm hm.
Proof.
  intros; unfold LOG.read.
  destruct (MapUtils.AddrMap.Map.find a (LOG.MSTxn (fst ms))) eqn:D.
  simpl; auto.
  simpl; auto; intuition.
  denote LOG.rep as Hx.
  unfold LOG.rep, LOG.rep_inner in Hx. destruct_lift Hx.
  eapply GLog_read_orp; eauto.
  pred_apply; cancel.
  simpl; auto.
Qed.

