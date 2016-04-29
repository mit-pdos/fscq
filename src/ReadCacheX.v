Require Import Mem.
Require Import List.
Require Import Prog.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ReadCache.

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.

Module RCacheX.

  Definition rep := RCache.rep.
  Definition cache0 := RCache.cache0.

  Definition read T a (cs : cachestate) rx : prog T :=
    r <- RCache.read a cs;
    rx r.

  Definition write T a v (cs : cachestate) rx : prog T :=
    r <- RCache.write a v cs;
    rx r.

  Definition sync T a (cs : cachestate) rx : prog T :=
    r <- RCache.sync a cs;
    rx r.

  Definition init_recover T cs rx : prog T :=
    r <- RCache.init_recover cs;
    rx r.

  Definition init_load T cs rx : prog T :=
    r <- RCache.init_load cs;
    rx r.

  Definition read_array T a i cs rx : prog T :=
    r <- RCache.read_array a i cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    r <- RCache.write_array a i v cs;
    rx r.

  Definition sync_array T a i cs rx : prog T :=
    r <- RCache.sync_array a i cs;
    rx r.

  Definition read_range T A a nr (vfold : A -> valu -> A) a0 cs rx : prog T :=
    r <- RCache.read_range a nr vfold a0 cs;
    rx r.

  Definition write_range T a l cs rx : prog T :=
    r <- RCache.write_range a l cs;
    rx r.

  Definition sync_range T a nr cs rx : prog T :=
    r <- RCache.sync_range a nr cs;
    rx r.

  Definition write_vecs T a l cs rx : prog T :=
    r <- RCache.write_vecs a l cs;
    rx r.

  Definition sync_vecs T a l cs rx : prog T :=
    r <- RCache.sync_vecs a l cs;
    rx r.

  Definition init_load_ok := RCache.init_load_ok.
  Definition init_recover_ok := RCache.init_recover_ok.
  Definition read_ok := RCache.read_ok.
  Definition read_array_ok := RCache.read_array_ok.
  Definition read_range_ok := RCache.read_range_ok.



  Theorem write_ok : forall cs a v,
    {< d (F : rawpred) v0,
    PRE
      rep cs d * [[ (F * a |-> v0)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    XCRASH
      exists d' cs',
      rep cs' d' * [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    >} write a v cs.
  Proof.
    unfold write.
    step.

    xcrash_rewrite.
    rewrite RCache.crash_xform_rep.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.
    eapply ptsto_upd'; eauto.
    eapply possible_crash_ptsto_upd_incl; eauto.
    apply incl_tl; apply incl_refl.
  Qed.

  Theorem sync_ok : forall a cs,
    {< d (F : rawpred) v,
    PRE
      rep cs d * [[ (F * a |-> v)%pred d ]]
    POST RET:cs
      exists d', rep cs d' * [[ (F * a |-> (fst v, nil))%pred d' ]]
    XCRASH
      exists cs' d',
      rep cs' d' * [[ (F * a |-> v)%pred d' ]]
    >} sync a cs.
  Proof.
    unfold sync.
    step.
    xcrash.
  Qed.


  Theorem write_array_ok : forall a i v cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    >} write_array a i v cs.
  Proof.
    unfold write_array.
    step.

    xcrash_rewrite.
    rewrite RCache.crash_xform_rep.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.
    apply arrayN_updN_memupd; eauto.
    eapply possible_crash_ptsto_upd_incl; eauto.
    pred_apply.
    rewrite arrayN_isolate with (i := i); eauto; cancel.
    apply incl_tl; apply incl_refl.
  Qed.


  Theorem sync_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync vs i))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' * [[ (F * arrayN a vs)%pred d' ]]
    >} sync_array a i cs.
  Proof.
    unfold sync_array.
    step.
    xcrash.
  Qed.


  Theorem write_range_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ length l <= length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_range vs l))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a (vsupd_range vs l))%pred d' ]]
    >} write_range a l cs.
  Proof.
    unfold write_range.
    step.

    xcrash_rewrite.
    rewrite RCache.crash_xform_rep.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.

    eapply arrayN_listupd; eauto.
    repeat rewrite vsupd_range_length; auto.
    rewrite firstn_length_l; omega.

    eapply possible_crash_incl_trans; eauto.
    erewrite arrayN_listupd_eq at 1 by eauto.
    apply mem_incl_listupd_same.
    apply vsupd_range_firstn_incl; auto.
  Qed.


  Theorem sync_range_ok : forall a n cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ n <= length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_range vs n))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a vs)%pred d' ]]
    >} sync_range a n cs.
  Proof.
    unfold sync_range; intros.
    step.

    xcrash_rewrite.
    rewrite RCache.crash_xform_rep.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.

    eapply arrayN_listupd; eauto.
    repeat rewrite vssync_range_length; omega.

    eapply possible_crash_incl_trans; eauto.
    erewrite arrayN_listupd_eq at 1 by eauto.
    apply mem_incl_listupd_same.
    apply vssync_range_incl; omega.
  Qed.


  Theorem write_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => fst e < length vs) l ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_vecs vs l))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a (vsupd_vecs vs l))%pred d' ]]
    >} write_vecs a l cs.
  Proof.
    unfold write_vecs.
    step.

    xcrash_rewrite.
    rewrite RCache.crash_xform_rep.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.

    eapply arrayN_listupd; eauto.
    repeat rewrite vsupd_vecs_length; omega.

    eapply possible_crash_incl_trans; eauto.
    erewrite arrayN_listupd_eq at 1 by eauto.
    apply mem_incl_listupd_same.
    apply vsupd_vecs_firstn_incl; auto.
  Qed.


  Theorem sync_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_vecs vs l))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a vs)%pred d' ]]
    >} sync_vecs a l cs.
  Proof.
    unfold sync_vecs.
    step.

    xcrash_rewrite.
    rewrite RCache.crash_xform_rep.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.

    eapply arrayN_listupd; eauto.
    repeat rewrite vssync_vecs_length; auto.

    eapply possible_crash_incl_trans; eauto.
    erewrite arrayN_listupd_eq at 1 by eauto.
    apply mem_incl_listupd_same.
    apply vssync_vecs_incl; auto.
    apply forall_firstn; auto.
  Qed.

  Definition crash_xform_rep := RCache.crash_xform_rep.
  Definition crash_xform_rep_r := RCache.crash_xform_rep_r.
  Definition crash_xform_rep_pred := RCache.crash_xform_rep_pred.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.



  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _) _) => apply write_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_array _ _ _) _) => apply sync_array_ok : prog.

  Hint Extern 1 ({{_}} progseq (read_range _ _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_range _ _ _) _) => apply write_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_range _ _ _) _) => apply sync_range_ok : prog.

  Hint Extern 1 ({{_}} progseq (write_vecs _ _ _) _) => apply write_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_vecs _ _ _) _) => apply sync_vecs_ok : prog.


End RCacheX.


Global Opaque RCacheX.init_load.
Global Opaque RCacheX.init_recover.

Global Opaque RCacheX.read.
Global Opaque RCacheX.write.
Global Opaque RCacheX.sync.

Global Opaque RCacheX.read_array.
Global Opaque RCacheX.write_array.
Global Opaque RCacheX.sync_array.

Global Opaque RCacheX.read_range.
Global Opaque RCacheX.write_range.
Global Opaque RCacheX.sync_range.

Global Opaque RCacheX.write_vecs.
Global Opaque RCacheX.sync_vecs.
