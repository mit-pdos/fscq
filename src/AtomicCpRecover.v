Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import SuperBlock.
Require Import DiskSet.
Require Import AsyncFS.
Require Import String.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreeNames.
Require Import DirTreeSafe.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import DirSepCrash.
Require Import SyncedMem.
Require Import AtomicCp.

Import TREESEQ.
Import DTCrash.
Import ListNotations.
Import ATOMICCP.

Set Implicit Arguments.

Lemma file_crash_trans: forall f1 f2 f3,
  file_crash f1 f2 ->
  file_crash f2 f3 ->
  file_crash f1 f3.
Proof.
  unfold file_crash; intros.
  repeat deex.
  do 2 eexists.
  eapply BFileCrash.file_crash_trans; eauto.
Qed.

Theorem copydata_with_recover_ok : forall fsxp srcinum tinum mscs,
    {X<< ds sm ts Fm Ftop Ftree srcpath file tfile v0 t0 dstbase dstname dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[[ DFData tfile ::: (Off0 |-> t0) ]]]
(*       [[ dirtree_inum (TStree ts!!) = the_dnum ]] *)
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    REC:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs' dstfile',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile') (t, nil) ]]
    >>X} copydata fsxp srcinum tinum mscs >> atomic_cp_recover.
  Proof.
    unfold forall_helper; intros.
    eapply pimpl_ok3; intros.
    eapply corr3_from_corr2_rx.
    apply copydata_ok.
    apply atomic_cp_recover_ok.
    
    cancel; eauto.
    specialize (H2 (a, (a0, b0))); simpl in H2; auto.
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    instantiate (1:= fun hm' => (exists c, F_ * c * 
      [[ crash_xform (F_ * c) =p=> 
        F_ * crash_xform (
        (exists ds' sm' ts' mscs',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
        [[ treeseq_in_ds v2 v3 fsxp sm' mscs' ts' ds' ]] *
        [[ treeseq_pred (tree_rep v4 v5 [temp_fn] srcinum v6 tinum v10 v11 v12) ts']])
        \/
        (exists ds' sm' ts' mscs' dstfile',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
        [[ treeseq_in_ds (crash_xform v2) (BFileCrash.flist_crash_xform v3)
            fsxp sm' mscs' ts' ds' ]] *
        [[ treeseq_pred (tree_rep (flatmem_crash_xform v4) v5 
            [temp_fn] srcinum v6 tinum v10 v11 dstfile') ts' ]] *
        [[ file_crash v12 dstfile' ]]))]])%pred); simpl.

    cancel; eauto.
    rewrite crash_xform_sep_star_dist; rewrite H3.
    cancel; eauto.
    rewrite crash_xform_or_dist; or_l; eauto.
    
    unfold pimpl; intros.
    apply crash_xform_sep_star_dist in H. 
    rewrite crash_xform_lift_empty in H.
    rewrite crash_xform_exists_comm in H; destruct_lift H.
    apply crash_xform_sep_star_dist in H.
    rewrite crash_xform_lift_empty in H.
    destruct_lift H.
    specialize (H13 _ H) as Hx.
    rewrite crash_xform_or_dist in Hx.
    apply sep_star_or_distr in Hx; apply pimpl_or_apply in Hx; destruct Hx.
    
    -
    repeat (rewrite crash_xform_exists_comm in H0; destruct_lift H0).
    repeat (rewrite crash_xform_sep_star_dist in H0;
        rewrite crash_xform_lift_empty in H0;
        destruct_lift H0).
    rewrite LOG.idempred_idem in H0.
    destruct_lift H0.
    rewrite SB.crash_xform_rep in H0.
    
    repeat eexists.
    repeat rewrite <- sep_star_assoc.
    repeat apply sep_star_lift_apply'; intros; eauto.

    specialize (H1 r_).
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel; eauto.
    
    eexists.
    apply sep_star_lift_apply'.
    destruct_lift H14; eauto.
    intros.
    apply crash_xform_sep_star_dist in H15.
    rewrite H3 in H15.
    pred_apply; cancel.
    unfold pimpl; intros m2 Hp; apply H5 in Hp; pred_apply; cancel.
    rewrite crash_xform_or_dist; cancel.
    rewrite crash_xform_or_dist; or_l; xcrash; eauto.
    rewrite crash_xform_or_dist; or_r; xcrash; eauto.
    
    -
    repeat (rewrite crash_xform_exists_comm in H0; destruct_lift H0).
    repeat (rewrite crash_xform_sep_star_dist in H0;
            rewrite crash_xform_lift_empty in H0;
            destruct_lift H0).
    rewrite LOG.idempred_idem in H0.
    destruct_lift H0.
    rewrite SB.crash_xform_rep in H0.
    
    repeat eexists.
    repeat rewrite <- sep_star_assoc.
    repeat apply sep_star_lift_apply'; intros; eauto.

    specialize (H1 r_).
    eapply pimpl_ok2; eauto.
    simpl; cancel; eauto.
    or_l; cancel; eauto.
    or_r; cancel. eauto.
    
    
    
    Focus 3.
    eexists.
    apply sep_star_lift_apply'.
    destruct_lift H14; eauto.
    intros.
    apply crash_xform_sep_star_dist in H15.
    rewrite H3 in H15.
    pred_apply; cancel.
    unfold pimpl; intros m2 Hp; apply H5 in Hp; pred_apply; cancel.
    rewrite crash_xform_or_dist; cancel.
    rewrite crash_xform_or_dist; or_r; xcrash; eauto.
    rewrite crash_xform_or_dist; or_r; xcrash.
    3: eapply file_crash_trans; eauto.
    
    Unfocus.
Admitted.

  Theorem copy_and_rename_with_recover_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {X<< Fm Ftop Ftree ds sm ts srcpath file dstfile tfile v0,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[r = false ]] *
        (exists f',
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])) \/
       ([[r = true ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    REC:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) (t, nil) ]]
    >>X} copy_and_rename fsxp srcinum tinum dstbase dstname mscs >> atomic_cp_recover.
  Proof.
    unfold forall_helper; intros.
    eapply pimpl_ok3; intros.
    eapply corr3_from_corr2_rx.
    apply copy_and_rename_ok.
    apply atomic_cp_recover_ok.
    safecancel.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    eauto.
    step.

    eassign_idempred.
    
  Admitted.