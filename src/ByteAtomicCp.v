Require Import Prog ProgMonad.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import String.
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
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import DiskSet.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import VBConv.
Require Import AsyncFS.
Require Import AByteFile.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.
Require Import Rounding.
Require Import BACHelper.
Require Import DirTreeDef.
Require Import DirTreeNames.
Require Import AtomicCp.
Require Import BytefileSpecs.

Import DIRTREE.
Import TREESEQ.
Import ATOMICCP.
Import ListNotations.

Set Implicit Arguments.

Notation tree_rep := ATOMICCP.tree_rep.

Hint Resolve valubytes_ne_O.
Hint Resolve valubytes_ge_O.
  

(* ---------------------------------------------------- *)
 (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.
  
    Lemma treeseq_tree_rep_sync_after_create: forall x0 (F: pred) dummy1 dummy5 srcinum dummy6 dummy4 dstbase
           dstname dummy9 temp_fn x a6 dummy3 a4 a5_1 a5_2,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  TStree dummy3 !! = TreeDir the_dnum x ->
  (F ✶ [temp_fn]%list |-> Nothing)%pred (dir2flatmem2 (TStree dummy3 !!)) ->
  (((((dstbase ++ [dstname])%list |-> File x0 dummy9
          ✶ dummy5 |-> File srcinum dummy6) ✶ [] |-> Dir the_dnum) ✶ dummy1)
       ✶ [temp_fn]%list |-> File a6 dirfile0)%pred
        (dir2flatmem2
           (tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
              (TStree dummy3 !!))) ->
  treeseq_pred
  (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 a6 dstbase dstname
     dummy9)
  ({|
   TStree := tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
               (TStree dummy3 !!);
   TSilist := a4;
   TSfree := (a5_1, a5_2) |}, []).
   Proof.
    intros.
  split; eauto.
  split; simpl.
  unfold tree_graft.
  apply tree_names_distinct_update_subtree.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  simpl.
  apply TND_dir.
  rewrite Forall_forall; intros dt Hx.
  apply in_map_iff in Hx.
  split_hypothesis.
  apply in_add_to_list_tree_or in H4.
  destruct H4.
  rewrite H4 in H3; rewrite <- H3; simpl; apply TND_file.
  
  eapply treeseq_pred_tree_rep_latest in H as Hz; destruct Hz.
  rewrite H0 in H5.
  inversion H5.
  rewrite <- H3.
  rewrite Forall_forall in H9.
  apply H9.
  apply in_map; auto.
  
  apply NoDup_add_to_list.
   eapply treeseq_pred_tree_rep_latest in H as Hz; destruct Hz.
  rewrite H0 in H3.
  inversion H3.
  auto.

  eapply find_subtree_none_In.
  rewrite <- H0.
  eapply dir2flatmem2_find_subtree_ptsto_none.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  pred_apply; cancel.

  split.
  eapply treerep_synced_dirfile; eauto.
  left; eexists; unfold tree_with_tmp; pred_apply; cancel.
  simpl; apply Forall_nil.
  Qed.
  
   
Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, r) <- AFS.create fsxp the_dnum temp_fn mscs;
    match r with
      | Err e => Ret ^(mscs, Err e)
      | OK tinum =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;   (* sync blocks *)
        let^ (mscs, ok) <- BytefileSpecs.copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.

Theorem atomic_cp_ok : forall fsxp srcinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts sm tinum srcpath file fy copy_data dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dstfile
          %pred (dir2flatmem2 (TStree ts!!)) ]] *
      [[ rep file fy ]] *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]] *
      [[ length copy_data > 0 ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       
      ([[ isError r ]] *
        
        (([[ treeseq_in_ds Fm Ftop fsxp sm' mscs ts' ds' ]] * 
        [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum
           file tinum dstbase dstname dstfile) ts' ]] * 
         [[ tree_with_src Ftree srcpath [temp_fn] srcinum
           file dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]) \/
          (exists tinum tfile dfile, [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum
               file tinum dstbase dstname dfile) ts' ]] * 
           [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum
                       file tinum tfile dstbase dstname dfile (dir2flatmem2 (TStree ts'!!))]]))
       \/
       ([[ r = OK tt ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] * 
          exists dfile dfy tinum,
            [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile) ts' ]] *
            [[ tree_with_src Ftree srcpath [temp_fn] srcinum
               file dstbase dstname dfile %pred (dir2flatmem2 (TStree ts'!!)) ]] *
            [[ rep dfile dfy ]] *
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]))
    XCRASH:hm'
       exists mscs' ds' ts' sm' tinum dstfile,
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       ((exists t, [[ ts' = (t, nil) ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']] )
       \/ (exists t ts'' dfile tinum', [[ ts' = pushd t ts'' ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dstfile) ts'' ]] ))
    >} atomic_cp fsxp srcinum dstbase dstname mscs.
Proof.
  unfold atomic_cp; prestep.
  unfold pimpl; intros m' Hx; destruct_lift Hx.
  eapply tree_with_src_the_dnum in H9 as Hy; eauto.
  destruct Hy.
  unfold tree_with_src in H9; destruct H9.
  pred_apply; norm.
  unfold stars; cancel.
  intuition; eauto.
  eapply treeseq_in_ds_tree_pred_latest; eauto.
  instantiate (2:= []); simpl; eauto.
  
  prestep.
  norm.
  inversion H16.
  inversion H16.
  
  unfold stars.
  simpl.
  cancel.
  eexists; eauto.
  intuition; eauto.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (1:= {| TStree:= (tree_graft the_dnum x [] temp_fn 
                                (TreeFile a0 dirfile0) (TStree dummy3 !!));
                      TSilist:= ilist';
                      TSfree:= (frees'_1, frees'_2) |}).
  simpl; auto.
  eauto.
  unfold treeseq_one_safe; simpl.
  rewrite <- H5; eauto.
  eauto.

  prestep.
  norm.
  unfold stars; cancel.
  split.
  split.
  split; auto.
  split; auto.
  split; eauto.
  split.
  2: instantiate (2:= dirfile0).
  split.
  split; eauto.
  intuition; eauto.
  
  unfold latest; simpl.
  split; eauto.
  apply treeseq_safe_refl.
  simpl; apply Forall_nil.
  
  inversion H14; inversion H0. 
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.

  inversion H16.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  pred_apply; cancel.
  
  inversion H14.
  unfold tree_with_tmp; simpl.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eexists.
  apply sep_star_assoc.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  pred_apply; cancel.
  simpl; auto.
  unfold dirfile0; simpl; length_rewrite_l.
  
  step.
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m0 Hx; apply H15 in Hx; pred_apply; xcrash.
  or_l; xcrash; eauto.
  eauto.
  or_r; xcrash; eauto.
  rewrite H25 in H24; eauto.
  pred_apply; cancel; eauto.
  
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m0 Hx; apply H13 in Hx; pred_apply; xcrash.
  or_r; xcrash.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (2:= {| TStree:= (tree_graft the_dnum x [] temp_fn 
                                (TreeFile a0 dirfile0) (TStree dummy3 !!));
                      TSilist:= ilist';
                      TSfree:= (frees'_1, frees'_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl.
  rewrite <- H5; eauto.
  eauto.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  eauto.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H19; auto.
  pred_apply; cancel.
  eauto.
  pred_apply; cancel.

  norm.
  unfold stars; cancel.
  or_l; cancel.
  or_l; cancel; eauto.
  unfold tree_with_src; pred_apply; cancel.
  intuition.
  
  unfold stars.
  simpl.
  cancel.
  eexists; eauto.
  intuition.
  
  eapply H2.
  instantiate (1:= realcrash).
  intros m0 Hx; apply H5 in Hx; pred_apply; xcrash.
  eapply crash_ts_split'; eauto.
  or_r; xcrash; eauto.
  
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest; simpl.
  instantiate (2:= {| TStree:= (tree_graft the_dnum x [] temp_fn 
                                (TreeFile x2 dirfile0) (TStree dummy3 !!));
                    TSilist:= x4;
                    TSfree:= (x5_1, x5_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; eauto.
  rewrite <- H16; auto.
  auto.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  eauto.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H15; auto.
  pred_apply; cancel.
  eauto.
  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.

  
  
  