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
Require Import DirTreePath.
Require Import TreeSeq.
Require Import DirSep.
Require Import Rounding.
Require Import BACHelper.
Require Import DirTreeDef.
Require Import DirTreeNames.
Require Import DirTreeSafe.
Require Import DirTreeInodes.
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

  Parameter the_dnum : addr.
  Parameter cachesize : nat.
  Axiom cachesize_ok : cachesize <> 0.
  Hint Resolve cachesize_ok.


  Definition temp_fn := ".temp"%string.
  Definition Off0 := 0.
  

  

(* ---------------------------------------------------- *)
 (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.

<<<<<<< Updated upstream
=======
  eapply find_subtree_none_In.
  rewrite <- H0.
  eapply dir2flatmem2_find_subtree_ptsto_none.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  pred_apply; cancel.

  left; eexists; unfold tree_with_tmp; pred_apply; cancel.
  simpl; apply Forall_nil.
  Qed.
  
(*    Lemma treeseq_safe_create: forall pathname' pathname name dnum tree_elem ts ilist' mscs 
    frees'_1 frees'_2 Ftree inum',
    tree_names_distinct (TStree ts !!) ->
    DirTreeInodes.tree_inodes_distinct (TStree ts !!) ->
    (Ftree ✶ (pathname ++ [name])%list |-> Nothing)%pred(dir2flatmem2 (TStree ts !!)) ->
    find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
    (forall inum def',
        (inum = dnum -> False) ->
        In inum (DirTreeInodes.tree_inodes (TStree ts !!)) ->
        In inum
          (DirTreeInodes.tree_inodes
             (tree_graft dnum tree_elem pathname name (TreeFile inum' dirfile0) (TStree ts !!))) ->
        selN (TSilist ts !!) inum def' = selN ilist' inum def')  ->
     DirTreeSafe.dirtree_safe (TSilist ts !!)
          (BFILE.pick_balloc (fst (TSfree ts !!), snd (TSfree ts !!))
             (MSAlloc mscs)) (TStree ts !!) ilist'
          (BFILE.pick_balloc (frees'_1, frees'_2) (MSAlloc mscs))
          (tree_graft dnum tree_elem pathname name (TreeFile inum' dirfile0) (TStree ts !!)) ->
     (~pathname_prefix (pathname ++ [name]) pathname') -> 
     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
     treeseq_pred
        (treeseq_safe pathname' (MSAlloc mscs)
           (pushd
              {|
              TStree := tree_graft dnum tree_elem pathname name (TreeFile inum' dirfile0) (TStree ts !!);
              TSilist := ilist';
              TSfree := (frees'_1, frees'_2) |} ts) !!)
        (pushd
           {|
           TStree := tree_graft dnum tree_elem pathname name (TreeFile inum' dirfile0) (TStree ts !!);
           TSilist := ilist';
           TSfree := (frees'_1, frees'_2) |} ts).
  Proof.
    intros.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H6; eauto.
    eapply treeseq_safe_trans; eauto.
    unfold treeseq_safe; intuition.
    - unfold treeseq_safe_fwd.
      intros; simpl.
      deex.
      exists f; eauto.
      intuition.

      eapply find_subtree_graft_subtree_oob in H9; eauto.

      unfold BFILE.block_belong_to_file in *.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.

      replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
      eapply find_subtree_inum_present; eauto.
      
      unfold tree_graft.
      eapply tree_inodes_in_update_subtree_child; eauto.
      replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
      eapply find_subtree_inum_present; eauto.
      erewrite find_subtree_add_to_dir_oob.
      Search find_subtree app.
      instantiate (1:= []).
      Search find_subtree.
      
      
      
      unfold pathname_prefix, not in *; simpl in *; intros.
      apply H5.
      destruct H8.
    - unfold treeseq_safe_bwd.
      intros.
      left.
      deex.
      eexists f'; intuition; simpl in *.
      eapply find_subtree_prune_subtree_oob' in H9; eauto. 

      unfold BFILE.block_belong_to_file in *.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique with (tree := 
        (update_subtree pathname 
                    (TreeDir dnum 
                     (delete_from_list name tree_elem)) (TStree ts !!))); eauto.

      destruct (TStree ts !!).

      eapply find_subtree_file_dir_exfalso in H2.
      exfalso; eauto.
      eapply tree_inodes_distinct_prune; eauto.
      eapply tree_names_distinct_prune_subtree'; eauto.
      subst.
      erewrite find_update_subtree in H9; eauto.
      congruence.

      apply find_subtree_inum_present in H9; simpl in H9.
      eapply In_incl; eauto.
      eapply incl_appr'.
      eapply incl_count_incl.
      eapply permutation_incl_count.
      eapply tree_inodes_after_prune'; eauto.

      erewrite <- find_subtree_dirlist.
      erewrite <- find_subtree_app with (p0 := pathname); eauto.
      eapply dir2flatmem2_find_subtree_ptsto with (tree := TStree ts !!).
      eauto.
      pred_apply; cancel.

      replace inum with (dirtree_inum (TreeFile inum f')) by reflexivity.
      eapply find_subtree_inum_present; eauto.

    - simpl.
      unfold dirtree_safe in *; intuition.
  Qed. *)
  
  
    Theorem treeseq_create_ok : forall fsxp dnum name mscs,
    {< ds ts pathname Fm Ftop Ftree tree_elem,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
      [[ (Ftree * ((pathname++[name])%list) |-> Nothing )%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] \/
       exists inum, [[ ok = OK inum ]] * exists d ds' ts' tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           ~ pathname_prefix (pathname ++ [name]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs') (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees' mscs') ]]] *
        [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name])%list |-> File inum dirfile0)%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d ds' ts' mscs' tree' ilist' frees' inum,
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           ~ pathname_prefix (pathname ++ [name]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees' mscs') ]]] *
        [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name])%list |-> File inum dirfile0)%pred (dir2flatmem2 (TStree ts' !!)) ]]

    >} AFS.create fsxp dnum name mscs.
Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.create_ok.
    cancel.
    match goal with
    | [H: treeseq_in_ds _ _ _ _ _ _|- _] =>
      eapply treeseq_in_ds_tree_pred_latest in H as Hpred; eauto
    end.
    eassumption.
    step.
    or_r; cancel.

    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    match goal with
    | [H: MSAlloc _ = MSAlloc _,
       H0: dirtree_safe _ _ _ _ _ _ |- _] =>
      rewrite H in H0; eassumption
    end.

    admit.
   (*  - eapply treeseq_safe_pushd; eauto.
    rewrite H.
     eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H8; eauto.
    eapply treeseq_safe_trans; eauto.
    unfold treeseq_safe; intuition.
     + unfold treeseq_safe_fwd.
      intros; simpl.
      deex.
      exists f; eauto.
      intuition.

      eapply find_subtree_graft_subtree_oob in H13; eauto.

      unfold BFILE.block_belong_to_file in *.
      Search dirtree_safe.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.

      replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
      eapply find_subtree_inum_present; eauto.
      
      unfold tree_graft.
      Search tree_inodes In.
      eapply tree_inodes_in_update_subtree_child; eauto.
      Search tree_inodes In add_to_dir.
      replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
      eapply find_subtree_inum_present; eauto.
     
      Search find_subtree add_to_dir.
      erewrite find_subtree_add_to_dir_oob.
      unfold pathname_prefix, not in *; simpl in *; intros.
      apply H5.
      destruct H8.
    
    
    
    
      Search treeseq_safe.
      distinct_names'.
      distinct_inodes'.
      rewrite H in *.
      eauto. *)
    
    eapply dirents2mem2_graft_file_none; eauto.
    match goal with
    | [ H: treeseq_in_ds _ _ _ _ _ _ |- _ ] => 
        edestruct H; unfold tree_rep_latest in *
    end.
    eapply rep_tree_names_distinct; eauto.
    
    xcrash.
    or_r; xcrash.
    
    Search treeseq_in_ds DirTreeRep.rep.
    
    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    match goal with
    | [H: MSAlloc _ = MSAlloc _,
       H0: dirtree_safe _ _ _ _ _ _ |- _] =>
      rewrite H in H0; eassumption
    end.

    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    rewrite <- surjective_pairing in H11.
    rewrite H5 in *; eauto.

    + eapply treeseq_safe_delete; eauto.
      distinct_names'.
      distinct_inodes'.
      rewrite H5 in *; eauto.

    + eapply dir2flatmem2_delete_file; eauto; distinct_names'.

  
  
  
  
  
  
  
  
  
  
>>>>>>> Stashed changes
   
Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, r) <- AFS.create fsxp the_dnum temp_fn mscs;
    match r with
      | Err _ => Ret ^(mscs, false)
      | OK tinum =>
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.

Theorem atomic_cp_ok : forall fsxp srcinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree Ftree' ds ts tmppath tinum srcpath file fy copy_data dstinum dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (BACHelper.tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts ]] *
      [[ tree_with_src Ftree' srcpath tmppath srcinum file dstbase dstname dstinum dstfile
          %pred (dir2flatmem2 (TStree ts!!)) ]] *
      AByteFile.rep file fy *
      [[[ (ByFData fy) ::: (arrayN (ptsto (V:= byteset)) 0 copy_data) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
      ([[r = false ]] *
        ([[ tree_with_src Ftree' srcpath tmppath srcinum
           file dstbase dstname dstinum dstfile 
           %pred (dir2flatmem2 (TStree ts'!!))  ]] \/
         exists tfile, [[ tree_with_tmp Ftree srcpath tmppath srcinum
                       file tinum tfile dstbase dstname dstinum
                       dstfile%pred (dir2flatmem2 (TStree ts!!))]] )
       \/
       ([[r = true ]] *
          exists dfile dfy,
            [[ tree_with_src Ftree' srcpath tmppath srcinum
               file dstbase dstname dstinum dfile 
               %pred (dir2flatmem2 (TStree ts'!!)) ]] *
            AByteFile.rep dfile dfy *
            [[[ (ByFData dfy) ::: (arrayN (ptsto (V:= byteset)) 0 (synced_bdata copy_data)) ]]]))
    XCRASH:hm'
      exists ds' ts',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
       [[ treeseq_pred (BACHelper.tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstinum dstfile) ts']]
    >} atomic_cp fsxp srcinum dstbase dstname mscs.
Proof.
  unfold atomic_cp; step.
  eapply treeseq_in_ds_tree_pred_latest; eauto.
  admit. (* XXX: find TreeDir dstuff *)
  apply rep_sync_invariant; auto.
  
  prestep; norm.
  inversion H4.
  inversion H4.
  unfold stars; cancel.
  intuition; eauto.

  intuition; eauto.
  eapply treeseq_in_ds_pushd.
  eauto.
  instantiate (1:= {| TStree:= (tree_graft the_dnum ?tree_elem ?pathname temp_fn
                                    (TreeFile a0 BFILE.bfile0) (TStree ts !!));
                      TSilist:= ilist';
                      TSfree:= (frees'_1, frees'_2) |}).
  apply H14.
  unfold treeseq_one_safe; simpl.
  rewrite <- H0; apply H15.
  auto.
  
  admit.
  eapply treeseq_pushd_tree_rep; eauto.
  inversion H4.
  eapply tree_rep_tree_graft; eauto.
  admit. (* XXX: Path separation needed*)
  intros.
Admitted.
  
  
  
  
  