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

  
  Lemma find_subtree_helper_add_to_list_ne: forall tree_elem name s pathname inum f t,
    ~ pathname_prefix [name] (s :: pathname) -> 
    fold_right (find_subtree_helper (find_subtree pathname) s) None
     (add_to_list name t tree_elem) = Some (TreeFile inum f) ->
    fold_right (find_subtree_helper (find_subtree pathname) s) None tree_elem = Some (TreeFile inum f).
  Proof.
    induction tree_elem; simpl; intros.
    * destruct (string_dec name s); subst; simpl in *; auto.
      exfalso; apply H; unfold pathname_prefix; exists pathname; eauto.
    * destruct a.
      destruct (string_dec s0 name); subst; simpl in *; auto.
      ** destruct (string_dec name s); subst; simpl in *; auto.
         exfalso; apply H; unfold pathname_prefix; exists pathname; eauto.
      ** destruct (string_dec s0 s); subst; simpl in *; auto.
         eapply IHtree_elem; eauto.
 Qed.
 
 Lemma pathname_prefix_neq_cons: forall a l l',
 ~ pathname_prefix (a :: l) (a :: l') <->
 ~ pathname_prefix (l) (l').
 Proof.
  split.
  unfold not, pathname_prefix; intros.
  destruct H0.
  apply H; exists x.
  rewrite <- app_comm_cons; rewrite H0; eauto.
  unfold not, pathname_prefix; intros.
  destruct H0.
  apply H; exists x.
  inversion H0; auto.
Qed.

 Lemma pathname_prefix_cons: forall a l l',
 pathname_prefix (a :: l) (a :: l') <->
 pathname_prefix (l) (l').
 Proof.
  split.
  unfold pathname_prefix; intros.
  destruct H.
  inversion H.
  exists x; auto.
  unfold pathname_prefix; intros.
  destruct H.
  exists x; auto.
  rewrite <- app_comm_cons; rewrite H; auto.
Qed.

Definition pathname_prefix_dec p1 p2: {pathname_prefix p1 p2}+{~pathname_prefix p1 p2}.
Proof.
  generalize dependent p1.
  induction p2; destruct p1.
  left.
  apply pathname_prefix_nil.
  right.
  unfold not; intros; destruct H; inversion H.
  left.
  apply pathname_prefix_nil.
  destruct (string_dec a s).
  subst.
  specialize IHp2 with p1.
  destruct IHp2.
  left.
  apply pathname_prefix_cons; auto.
  right.
  apply pathname_prefix_neq_cons; auto.
  right.
  unfold not; intros Hx; destruct Hx.
  inversion H; subst; apply n; auto.
Defined.

Lemma find_subtree_tree_graft_oob: forall pathname' pathname name dnum tree_elem inum'
      ts inum f,
tree_names_distinct (TStree ts!!) ->
~pathname_prefix (pathname ++ [name]) pathname' ->
find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
find_subtree pathname'
  (tree_graft dnum tree_elem pathname name (TreeFile inum' dirfile0)
     (TStree ts !!)) = Some (TreeFile inum f) 
     -> find_subtree pathname' (TStree ts !!) = Some (TreeFile inum f).
 Proof.
  intros.
  destruct (pathname_prefix_dec pathname pathname').
  unfold pathname_prefix in p; deex.
  - unfold tree_graft in *.
    erewrite find_update_subtree_suffix in H2; eauto.
    erewrite find_subtree_add_to_dir_oob' in H2.
    erewrite find_subtree_app; eauto.
    eapply tree_names_distinct_subtree; eauto.
    erewrite pathname_prefix_trim; eauto.
    eauto.
  - unfold tree_graft in *.
    eapply find_subtree_update_subtree_oob'; eauto.
    unfold pathname_prefix in *; auto.
    unfold not; intros.
    apply n.
    destruct H3; eexists; eauto.
Qed.

Lemma find_subtree_helper_add_to_list_ne': forall tree_elem name s suffix t,
s <> name ->
fold_right (find_subtree_helper (find_subtree suffix) s) None
(add_to_list name t tree_elem) =
fold_right (find_subtree_helper (find_subtree suffix) s) None tree_elem.
Proof.
 induction tree_elem; simpl; intros.
  * destruct (string_dec name s); subst; simpl in *; auto.
    exfalso; apply H; eauto.
  * destruct a.
    destruct (string_dec s0 name); subst; simpl in *; auto.
    ** destruct (string_dec name s); subst; simpl in *; auto.
       exfalso; apply H; eauto.
    ** destruct (string_dec s0 s); subst; simpl in *; auto.
Qed.

Lemma find_subtree_add_to_dir_oob'': forall tree_elem pathname name suffix ts inum f dnum t,
~pathname_prefix (pathname ++ [name]) (pathname ++ suffix) ->
find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
find_subtree (pathname ++ suffix) (TStree ts !!) = Some (TreeFile inum f) ->
find_subtree suffix (add_to_dir name t (TreeDir dnum tree_elem)) = Some (TreeFile inum f).
Proof.
  destruct tree_elem; intros; simpl in *.
  - erewrite find_subtree_app in H1.
    2: apply H0.
    destruct suffix; simpl in *; inversion H1.
  
  - destruct p.
    destruct (string_dec s name).
    + subst.
      erewrite find_subtree_app in H1.
      2: apply H0.
      destruct suffix; simpl in *; inversion H1.
      destruct (string_dec name s); auto.
      subst.
      erewrite <- pathname_prefix_trim in H; eauto.
      exfalso; apply H.
      unfold pathname_prefix; exists suffix.
      rewrite cons_app; eauto.
    + simpl.
      erewrite find_subtree_app in H1.
      2: apply H0.
      destruct suffix; simpl in *; inversion H1.
      destruct (string_dec s s0); auto.
      destruct (string_dec s0 name); simpl in *.
      * subst; simpl.
        exfalso; apply H; exists suffix.
        rewrite cons_nil_app; auto.
      * apply find_subtree_helper_add_to_list_ne'; auto.
Qed.

Lemma find_subtree_tree_graft_oob': forall pathname' pathname name dnum tree_elem inum'
      ts inum f,
tree_names_distinct (TStree ts!!) ->
~pathname_prefix (pathname ++ [name]) pathname' ->
find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
find_subtree pathname' (TStree ts !!) = Some (TreeFile inum f) ->
In inum (tree_inodes (tree_graft dnum tree_elem pathname name (TreeFile inum' dirfile0)
  (TStree ts !!))).
 Proof.
  intros.
  destruct (pathname_prefix_dec pathname pathname').
  - unfold pathname_prefix in p; deex.
    eapply tree_inodes_in_update_subtree_child; eauto.
    replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
    eapply find_subtree_inum_present; eauto.
    instantiate (1:= suffix).
    eapply find_subtree_add_to_dir_oob''; eauto.
  - replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
    eapply find_subtree_inum_present; eauto.
    unfold tree_graft in *.
    erewrite find_subtree_update_subtree_oob; eauto.
    unfold not; intros; apply n.
    destruct H3; eexists; eauto.
Qed.
  
   Lemma treeseq_safe_create: forall pathname' pathname name dnum tree_elem ts ilist' mscs 
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
      eapply find_subtree_tree_graft_oob'; eauto. 

    - unfold treeseq_safe_bwd.
      simpl.
      intros.
      destruct H4.
      deex.
      eapply H9 in H10 as Hx; eauto.
      destruct Hx.
      + left.
        eexists f'; intuition; simpl in *.
        eapply find_subtree_tree_graft_oob; eauto.
      + right; auto.
    - simpl.
      destruct H4; auto.
Qed.
  
  
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
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DirTreeRep.rep fsxp Ftop tree' ilist' frees' mscs') ]]] *
        [[ tree' = tree_graft dnum tree_elem pathname name (TreeFile inum dirfile0) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name])%list |-> File inum dirfile0)%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d ds' ts' mscs' tree' ilist' frees' inum,
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
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

    rewrite H in *; eapply treeseq_safe_create; eauto.
    eapply rep_tree_names_distinct; eauto.
    destruct H7; unfold tree_rep_latest in *; eauto.
    eapply rep_tree_inodes_distinct; eauto.
    destruct H7; unfold tree_rep_latest in *; eauto.
    
    admit.

    eapply dirents2mem2_graft_file_none; eauto.
    match goal with
    | [ H: treeseq_in_ds _ _ _ _ _ _ |- _ ] => 
        edestruct H; unfold tree_rep_latest in *
    end.
    eapply rep_tree_names_distinct; eauto.

    xcrash.
    or_r; xcrash.

    eapply dirents2mem2_graft_file_none; eauto.
    match goal with
    | [ H: treeseq_in_ds _ _ _ _ _ _ |- _ ] => 
        edestruct H; unfold tree_rep_latest in *
    end.
    eapply rep_tree_names_distinct; eauto.
Admitted.
  
  
  
  
  
  