Require Import Bool.
Require Import Word.
Require Import Balloc.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DirCache.
Require Import DirTreeDef.
Require Import FSLayout.
Require Import GenSepN.
Require Import SepAuto.
Require Import DirTreePred.


Import ListNotations.

Set Implicit Arguments.

  (**
   *
   * The dirtree representation invariant 
   *
   * [F] represents the other parts of the file system above [tree],
   * in cases where [tree] is a subdirectory somewhere in the tree.
   *)

  Definition rep fsxp F tree ilist frees ms sm dm :=
    (exists bflist freeinodes freeinode_pred,
     BFILE.rep fsxp.(FSXPBlockAlloc) sm fsxp.(FSXPInode) bflist ilist frees
        (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) dm *
     IAlloc.rep BFILE.freepred fsxp freeinodes freeinode_pred (IAlloc.Alloc.mk_memstate (BFILE.MSLL ms) (BFILE.MSIAllocC ms)) *
     [[ (F * tree_pred fsxp tree * freeinode_pred)%pred (list2nmem bflist) ]]
    )%pred.

  Theorem rep_length : forall fsxp F tree ilist frees ms sm dm,
    rep fsxp F tree ilist frees ms sm dm =p=>
    (rep fsxp F tree ilist frees ms sm dm *
     [[ length ilist = ((INODE.IRecSig.RALen (FSXPInode fsxp)) * INODE.IRecSig.items_per_val)%nat ]])%pred.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    rewrite BFILE.rep_length_pimpl at 1.
    cancel.
  Qed.

  Theorem dirtree_update_free : forall tree fsxp F F0 ilist freeblocks ms sm dm v bn m flag,
    (F0 * rep fsxp F tree ilist freeblocks ms sm dm)%pred (list2nmem m) ->
    BFILE.block_is_unused (BFILE.pick_balloc freeblocks flag) bn ->
    (F0 * rep fsxp F tree ilist freeblocks ms sm dm)%pred (list2nmem (updN m bn v)).
  Proof.
    intros.
    unfold rep in *.
    destruct_lift H.
    eapply pimpl_apply; [ | eapply BFILE.rep_safe_unused; eauto; pred_apply; cancel ].
    cancel.
  Qed.

  Theorem dirtree_rep_used_block_eq : forall pathname F0 tree fsxp F ilist freeblocks ms dm inum off bn m sm f,
    (F0 * rep fsxp F tree ilist freeblocks ms sm dm)%pred (list2nmem m) ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    selN (DFData f) off valuset0 = selN m bn valuset0.
  Proof.
    intros.

    unfold rep in *.
    destruct_lift H.

    erewrite <- BFILE.rep_used_block_eq with (m := m).
    2:  eassign (IAlloc.rep BFILE.freepred fsxp dummy0 dummy1
               {|
                 IAlloc.Alloc.MSLog := SDIR.MSLL ms;
                 IAlloc.Alloc.MSCache := SDIR.MSIAllocC ms |} * F0)%pred; pred_apply; cancel.
    2: eauto.
    f_equal.
    f_equal.

    rewrite subtree_extract in * by eassumption.
    simpl in *.
    apply eq_sym.
    eapply BFILE.rep_used_block_eq_Some_helper.

    destruct_lifts.
    assert (inum < Datatypes.length dummy) as Hlt by ( eapply list2nmem_inbound; pred_apply; cancel ).

    pose proof (list2nmem_sel_inb dummy BFILE.bfile0 Hlt) as Hx.
    eapply pimpl_trans in H2; [ | apply pimpl_refl | ].
    eapply ptsto_valid in H2.
    rewrite Hx in H2; clear Hx.
    2: cancel.
    inversion H2; clear H2.
    rewrite H4; simpl.
    auto.    
  Qed.

  Lemma tree_pred_ino_goodSize : forall F Fm xp tree m d frees prd allocc,
    (Fm * (IAlloc.rep BFILE.freepred xp frees prd allocc))%pred m ->
    (F * tree_pred xp tree)%pred d ->
    goodSize addrlen (dirtree_inum tree).
  Proof.
    induction tree using dirtree_ind2; simpl; intros.
    destruct_lift H0.
    eapply IAlloc.ino_valid_goodSize; eauto.
    unfold tree_dir_names_pred in H1; destruct_lift H1.
    eapply IAlloc.ino_valid_goodSize; eauto.
  Qed.

  Lemma find_subtree_inum_valid : forall F F' xp m s tree inum f,
    find_subtree s tree = Some (TreeFile inum f)
    -> (F * tree_pred xp tree * F')%pred m
    -> IAlloc.ino_valid xp inum.
  Proof.
    unfold rep; intros.
    destruct_lift H0.
    rewrite subtree_extract in H0 by eauto.
    simpl in H0; destruct_lift H0; auto.
  Qed.

  Theorem rep_domainmem_subset : forall mscs fsxp F tree ilist frees sm dm dm',
    dm c= dm' ->
    rep fsxp F tree ilist frees mscs sm dm =p=> rep fsxp F tree ilist frees mscs sm dm'.
  Proof.
    unfold rep; intros.
    cancel; eauto.
  Qed.

  Hint Resolve rep_domainmem_subset.

  Theorem mscs_same_except_log_rep' : forall mscs1 mscs2 fsxp F tree ilist frees sm dm,
    BFILE.mscs_same_except_log mscs1 mscs2 ->
    rep fsxp F tree ilist frees mscs1 sm dm =p=> rep fsxp F tree ilist frees mscs2 sm dm.
  Proof.
    unfold BFILE.mscs_same_except_log; unfold rep; intros.
    intuition msalloc_eq.
    apply pimpl_refl.
  Qed.

  Theorem mscs_same_except_log_rep : forall mscs1 mscs2 fsxp F tree ilist frees sm dm,
    BFILE.mscs_same_except_log mscs1 mscs2 ->
    rep fsxp F tree ilist frees mscs1 sm dm <=p=> rep fsxp F tree ilist frees mscs2 sm dm.
  Proof.
    split; eapply mscs_same_except_log_rep'; eauto.
    unfold BFILE.mscs_same_except_log in *; intuition eauto.
  Qed.

    Lemma find_subtree_helper_in:
      forall l a x,
        fold_right (find_subtree_helper (fun tree : dirtree => Some tree) a) None l = Some x ->
        exists l1 l2, l = l1 ++ (a, x)::l2.
    Proof.
      induction l; simpl; intros; try congruence.
      unfold find_subtree_helper at 1 in H.
      destruct a.
      destruct (string_dec s a0); cleanup.
      exists nil, l. simpl; auto.
      apply IHl in H; cleanup.
      exists ((s, d) :: x0), x1; eauto.
    Qed.
