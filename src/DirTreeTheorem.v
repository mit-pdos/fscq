Require Import DirName.
Require Import Balloc.
Require Import Prog ProgMonad.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import FSLayout.
Require Import Pred.
Require Import Arith.
Require Import GenSepN.
Require Import List ListUtils.
Require Import Hoare.
Require Import Log.
Require Import SepAuto.
Require Import Array.
Require Import FunctionalExtensionality.
Require Import AsyncDisk.
Require Import DiskSet.
Require Import GenSepAuto.
Require Import Lock.
Require Import Errno.
Import ListNotations.

Require Import DirTree.
Import DIRTREE.

Set Implicit Arguments.

Theorem alter_inum_to_alter_path : forall pathname tree subtree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree pathname tree = Some subtree ->
    forall up,
      alter_inum (dirtree_inum subtree) up tree = alter_subtree pathname up tree.
Proof.
  induction pathname; simpl; intros.
  - inversion H1; subst; simpl.
    destruct subtree; simpl; destruct (addr_eq_dec n n); congruence.
  - destruct tree; simpl in *; try congruence.
    destruct (addr_eq_dec (dirtree_inum subtree) n); subst.
    * exfalso.
      induction l; simpl in *; try congruence.
      destruct a0.
      specialize (IHl ltac:(eauto) ltac:(eauto)).
      unfold find_subtree_helper in H1 at 1.
      destruct (string_dec s a); subst; eauto.
      admit.
    * f_equal.
      induction l; simpl in *; try congruence.
      destruct a0; subst; eauto.
    + erewrite IHpathname; eauto.

(*
    induction pathname; simpl; intros.
    - inversion H1; subst; simpl.
      destruct (addr_eq_dec inum inum); congruence.
    - destruct tree; simpl in *; try congruence.
      f_equal.
      induction l; simpl in *; try congruence.
      destruct a0; simpl in *.
      destruct (string_dec s a); subst; eauto.
      + erewrite IHpathname; eauto.
        f_equal.
        inversion H0. inversion H6.
        rewrite update_subtree_notfound by eauto.
        inversion H.
        rewrite dirtree_update_inode_absent'; eauto.
        apply find_subtree_inum_present in H1; simpl in *.
        eapply tree_inodes_distinct_not_in_tail; eauto.
      + rewrite dirtree_update_inode_absent.
        rewrite IHl; eauto.
        eapply tree_inodes_distinct_not_this_child with (pathname := a :: pathname).
        2: apply H1.
        eauto.
 *)
Admitted.