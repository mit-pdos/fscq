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

Lemma alter_inum_inode_absent : forall tree inum up,
    ~ In inum (tree_inodes tree) ->
    alter_inum inum up tree = tree.
Proof.
  induction tree using dirtree_ind2; simpl in *; intros; intuition.
  - destruct (addr_eq_dec inum0 inum); congruence.
  - destruct (addr_eq_dec inum0 inum); try congruence.
    f_equal.
    induction tree_ents; simpl; auto.
    destruct a; simpl in *.
    inversion H.
    rewrite H4 by eauto.
    rewrite IHtree_ents; eauto.
Qed.

Lemma alter_inum_inode_absent' : forall (l: list (string * dirtree))  inum up,
    ~ In inum (concat (map (fun e => tree_inodes (snd e)) l)) ->
    map (fun '(name, item) => (name, alter_inum inum up item)) l = l.
Proof.
  induction l; simpl; intros; eauto.
  destruct a; simpl in *.
  rewrite alter_inum_inode_absent; eauto.
  rewrite IHl; eauto.
Qed.

Lemma tree_inodes_distinct_not_this_subtree : forall n s d l pathname inum subtree,
    tree_inodes_distinct (TreeDir n ((s, d) :: l)) ->
    find_subtree pathname (TreeDir n l) = Some subtree ->
    dirtree_inum subtree = inum ->
    ~In inum (tree_inodes d).
Proof.
  intros; subst.
  apply find_subtree_inum_present in H0; simpl in *.
  inversion H; subst.
  intuition; subst; eauto.
  eapply not_In_NoDup_app; [ | eauto | ]; eauto.
Qed.

Theorem alter_inum_to_alter_path' : forall pathname tree subtree,
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
    + exfalso.
      inversion H0; subst.
      induction l; simpl in *; try congruence.
      destruct a0.
      unfold find_subtree_helper in H1 at 1.
      destruct (string_dec s a); subst; eauto.
      apply IHl; eauto.
    + f_equal.
      induction l; simpl in *; try congruence.
      destruct a0; subst; eauto; simpl in *.
      destruct (string_dec s a).
      * erewrite IHpathname by eauto.
        f_equal.
        inversion H; subst.
        inversion H5; subst.
        rewrite update_subtree_notfound by auto.
        rewrite alter_inum_inode_absent'; auto.
        apply find_subtree_inum_present in H1.
        eapply tree_inodes_distinct_not_in_tail; eauto.
      * rewrite IHl; eauto.
        f_equal.
        rewrite alter_inum_inode_absent; auto.
        eapply tree_inodes_distinct_not_this_subtree
        with (pathname := a :: pathname); simpl; eauto.
Qed.

Theorem alter_inum_to_alter_path : forall pathname inum tree subtree,
    tree_names_distinct tree ->
    tree_inodes_distinct tree ->
    find_subtree pathname tree = Some subtree ->
    dirtree_inum subtree = inum ->
    forall up,
      alter_inum inum up tree = alter_subtree pathname up tree.
Proof.
  intros; subst.
  apply alter_inum_to_alter_path'; auto.
Qed.