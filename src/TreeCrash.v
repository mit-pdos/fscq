Require Import DirName.
Require Import Balloc.
Require Import Prog.
Require Import BasicProg.
Require Import Bool.
Require Import Word.
Require Import BFile Bytes Rec Inode.
Require Import String.
Require Import FSLayout.
Require Import Pred PredCrash.
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
Require Import DirTree.
Require Import GenSepAuto.
Require Import BFileCrash.
Require Import Omega.
Import ListNotations.

Set Implicit Arguments.

Module DTCrash.

  Import BFILE DIRTREE.


  Inductive tree_crash : dirtree -> dirtree -> Prop :=
    | TCFile : forall inum f f', file_crash f f' ->
               tree_crash (TreeFile inum f) (TreeFile inum f')
    | TCDir  : forall inum st st',
               map fst st = map fst st' ->
               Forall2 tree_crash (map snd st) (map snd st') ->
               tree_crash (TreeDir inum st) (TreeDir inum st').

  Theorem tree_crash_trans : forall t1 t2 t3,
    tree_crash t1 t2 ->
    tree_crash t2 t3 ->
    tree_crash t1 t3.
  Proof.
    induction t1 using dirtree_ind2; simpl; intros.
    inversion H; subst. inversion H0; subst. constructor. eapply file_crash_trans; eauto.
    inversion H0; subst. inversion H1; subst. constructor. congruence.
    generalize dependent st'. generalize dependent st'0.
    induction tree_ents; simpl; intros.
    - destruct st'; simpl in *; try congruence.
    - destruct st'; destruct st'0; simpl in *; try congruence.
      inversion H6. inversion H8. inversion H. inversion H4. inversion H5. subst; simpl in *.
      constructor; eauto.
      eapply IHtree_ents. eauto.
      all: try match goal with | [ |- Forall2 _ _ _ ] => eauto end.
      all: eauto.
      constructor; eauto.
      constructor; eauto.
  Qed.

  Lemma flist_crash_xform_dirlist_pred : forall tree_ents p,
    Forall
      (fun t => flist_crash_xform (p t) =p=> exists t', [[ tree_crash t t' ]] * p t')
      (map snd tree_ents) ->
    flist_crash_xform (dirlist_pred p tree_ents) =p=>
      exists tree_ents',
      [[ Forall2 tree_crash (map snd tree_ents) (map snd tree_ents') ]] *
      [[ map fst tree_ents = map fst tree_ents' ]] *
      dirlist_pred p tree_ents'.
  Proof.
    induction tree_ents; simpl; intros.
    - rewrite flist_crash_xform_emp. cancel.
      eassign (@nil (string * dirtree)); cancel.
      constructor.
      constructor.
    - destruct a. rewrite flist_crash_xform_sep_star.
      inversion H; subst.
      rewrite H2.
      rewrite IHtree_ents by eauto.
      cancel.
      eassign ((s, t') :: tree_ents').
      cancel.
      constructor; eauto.
      simpl; congruence.
  Qed.

  Lemma tree_dir_names_pred'_unchanged : forall tree_ents tree_ents',
    map fst tree_ents = map fst tree_ents' ->
    map (fun e => dirtree_inum e) (map snd tree_ents) = map (fun e => dirtree_inum e) (map snd tree_ents') ->
    map (fun e => dirtree_isdir e) (map snd tree_ents) = map (fun e => dirtree_isdir e) (map snd tree_ents') ->
    tree_dir_names_pred' tree_ents =p=> tree_dir_names_pred' tree_ents'.
  Proof.
    induction tree_ents; intros; destruct tree_ents'; simpl in *; try congruence.
    destruct a; destruct p; simpl in *.
    inversion H; clear H.
    inversion H0; clear H0.
    inversion H1; clear H1.
    subst.
    rewrite IHtree_ents; eauto.
  Qed.

  Lemma flist_crash_xform_tree_dir_names_pred : forall tree_ents tree_ents' xp inum,
    map fst tree_ents = map fst tree_ents' ->
    map (fun e => dirtree_inum e) (map snd tree_ents) = map (fun e => dirtree_inum e) (map snd tree_ents') ->
    map (fun e => dirtree_isdir e) (map snd tree_ents) = map (fun e => dirtree_isdir e) (map snd tree_ents') ->
    flist_crash_xform (tree_dir_names_pred xp inum tree_ents) =p=>
      tree_dir_names_pred xp inum tree_ents'.
  Proof.
    unfold tree_dir_names_pred; intros.
    rewrite flist_crash_xform_exists. norml; unfold stars; simpl; clear_norm_goal.
    rewrite flist_crash_xform_exists. norml; unfold stars; simpl; clear_norm_goal.
    repeat rewrite flist_crash_xform_sep_star.
    repeat rewrite flist_crash_xform_lift_empty.
    rewrite flist_crash_xform_ptsto.
    cancel.
    eapply SDIR.crash_rep; eauto.
    pred_apply.
    apply tree_dir_names_pred'_unchanged; eauto.
  Qed.

  Lemma tree_crash_preserves_dirtree_inum : forall t t',
    tree_crash t t' ->
    dirtree_inum t = dirtree_inum t'.
  Proof.
    inversion 1; auto.
  Qed.

  Lemma tree_crash_preserves_dirtree_isdir : forall t t',
    tree_crash t t' ->
    dirtree_isdir t = dirtree_isdir t'.
  Proof.
    inversion 1; auto.
  Qed.

  Lemma flist_crash_xform_tree_pred : forall xp t,
    flist_crash_xform (tree_pred xp t) =p=> exists t', [[ tree_crash t t' ]] * tree_pred xp t'.
  Proof.
    induction t using dirtree_ind2; simpl; intros.
    - rewrite flist_crash_xform_sep_star.
      rewrite flist_crash_xform_lift_empty.
      rewrite flist_crash_xform_ptsto.
      cancel.
      2: constructor; eauto.
      simpl; cancel.
    - rewrite flist_crash_xform_sep_star.
      rewrite flist_crash_xform_dirlist_pred by eauto.
      cancel.
      eassign (TreeDir inum tree_ents').
      cancel.
      apply flist_crash_xform_tree_dir_names_pred; eauto.
      eapply Forall2_to_map_eq. apply tree_crash_preserves_dirtree_inum. eauto.
      eapply Forall2_to_map_eq. apply tree_crash_preserves_dirtree_isdir. eauto.
      constructor; eauto.
  Qed.

  Lemma flist_crash_xform_freelist : forall xp frees freepred,
    IAlloc.Alloc.rep xp frees freepred =p=>
      IAlloc.Alloc.rep xp frees freepred *
      [[ flist_crash_xform freepred =p=> freepred ]].
  Proof.
    unfold IAlloc.Alloc.rep; intros.
    cancel.
    rewrite H1.
    clear H1 H2 bmap.
    induction frees; simpl.
    rewrite flist_crash_xform_emp; auto.
    rewrite flist_crash_xform_sep_star. rewrite flist_crash_xform_exists. rewrite IHfrees.
    norml; unfold stars; simpl.
    rewrite flist_crash_xform_ptsto. cancel.
  Qed.

  Lemma xform_tree_rep : forall xp F t ilist frees,
    crash_xform (rep xp F t ilist frees) =p=> exists t',
      [[ tree_crash t t' ]] * rep xp (flist_crash_xform F) t' ilist frees.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite xform_rep.
    rewrite IAlloc.xform_rep.
    rewrite flist_crash_xform_freelist.
    norml; unfold stars; simpl; clear_norm_goal.
    eapply flist_crash_flist_crash_xform in H0; eauto.
    apply flist_crash_xform_sep_star in H0. rewrite flist_crash_xform_sep_star in H0.
    rewrite flist_crash_xform_tree_pred in H0.
    destruct_lift H0.
    cancel. eauto.
    cancel. eauto.
  Qed.


  Theorem tree_crash_find_name :
    forall fnlist t t' subtree,
    tree_crash t t' ->
    find_subtree fnlist t = Some subtree ->
    exists subtree',
    find_subtree fnlist t' = Some subtree' /\
    tree_crash subtree subtree'.
  Proof.
    induction fnlist.
    - simpl; intros.
      eexists; intuition eauto.
      inversion H0; subst; auto.
    - intros.
      inversion H0.
      destruct t; try congruence.
      inversion H; subst.
      generalize dependent st'.
      induction l; intros.
      + simpl in *. congruence.
      + destruct st'; try solve [ simpl in *; congruence ].
        destruct p.
        unfold find_subtree_helper in H2 at 1.
        destruct a0.
        simpl in H2.
        destruct (string_dec s0 a).
        * subst.
          edestruct IHfnlist.
          2: apply H2.
          inversion H6; eauto.
          eexists.
          intuition eauto.
          inversion H4; subst.
          simpl; destruct (string_dec s s); try congruence.
        * edestruct IHl.

          eauto.
          eauto.
          all: try solve [ inversion H4; exact H5 ].
          all: try solve [ inversion H6; eauto ].

          constructor. inversion H4; eauto.
          inversion H. inversion H8; eauto.

          exists x. intuition.
          simpl.
          inversion H4; subst. destruct (string_dec s a); try congruence.
          apply H3.
  Qed.

  Lemma tree_crash_root: forall t t' inum,
    tree_crash t t' ->
    find_name [] t = Some (inum, true) ->
    find_name [] t' = Some (inum, true).
  Proof.
    intros.
    destruct t.
    - unfold find_name in H0; subst; simpl.
      unfold find_subtree in H0.
      inversion H0.
    - destruct t'.
      unfold find_name in H0.
      destruct (find_subtree [] (TreeDir n l)).
      destruct d.
      inversion H0.
      inversion H0.
      subst; simpl.
      exfalso.
      inversion H.
      congruence.
      inversion H.
      subst; simpl; eauto.
  Qed.

  Theorem file_crash_exists : forall file, exists file',
    file_crash file file'.
  Proof.
    unfold file_crash; intros.
    eexists.
    exists (map fst (BFData file)).
    intuition.
    split; intros.
    rewrite map_length; eauto.
    unfold vsmerge. constructor.
    erewrite selN_map; eauto.
  Qed.

  Theorem tree_crash_exists : forall tree, exists tree',
    tree_crash tree tree'.
  Proof.
    induction tree using dirtree_ind2; intros.
    edestruct file_crash_exists; eexists; constructor; eauto.
    induction tree_ents.
    eexists; constructor; eauto. constructor.
    destruct a; simpl in *.
    inversion H.
    edestruct IHtree_ents; eauto.
    inversion H4.
    repeat deex.
    exists (TreeDir inum ((s, tree') :: st')).
    constructor. simpl; f_equal; auto.
    constructor; auto.
  Qed.

  Theorem tree_crash_update_subtree :
    forall tree subtree filename updated_tree_crashed,
    tree_crash (update_subtree [filename] subtree tree) updated_tree_crashed ->
    exists tree_crashed subtree_crashed,
    tree_crash tree tree_crashed /\
    tree_crash subtree subtree_crashed /\
    updated_tree_crashed = update_subtree [filename] subtree_crashed tree_crashed.
  Proof.
  Admitted.

End DTCrash.
