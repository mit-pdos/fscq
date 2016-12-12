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

  Fixpoint remap_tree (flist : list bfile) (t : dirtree) :=
    match t with
    | TreeFile inum f => TreeFile inum (selN flist inum bfile0)
    | TreeDir inum st =>
         let st' := map (fun e => (fst e, remap_tree flist (snd e))) st in
         TreeDir inum st'
    end.

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

  Lemma map_fst_map_eq : forall A B (ents : list (A * B)) C (f : B -> C),
    map fst ents = map fst (map (fun e => (fst e, f (snd e))) ents).
  Proof.
    induction ents; simpl; auto; intros.
    f_equal.
    apply IHents.
  Qed.

  Lemma map_snd_map_eq : forall A B (ents : list (A * B)) C (f : B -> C),
    map snd (map (fun e => (fst e, f (snd e))) ents) = map f (map snd ents).
  Proof.
    induction ents; simpl; auto; intros.
    f_equal.
    apply IHents.
  Qed.

  Lemma Forall_combine_same : forall T T1 T2 (l : list T) P (f1 : T -> T1) (f2 : T -> T2),
    Forall (fun x => P (f1 x, f2 x)) l ->
    Forall P (combine (map f1 l) (map f2 l)).
  Proof.
    induction l; simpl; intros.
    - constructor.
    - inversion H; subst.
      constructor; auto.
  Qed.

  Lemma tree_dir_names_pred_extract :
    forall xp tree_ents s d,
    In (s, d) tree_ents ->
    exists F,
    dirlist_pred (tree_pred xp) tree_ents =p=> F * tree_pred xp d.
  Proof.
    induction tree_ents; simpl; intros.
    - exfalso; auto.
    - destruct a.
      inversion H; subst.
      + eexists; cancel.
      + edestruct IHtree_ents; eauto.
        eexists.
        rewrite H1. cancel.
  Qed.


  Lemma flist_crash_remap_tree_crash : forall xp fs fs' t F,
    (F * tree_pred xp t)%pred (list2nmem fs) ->
    flist_crash fs fs' ->
    tree_crash t (remap_tree fs' t).
  Proof.
    induction t using dirtree_ind2; simpl; intros.
    - constructor.
      destruct_lift H.
      eapply forall2_selN in H0.
      erewrite <- list2nmem_sel with (l := fs) in H0.
      eauto.
      pred_apply; cancel.
      eapply list2nmem_inbound; pred_apply; cancel.
    - constructor; [ apply map_fst_map_eq | ].
      rewrite map_snd_map_eq.
      apply forall_forall2.
      2: repeat rewrite map_length; auto.
      rewrite map_map.
      apply Forall_map in H.
      rewrite Forall_forall in H.
      apply Forall_combine_same.
      apply Forall_forall; intros.
      simpl.
      destruct x; simpl in *.
      edestruct tree_dir_names_pred_extract; eauto.
      specialize (H (s, d) H2); simpl in H.
      eapply H; eauto.
      pred_apply.
      rewrite H3. cancel.

    Grab Existential Variables.
    apply BFILE.bfile0.
  Qed.


  Lemma flist_crash_remap_tree_pred : forall xp fs fs' t F,
    (F * tree_pred xp t)%pred (list2nmem fs) ->
    flist_crash fs fs' ->
    (F * tree_pred xp (remap_tree fs' t))%pred (list2nmem fs').
  Proof.
    induction t using dirtree_ind2; simpl; intros.
    destruct_lift H.
    apply sep_star_assoc.
    apply sep_star_comm.
    apply lift_impl; intros; auto.
    unfold flist_crash in H0.
    unfold file_crash in H0.
  Admitted.


  Local Hint Extern 0 (okToUnify (tree_pred _ _) (tree_pred _ _)) => constructor : okToUnify.

  Lemma xform_tree_rep : forall xp F t ilist frees,
    crash_xform (rep xp F t ilist frees) =p=> exists t',
      [[ tree_crash t t' ]] * rep xp F t' ilist frees.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite xform_rep.
    rewrite IAlloc.xform_rep.
    cancel.
    eapply flist_crash_remap_tree_crash; eauto.
    pred_apply; cancel.
    eapply pimpl_trans. eauto.
    2: eapply flist_crash_remap_tree_pred; eauto.
    cancel.
    pred_apply; cancel.
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

  Theorem file_crash_trans : forall f1 f2 f3,
    file_crash f1 f2 ->
    file_crash f2 f3 ->
    file_crash f1 f3.
  Proof.
    unfold file_crash; intros; repeat deex; simpl in *.
    apply possible_crash_list_synced_list_eq in H1; subst.
    eauto.
  Qed.

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
      eapply IHtree_ents. eauto. 2: eauto. congruence. 2: congruence. 2: eauto.
      constructor; eauto.
      constructor; eauto.
  Qed.

End DTCrash.
