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
Require Import NEList.
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


  Lemma flist_crash_remap_tree_crash : forall xp fs fs' t F,
    (F * tree_pred xp t)%pred (list2nmem fs) ->
    flist_crash fs fs' ->
    tree_crash t (remap_tree fs' t).
  Proof.
    induction t using dirtree_ind2; simpl; intros.
    destruct_lift H.
    constructor.
    seprewrite.
    eapply forall2_selN with (n := inum); eauto.

    constructor.
    apply map_fst_map_eq.
    rewrite map_snd_map_eq.

    destruct tree_ents; simpl in *.
    apply Forall2_nil.
    destruct p; simpl in *.
    constructor.
    apply Forall_inv in H.
    eapply H; eauto.
    pred_apply; cancel.

    admit.
  Admitted.


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
  Admitted.


  Local Hint Extern 0 (okToUnify (tree_pred _ _) (tree_pred _ _)) => constructor : okToUnify.

  Lemma xform_tree_rep : forall xp F t,
    crash_xform (rep xp F t) =p=> exists t',
      [[ tree_crash t t' ]] * rep xp F t'.
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
  
End DTCrash.