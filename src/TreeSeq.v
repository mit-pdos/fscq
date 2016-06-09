Require Import DiskSet.
Require Import DirTree.
Require Import Pred.
Require Import List.
Require Import BFile.
Require Import Inode.
Require Import GenSepN.
Require Import AsyncDisk.
Require Import Array.
Require Import ListUtils.
Require Import DirUtil.

Import DIRTREE.

Record treeseq_one := mk_tree {
  TStree  : DIRTREE.dirtree;
  TSilist : list INODE.inode;
  TSfree  : list addr * list addr
}.

Definition treeseq_one_safe t1 t2 mscs :=
  DIRTREE.dirtree_safe (TSilist t1) (BFILE.pick_balloc (TSfree t1) (BFILE.MSAlloc mscs)) (TStree t1)
                       (TSilist t2) (BFILE.pick_balloc (TSfree t2) (BFILE.MSAlloc mscs)) (TStree t2).

Definition treeseq := nelist treeseq_one.

Definition tree_rep F Ftop fsxp t :=
  (F * DIRTREE.rep fsxp Ftop (TStree t) (TSilist t) (TSfree t))%pred.

Definition treeseq_in_ds F Ftop fsxp mscs (ts : treeseq) (ds : diskset) :=
  tree_rep F Ftop fsxp (latest ts) (list2nmem (latest ds)) /\
  NEforall2
    (fun t d => tree_rep F Ftop fsxp t (list2nmem d) /\
                treeseq_one_safe t (latest ts) mscs)
    ts ds.

Definition treeseq_pred (p : treeseq_one -> Prop) (ts : treeseq) := NEforall p ts.

Theorem treeseq_in_ds_pushd : forall F Ftop fsxp mscs ts ds t mscs' d,
  treeseq_in_ds F Ftop fsxp mscs ts ds ->
  tree_rep F Ftop fsxp t (list2nmem d) ->
  treeseq_one_safe (latest ts) t mscs ->
  BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
  treeseq_in_ds F Ftop fsxp mscs' (pushd t ts) (pushd d ds).
Proof.
  unfold treeseq_in_ds; simpl; intuition.
  apply NEforall2_pushd; intuition.
  rewrite latest_pushd.
  eapply NEforall2_impl; eauto.
  intuition.
  intuition.
  unfold treeseq_one_safe in *; intuition.
  rewrite H2 in *.
  eapply DIRTREE.dirtree_safe_trans; eauto.
  eapply DIRTREE.dirtree_safe_refl.
Qed.

Theorem treeseq_dssync_vecs : forall F Ftop fsxp mscs ts ds al inum,
  treeseq_in_ds F Ftop fsxp mscs ts ds ->
  (forall i, i < length al -> BFILE.block_belong_to_file (TSilist (latest ts)) (selN al i 0) inum i) ->
  exists ts',
  treeseq_in_ds F Ftop fsxp mscs ts' (dssync_vecs ds al) /\
  NEforall2
    (fun t t' => t' = t \/
                 exists pathname' f',
                 find_subtree pathname' (TStree t) = Some (TreeFile inum f') /\
                 t' = mk_tree (update_subtree pathname' (TreeFile inum (BFILE.synced_file f')) (TStree t))
                              (TSilist t) (TSfree t))
    ts ts'.
Proof.
  unfold treeseq_in_ds, tree_rep; intuition.
  edestruct NEforall2_exists.

  edestruct dirtree_update_safe_pathname_vssync_vecs.
Admitted.
