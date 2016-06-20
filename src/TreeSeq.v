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
Require Import DirSep.

Print DirSep.

Import DIRTREE.
Import ListNotations.

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

(* XXX if file smaller than off, don't update *)
Definition treeseq_one_upd (t: treeseq_one) pathname off v :=
  match find_subtree pathname (TStree t) with
  | None => t
  | Some (TreeFile inum f) => mk_tree (update_subtree pathname 
                                (TreeFile inum (BFILE.mk_bfile (updN (BFILE.BFData f) off v) (BFILE.BFAttr f))) (TStree t))
                         (TSilist t) (TSfree t)
  | Some (TreeDir inum d) => t
  end.

Definition tsupd (ts: treeseq) pathname off v :=
  d_map (fun t => treeseq_one_upd t pathname off v) ts.

(* XXX to prove this property when creating a new file, we would have to issue a sync,
 * since otherwise inode number reuse can make this false.  a solution may be to add
 * generation numbers to inodes (perhaps just keeping them as ghost state).  with
 * generation numbers, [dirtree_safe] could be more specific in stating that the block
 * should only be belong to inodes with the same generation#.
 *)
Definition no_inode_regrow ilist1 ilist2 inum :=
  forall off bn1 bn2,
    BFILE.block_belong_to_file ilist1 bn1 inum off ->
    BFILE.block_belong_to_file ilist2 bn2 inum off ->
    bn1 = bn2.

(* XXX maybe need a bit more disallow alloc, free, re-alloc of bn in treeseq. *)
Definition treeseq_upd_safe Ftree pathname inum bn off (to : treeseq_one) :=
    BFILE.block_is_unused (fst (TSfree to)) bn \/
    (exists f,
      ((Ftree * pathname |-> (inum, f))%pred  (dir2flatmem [] (TStree to)) /\
       BFILE.block_belong_to_file (TSilist to) bn inum off)).

Theorem treeseq_in_ds_upd : forall  F Ftop Ftree fsxp mscs ts ds mscs' pathname inum bn off v,
  treeseq_in_ds F Ftop fsxp mscs ts ds ->
  treeseq_pred (treeseq_upd_safe Ftree pathname inum off bn) ts ->
  tree_rep F Ftop fsxp (tsupd ts pathname off v) !! (list2nmem (dsupd ds bn v) !!) ->
  BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
  treeseq_in_ds F Ftop fsxp mscs' (tsupd ts pathname off v) (dsupd ds bn v).
Proof.
  intros.
  unfold treeseq_in_ds; simpl; intuition.
  unfold treeseq_pred in H0.
  unfold treeseq_upd_safe in H0.
  unfold tsupd.
  (* maybe using H0 we can prove goal, maybe n *)
Admitted.
