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
Require Import Arith.
Require Import SepAuto.
Require Import Omega.



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

Definition treeseq_upd_safe pathname off flag (tnewest tolder : treeseq_one) :=
  forall bn inum f,
  find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
  BFILE.block_belong_to_file (TSilist tnewest) bn inum off ->
  (BFILE.block_is_unused (BFILE.pick_balloc (TSfree tolder) flag) bn /\
   ~ exists inum' f',
   find_subtree pathname (TStree tolder) = Some (TreeFile inum' f') /\ off < length (BFILE.BFData f')
   )
  \/
  (exists f',
   find_subtree pathname (TStree tolder) = Some (TreeFile inum f') /\
   BFILE.block_belong_to_file (TSilist tolder) bn inum off).

Lemma Forall2_map2: forall  A (l1 : list A) B l2 T1 T2 (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) (f1 : A -> T1) (f2 : B -> T2),
    (forall a b, In a l1 -> In b l2 -> q a b -> p (f1 a) (f2 b)) ->
    Forall2 q l1 l2 ->
    Forall2 p (map f1 l1) (map f2 l2).
Proof.
  intros.
  induction H0.
  - simpl. eapply Forall2_nil.
  - constructor.
    specialize (H x y).
    eapply H; eauto.
    constructor; auto.
    constructor; auto.
    eapply IHForall2; intros.
    eapply H; eauto.
    eapply in_cons; eauto.
    eapply in_cons; eauto.
Qed.

Theorem NEforall2_d_map : forall T1 T2 A B (p : T1 -> T2 -> Prop) ( q : A -> B -> Prop) l1 (f1 : A -> T1) l2 (f2 : B -> T2),
  (forall a b n, a = nthd n l1 -> b = nthd n l2 -> q a b -> p (f1 a) (f2 b)) ->
  NEforall2 q l1 l2 ->
  NEforall2 p (d_map f1 l1) (d_map f2 l2).
Proof.
(*
  destruct l1; destruct l2; unfold NEforall2; intuition; simpl in *.
  specialize (H a b).
  eapply H; auto.
  constructor; auto.
  constructor; auto.
  eapply Forall2_map2; eauto; intros.
  eapply H; eauto.
  right; eauto.
  right; eauto.
Qed.
*)
Admitted.

Lemma NEforall_d_in : forall T (p : T -> Prop) l x,
  NEforall p l ->
  d_in x l ->
  p x.
Proof.
  unfold NEforall, d_in.
  intuition.
  subst; eauto.
  eapply Forall_forall; eauto.
Qed.

Lemma NEforall2_d_in : forall T1 T2 (p : T1 -> T2 -> Prop) l1 l2 x y n,
  NEforall2 p l1 l2 ->
  x = nthd n l1 ->
  y = nthd n l2 ->
  p x y.
Proof.
Admitted.

Lemma update_subtree_same_2 :
  forall pn tree subtree,
  tree_names_distinct tree ->
  find_subtree pn tree = Some subtree ->
  update_subtree pn subtree tree = tree.
Admitted.

Theorem treeseq_in_ds_upd : forall  F Ftop fsxp mscs ts ds mscs' pathname bn off v inum f,
  find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
  BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
  treeseq_in_ds F Ftop fsxp mscs ts ds ->
  treeseq_pred (treeseq_upd_safe pathname off (BFILE.MSAlloc mscs) (ts !!)) ts ->
  BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
  treeseq_in_ds F Ftop fsxp mscs' (tsupd ts pathname off v) (dsupd ds bn v).
Proof.
  unfold treeseq_in_ds.
  intros.
  simpl; intuition.
  unfold tsupd.
  unfold dsupd.
  eapply NEforall2_d_map; eauto.
  simpl; intros.
  intuition; subst.

  eapply NEforall_d_in in H2 as H2'; [ | apply nthd_in_ds with (n := n) ].
  unfold treeseq_upd_safe in H2'.
  edestruct H2'.
  eauto.
  eauto.

  (* case 1: block is unused and there's no filename at [pathname] that's longer than off *)
  intuition.
  unfold tree_rep in *.
  eapply dirtree_update_free with (v := v) in H7; eauto.
  pred_apply.

  case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
  case_eq d; intros; subst.
  destruct (lt_dec off (length (BFILE.BFData b))).
  exfalso; eauto.

  (* off out of bounds *)
  unfold treeseq_one_upd; rewrite H4; simpl.
  rewrite updN_oob by omega.
  erewrite update_subtree_same_2. cancel.
  eapply rep_tree_names_distinct; eauto.
  destruct b; simpl in *; eauto.

  (* pathname is a directory *)
  unfold treeseq_one_upd; rewrite H4; simpl.
  cancel.

  (* pathname does not exist *)
  unfold treeseq_one_upd; rewrite H4; simpl.
  cancel.

  (* case 2: block does exist, in the right pathname *)
  repeat deex; intuition.
  unfold tree_rep in *.
  eapply dirtree_update_block with (v := v) in H7 as H7'; eauto.
  pred_apply.
  unfold treeseq_one_upd; rewrite H5; simpl.
  erewrite dirtree_update_inode_update_subtree.
  cancel.
  eapply rep_tree_inodes_distinct; eauto.
  eapply rep_tree_names_distinct; eauto.
  eauto.

  Search BFILE.block_belong_to_file length.
  admit.

  (* now, prove treeseq_one_safe.. *)
  rename H1 into H1'.
  eapply NEforall2_d_in in H1' as H1; try eassumption; intuition.
  unfold treeseq_one_safe in *.
  rewrite d_map_latest.

  (* First, prove some intermediate thing that will be useful in all 3 cases below.. *)
  assert (dirtree_safe (TSilist (nthd n ts)) (BFILE.pick_balloc (TSfree (nthd n ts)) (MSAlloc mscs'))
    (TStree (nthd n ts)) (TSilist (treeseq_one_upd ts !! pathname off v))
    (BFILE.pick_balloc (TSfree (treeseq_one_upd ts !! pathname off v)) (MSAlloc mscs'))
    (TStree (treeseq_one_upd ts !! pathname off v))).

  eapply NEforall_d_in in H2; [ | eapply latest_in_ds ].
  unfold treeseq_upd_safe in H2.
  edestruct H2.
  eauto.
  eauto.

  (* block is unused *)
  intuition.
  case_eq (find_subtree pathname (TStree ts !!)).
  intros; case_eq d; intros; subst.
  destruct (lt_dec off (length (BFILE.BFData b))).

  (* cannot be in-range *)
  exfalso; eauto.

  (* out of range *)
  unfold treeseq_one_upd; rewrite H1; simpl.
  rewrite updN_oob by omega.
  rewrite H3.
  rewrite update_subtree_same_2.
  eauto.

  eapply NEforall2_d_in in H1'. intuition.
  unfold tree_rep in *.
  eapply rep_tree_names_distinct; eauto.
  rewrite nthd_oob; auto.
  eauto.
  destruct b; simpl in *; eauto.

  (* it's a directory *)
  unfold treeseq_one_upd; rewrite H1; simpl.
  rewrite H3.
  eauto.

  (* it's not present *)
  intros.
  unfold treeseq_one_upd; rewrite H1; simpl.
  rewrite H3.
  eauto.

  (* block IS USED *)
  repeat deex; intuition.
  unfold treeseq_one_upd; rewrite H6; simpl.
  eapply dirtree_safe_dupdate; eauto.
  rewrite H3.
  eauto.

  (* First, consider whether the left [treeseq_one_upd] had an effect *)
  case_eq (find_subtree pathname (TStree (nthd n ts))).
  intros; case_eq d; intros; subst.
  unfold treeseq_one_upd at 1 2 3; rewrite H6; simpl.
  eapply dirtree_safe_update_subtree; eauto.

  (* Directory *)
  unfold treeseq_one_upd at 1 2 3; rewrite H6; simpl.
  eauto.

  (* Not present *)
  intros; subst.
  unfold treeseq_one_upd at 1 2 3; rewrite H6; simpl.
  eauto.

  Unshelve.
  all: try apply BFILE.bfile0.
Qed.
