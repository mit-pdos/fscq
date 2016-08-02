Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DiskSet.
Require Import DirTree.
Require Import Pred.
Require Import String.
Require Import List.
Require Import BFile.
Require Import Inode.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import AsyncDisk.
Require Import Array.
Require Import ListUtils.
Require Import DirTree.
Require Import DirSep.
Require Import Arith.
Require Import SepAuto.
Require Import Omega.
Require Import SuperBlock.
Require Import FSLayout.
Require Import AsyncFS.
Require Import Arith.
Require Import Errno.
Require Import List ListUtils.
Require Import GenSepAuto.



Import DIRTREE.
Import ListNotations.


Module TREESEQ.

  (* a layer over AFS that provides the same functions but with treeseq and dirsep specs *)

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Record treeseq_one := mk_tree {
    TStree  : DIRTREE.dirtree;
    TSilist : list INODE.inode;
    TSfree  : list addr * list addr
  }.

  Definition treeseq_one_safe t1 t2 mscs :=
    DIRTREE.dirtree_safe (TSilist t1) (BFILE.pick_balloc (TSfree t1) (MSAlloc mscs)) (TStree t1)
                         (TSilist t2) (BFILE.pick_balloc (TSfree t2) (MSAlloc mscs)) (TStree t2).

  Definition treeseq := nelist treeseq_one.

  Definition tree_rep F Ftop fsxp t :=
    (F * DIRTREE.rep fsxp Ftop (TStree t) (TSilist t) (TSfree t))%pred.

  Definition treeseq_in_ds F Ftop fsxp mscs (ts : treeseq) (ds : diskset) :=
    NEforall2
      (fun t d => tree_rep F Ftop fsxp t (list2nmem d) /\
                  treeseq_one_safe t (latest ts) mscs)
      ts ds.

  Definition treeseq_pred (p : treeseq_one -> Prop) (ts : treeseq) := NEforall p ts.

  Lemma treeseq_in_ds_eq: forall Fm Ftop fsxp mscs a ts ds,
    MSAlloc a = MSAlloc mscs ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds <->
    treeseq_in_ds Fm Ftop fsxp a ts ds.
  Proof.
    intros.
    unfold treeseq_in_ds in *.
    unfold treeseq_one_safe in *.
    rewrite H.
    split.
    intro.
    apply H0.
    intro.
    apply H0.
  Qed.

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

  Lemma tsupd_latest: forall (ts: treeseq) pathname off v,
    (tsupd ts pathname off v) !! = treeseq_one_upd (ts !!) pathname off v.
  Proof.
    intros.
    unfold tsupd.
    rewrite d_map_latest; eauto.
  Qed.

  (**
   * [treeseq_safe] is defined with respect to a specific pathname.  What it means for
   * [treeseq_safe] to hold for a pathname is that, in all previous trees, that pathname
   * must refer to a file that has all the same blocks as the current file (modulo being
   * shorter), or that pathname does not exist.  If, in some previous tree, the file does
   * not exist or is shorter, then the "leftover" blocks must be unused.
   *
   * The reason why [treeseq_safe] is defined per pathname is that we imagine that some
   * application may want to violate these rules for other pathnames.  For example, other
   * files might shrink and re-grow over time, without calling [tree_sync] before re-growing.
   * Or, the application might rename a file and continue writing to it using [update_fblock_d],
   * which (below) will be not supported unless the caller can prove [treeseq_safe] for the
   * current pathname of the file being modified.  The other behavior prohibited by [treeseq_safe]
   * is re-using a pathname without [tree_sync].
   *
   * The per-pathname aspect of [treeseq_safe] might also come in handy for concurrency,
   * where one thread does not know if other threads have already issued their [tree_sync]
   * or not for other pathnames.
   *)

  (**
   * [treeseq_safe] is defined as an if-and-only-if implication.  This captures two
   * important properties.  First, the file is monotonically growing: if the file existed
   * and some block belonged to it in the past, then the file must continue to exist and
   * the block must continue to belong to the file at the same offset.  The forward
   * implication captures this.  Second, we also need to know that all blocks used by
   * the current file were never used by other files.  The reverse implication captures
   * this part (the currently-used blocks were either free or used for the same file at
   * the same pathname).
   *)

 Definition treeseq_safe_fwd pathname (tnewest tolder : treeseq_one) :=
    forall inum off bn,
    (exists f, find_subtree pathname (TStree tolder) = Some (TreeFile inum f) /\
      BFILE.block_belong_to_file (TSilist tolder) bn inum off)
   ->
    (exists f', find_subtree pathname (TStree tnewest) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tnewest) bn inum off).

 Definition treeseq_safe_bwd pathname flag (tnewest tolder : treeseq_one) :=
    forall inum off bn,
    (exists f', find_subtree pathname (TStree tnewest) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tnewest) bn inum off) ->
    ((exists f, find_subtree pathname (TStree tolder) = Some (TreeFile inum f) /\
      BFILE.block_belong_to_file (TSilist tolder) bn inum off) \/
     BFILE.block_is_unused (BFILE.pick_balloc (TSfree tolder) flag) bn).

  Definition treeseq_safe pathname flag (tnewest tolder : treeseq_one) :=
    treeseq_safe_fwd pathname tnewest tolder /\ treeseq_safe_bwd pathname flag tnewest tolder.


  Lemma tree_file_flist: forall F Ftop flist  tree pathname inum f,
    find_subtree pathname tree = Some (TreeFile inum f) ->
    (F * tree_pred Ftop tree)%pred (list2nmem flist) ->
    selN flist inum BFILE.bfile0 = f.
  Proof.
    intros.
    rewrite subtree_extract in H0; eauto.
    unfold tree_pred in H0.
    setoid_rewrite sep_star_comm at 2 in H0.
    setoid_rewrite sep_star_assoc_2 in H0.
    eapply sep_star_assoc_2 in H0.
    eapply list2nmem_sel in H0; eauto.
  Qed.

  (* XXX maybe we can use [block_belong_to_file_bfdata_length] combined with [tree_file_flist] *)
  Lemma tree_file_length_ok: forall F Ftop fsxp ilist frees d tree pathname off bn inum f,
      (F * rep Ftop fsxp tree ilist frees)%pred d ->
      find_subtree pathname tree = Some (TreeFile inum f) ->
      BFILE.block_belong_to_file ilist bn inum off ->
      off < Datatypes.length (BFILE.BFData f).
  Proof.
    intros.
    apply BFILE.block_belong_to_file_inum_ok in H1 as H1'.

    unfold rep in H.
    unfold BFILE.rep in H.
    destruct_lift H.

    eapply sep_star_assoc_1 in H3.
    setoid_rewrite sep_star_comm in H3.
    eapply sep_star_assoc_2 in H3.
    eapply tree_file_flist with (pathname := pathname) in H3 as H3'.

    erewrite listmatch_extract with (i := inum) in H.
    unfold BFILE.file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFILE.BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    rewrite H3' in H14.
    rewrite H14; eauto.
    unfold BFILE.block_belong_to_file in H1.
    intuition.
    eassumption.

    rewrite listmatch_length_pimpl in H.
    destruct_lift H.
    rewrite H11. eauto.
    eassumption.
  Qed.

(*
  Lemma tree_rep_nth_upd: forall F Ftop fsxp mscs ts ds n pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp mscs ts ds ->
    tree_rep F Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs) ts !!) ts ->
    tree_rep F Ftop fsxp (treeseq_one_upd (nthd n ts) pathname off v) (list2nmem (nthd n ds) ⟦ bn := v ⟧).
  Proof.
    intros.
    eapply NEforall_d_in in H3 as H3'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_upd_safe in H3'.
    edestruct H3'.
    eauto.
    eauto.

    (* case 1: block is unused and there's no filename at [pathname] that's longer than off *)
    intuition.
    unfold tree_rep in *.
    eapply dirtree_update_free with (v := v) in H2; eauto.
    pred_apply.

    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    rewrite H4 in H6.
    case_eq d; intros; subst.
    (* a file and off is out of bound *)
    intuition.
    unfold treeseq_one_upd; rewrite H4; simpl.
    rewrite updN_oob by omega.
    erewrite update_subtree_same. cancel.
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
    eapply dirtree_update_block with (v := v) in H2 as H2'; eauto.
    pred_apply.
    unfold treeseq_one_upd; rewrite H5; simpl.
    erewrite dirtree_update_inode_update_subtree.
    cancel.
    eapply rep_tree_inodes_distinct; eauto.
    eapply rep_tree_names_distinct; eauto.
    eauto.
    eapply tree_file_length_ok in H2; eauto.
    Unshelve.
    exact [].
  Qed.

  Lemma tree_safe_upd: forall F Ftop fsxp mscs ts ds mscs' pathname bn off v inum f n,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp mscs ts ds ->
    treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs) ts !!) ts ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_upd (nthd n ts) pathname off v) 
     (d_map (fun t : treeseq_one => treeseq_one_upd t pathname off v) ts) !! mscs'.
  Proof.
    intros.
    unfold treeseq_in_ds in H1.

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

    rewrite H1 in H7.
    intuition.

     (* out of range *)
    unfold treeseq_one_upd; rewrite H1; simpl.
    rewrite updN_oob by omega.
    rewrite H3.
    rewrite update_subtree_same.
    eauto.

    eapply NEforall2_d_in in H1'. intuition.
    unfold tree_rep in *.
    eapply rep_tree_names_distinct; eauto.
    rewrite nthd_oob; auto.
    eauto.
    destruct b; simpl in *; eauto.

    (* it's a directory *)
    rewrite H1 in H7; exfalso; auto.
 
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
    exact [].
  Qed.
*)

(*
  Theorem treeseq_in_ds_upd : forall F Ftop fsxp mscs ts ds mscs' pathname bn off v inum f,
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

    eapply tree_rep_nth_upd; eauto.
    eapply tree_safe_upd; eauto.
   Qed.
*)

  Lemma treeseq_in_ds_tree_pred_latest: forall Fm Ftop fsxp mscs ts ds,
   treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
   (Fm ✶ rep fsxp Ftop (TStree ts !!) (TSilist ts!!) (TSfree ts!!))%pred (list2nmem ds !!).
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    intuition.
    unfold tree_rep in H.
    eapply NEforall2_d_in with (x := ts !!) in H as H'.
    intuition.
    eassumption.
    instantiate (1 := (Datatypes.length (snd ts))).
    rewrite latest_nthd; auto.
    eapply NEforall2_length in H as Hl.
    rewrite Hl.
    rewrite latest_nthd; auto.
  Qed.

  Ltac distinct_names :=
    match goal with
      [ H: (_ * DIRTREE.rep _ _ ?tree _ _)%pred (list2nmem _) |- DIRTREE.tree_names_distinct ?tree ] => 
        eapply DIRTREE.rep_tree_names_distinct; eapply H
    end.

  Ltac distinct_inodes :=
    match goal with
      [ H: (_ * DIRTREE.rep _ _ ?tree _ _)%pred (list2nmem _) |- DIRTREE.tree_inodes_distinct ?tree ] => 
        eapply DIRTREE.rep_tree_inodes_distinct; eapply H
    end.

  Ltac distinct_names' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ ?ts _ |- DIRTREE.tree_names_distinct (TStree ?ts !!) ] => 
        idtac "treeseq"; eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        eapply DIRTREE.rep_tree_names_distinct; eapply Hpred
    end.

  Lemma treeseq_safe_eq: forall pathname flag tree,
   treeseq_safe pathname flag tree tree.
  Proof.
    intros.
    unfold treeseq_safe, treeseq_safe_fwd, treeseq_safe_bwd.
    split.
    intros.
    destruct H.
    eexists x; eauto.
    intros.
    destruct H.
    left.
    eexists x; eauto.
  Qed.

  Lemma treeseq_safe_pushd: forall ts pathname flag tree',
    treeseq_pred (treeseq_safe pathname flag tree') ts ->
    treeseq_pred (treeseq_safe pathname flag tree') (pushd tree' ts).
  Proof.
    intros.
    eapply NEforall_d_in'; intros.
    eapply d_in_pushd in H0.
    intuition.
    rewrite H1.
    eapply treeseq_safe_eq.
    eapply NEforall_d_in; eauto. 
  Qed.

(*
  Lemma treeseq_upd_safe_truncate': forall ts pathname off flag inum file ilist' frees',
    let file' := {|
               BFILE.BFData := setlen (BFILE.BFData file) 1 ($ (0), []);
               BFILE.BFAttr := BFILE.BFAttr file |} in
    let tree' := mk_tree (update_subtree pathname (TreeFile inum file') (TStree ts !!)) ilist' frees' in
    treeseq_pred (treeseq_grow_safe pathname off flag tree') ts ->
    treeseq_pred (treeseq_upd_safe pathname off flag tree') ts.
  Proof.
    intros.
    unfold treeseq_pred.
    eapply NEforall_d_in'; intros.
    unfold treeseq_upd_safe.
    intros.
    unfold treeseq_pred in H.
    eapply NEforall_d_in in H as H'; eauto.
  Qed.

  Lemma treeseq_grow_safe_grow: forall ts pathname inum off flag file ilist' frees',
    let file' := {|
                 BFILE.BFData := setlen (BFILE.BFData file) 1 ($ (0), []);
                 BFILE.BFAttr := BFILE.BFAttr file |} in
    let tree' := mk_tree (update_subtree pathname (TreeFile inum file') (TStree ts !!)) ilist' frees' in
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum file) ->
    True ->
    treeseq_pred (treeseq_grow_safe pathname off flag ts !!) ts ->
    True ->
    treeseq_pred (treeseq_grow_safe pathname off flag tree') ts.
   Proof.
    intros.
    unfold treeseq_pred.
    eapply NEforall_d_in'.
    intros.
    unfold treeseq_pred in H1.
    eapply NEforall_d_in in H1 as H1'; eauto.
    unfold treeseq_grow_safe in *.
    intros.
    specialize (H1' bn inum file).
    edestruct H1'.
    eassumption.
    destruct (find_subtree pathname (TStree x)).
    destruct d.
    split; eauto.
    subst tree'; simpl in *.
    erewrite find_update_subtree in H4.
    inversion H4.
    intuition.
    subst; eauto.
    rewrite <- H8.
    rewrite H9.
    eassumption.
    eauto.
    eauto.
  Qed.

  Lemma treeseq_upd_safe_truncate: forall F1 ts pathname off flag inum file ilist' frees',
    let file' := {|
               BFILE.BFData := setlen (BFILE.BFData file) 1 ($ (0), []);
               BFILE.BFAttr := BFILE.BFAttr file |} in
    let tree' := mk_tree (update_subtree pathname (TreeFile inum file') (TStree ts !!)) ilist' frees' in
    treeseq_pred (treeseq_grow_safe pathname off flag ts !!) ts ->
    (F1 * pathname |-> Some (inum, file))%pred (dir2flatmem2 (TStree ts !!)) ->
    tree_names_distinct (TStree ts !!) ->
    treeseq_pred (treeseq_upd_safe pathname off flag tree') (pushd tree' ts).
  Proof.
    intros.
    unfold treeseq_pred.
    eapply NEforall_treeseq_upd_safe_pushd.
    eapply treeseq_upd_safe_truncate'; eauto.
    eapply treeseq_grow_safe_grow; auto.
    eapply dir2flatmem2_find_subtree_ptsto; eauto.
  Qed.
*)

  Theorem treeseq_file_getattr_ok : forall fsxp inum mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
         [[ r = BFILE.BFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_get_attr fsxp inum mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_getattr_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
  Qed.

  Theorem treeseq_lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ DIRTREE.dirtree_inum (TStree ts !!) = dnum ]] *
      [[ DIRTREE.dirtree_isdir (TStree ts !!) = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
      [[ (isError r /\ None = DIRTREE.find_name fnlist (TStree ts !!)) \/
         (exists v, r = OK v /\ Some v = DIRTREE.find_name fnlist (TStree ts !!))%type ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} AFS.lookup fsxp dnum fnlist mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.lookup_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
  Qed.

  Theorem treeseq_read_fblock_ok : forall fsxp inum off mscs,
    {< ds ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} AFS.read_fblock fsxp inum off mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.read_fblock_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    eassumption.
  Qed.

  Lemma dirtree_block_belong_to_file_setattr_fwd: forall Fm fsxp Ftop pathname d d' tree attr f ilist ilist' frees frees' bn inum off,
    let tree' := update_subtree pathname (TreeFile inum
                     {|
                     BFILE.BFData := BFILE.BFData f;
                     BFILE.BFAttr := attr |}) tree in
    (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) ->
    (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')%pred (list2nmem d') ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist bn inum off ->
    BFILE.block_belong_to_file ilist' bn inum off.
  Proof.
    (* proof: changing the attr doesn't effect blocks: inum off must be same bn *)
    intros.

    eapply tree_file_length_ok in H as Hlength; eauto.
    eapply BFILE.block_belong_to_file_inum_ok in H2 as Hinum; eauto.

    subst tree'.
    unfold BFILE.block_belong_to_file in *; split.


    unfold rep, BFILE.rep, INODE.rep in H0. destruct_lift H0.
    setoid_rewrite listmatch_extract with (i := inum) in H0 at 2.
    unfold BFILE.file_match in H0 at 2; destruct_lift H0.
    setoid_rewrite listmatch_extract with (i := off) in H0 at 3.
    destruct_lift H0.
    rewrite map_length in *.


    eapply sep_star_assoc_1 in H6.
    setoid_rewrite sep_star_comm in H6.
    eapply sep_star_assoc_2 in H6.
    eapply tree_file_flist with (pathname := pathname) in H6 as Hf; eauto.
    rewrite <- H9.
    intuition. 
    rewrite Hf; simpl; eauto.

    eapply sep_star_assoc_1 in H6.
    setoid_rewrite sep_star_comm in H6.
    eapply sep_star_assoc_2 in H6.
    eapply tree_file_flist with (pathname := pathname) in H6 as Hf; eauto.
    intuition. 
    rewrite Hf; simpl; eauto.

    eapply list2nmem_inbound.
    pred_apply.
    admit.  (* if find_subtree (update_tree .. ) = inum -> true *)

    intuition.

    unfold rep, BFILE.rep, INODE.rep in H0. destruct_lift H0.
    setoid_rewrite listmatch_extract with (i := inum) in H0 at 2.
    unfold BFILE.file_match in H0 at 2; destruct_lift H0.
    setoid_rewrite listmatch_extract with (i := off) in H0 at 3.
    destruct_lift H0.
    rewrite map_length in *.

    eapply sep_star_assoc_1 in H7.
    setoid_rewrite sep_star_comm in H7.
    eapply sep_star_assoc_2 in H7.
    eapply tree_file_flist with (pathname := pathname) in H7 as Hf; eauto.

    (* INODE.IBLocks ilist [[inum ]] = INODE.IBlocks ilist' [[inum]] 
       because both are equal to BFData f, because setattr didn't change blocks 
       find a way to rewrite both to BFdata f.
     *)
  Admitted.

  Lemma dirtree_block_belong_to_file_setattr_bwd: forall Fm fsxp Ftop pathname d d' tree attr f ilist ilist' frees frees' bn inum off,
    let tree' := update_subtree pathname (TreeFile inum
                     {|
                     BFILE.BFData := BFILE.BFData f;
                     BFILE.BFAttr := attr |}) tree in
    (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) ->
    (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')%pred (list2nmem d') ->
    find_subtree pathname tree = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file ilist' bn inum off ->
    BFILE.block_belong_to_file ilist bn inum off.
  Proof.
  Admitted.

  Lemma dirtree_block_belong_to_file_update_ne_fwd: forall Fm fsxp Ftop pathname0 pathname1 d d' tree f0 f1 ilist ilist' frees frees' bn inum0 inum1 off,
    let tree' := update_subtree pathname0 (TreeFile inum0 f0) tree in
    (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) ->
    (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')%pred (list2nmem d') ->
    pathname0 <> pathname1 ->
    find_subtree pathname1 tree = Some (TreeFile inum1 f1) ->
    BFILE.block_belong_to_file ilist bn inum1 off ->
    BFILE.block_belong_to_file ilist' bn inum1 off.
  Proof.
  Admitted.

  Lemma dirtree_block_belong_to_file_update_ne_bwd: forall Fm fsxp Ftop pathname0 pathname1 d d' tree f0 f1 ilist ilist' frees frees' bn inum0 inum1 off,
    let tree' := update_subtree pathname0 (TreeFile inum0 f0) tree in
    (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)%pred (list2nmem d) ->
    (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')%pred (list2nmem d') ->
    pathname0 <> pathname1 ->
    find_subtree pathname1 tree = Some (TreeFile inum1 f1) ->
    BFILE.block_belong_to_file ilist' bn inum1 off ->
    BFILE.block_belong_to_file ilist bn inum1 off.
  Proof.
  Admitted.

  Lemma treeseq_safe_pushd_attr: forall Fm fsxp Ftop d d' ts pathname ilist' attr f inum  mscs pathname',
  let tree' := {|
      TStree := update_subtree pathname
                  (TreeFile inum
                     {|
                     BFILE.BFData := BFILE.BFData f;
                     BFILE.BFAttr := attr |}) 
                  (TStree ts !!);
      TSilist := ilist';
      TSfree := TSfree ts !! |} in
  (Fm * DIRTREE.rep fsxp Ftop (TStree ts !!) (TSilist ts !!) (TSfree ts !!))%pred (list2nmem d) ->
  (Fm * DIRTREE.rep fsxp Ftop (TStree tree') ilist' (TSfree ts !!))%pred (list2nmem d') ->
  find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
  treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
  treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (pushd tree' ts) !!) (pushd tree' ts).
  Proof.
    intros.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    subst tree'.
    eapply NEforall_d_in in H2.
    2: instantiate (1 := x); eauto.
    destruct (list_eq_dec string_dec pathname pathname'); simpl.
    - rewrite e in *; simpl.
      unfold treeseq_safe in *.
      intuition; simpl.
      * unfold treeseq_safe_fwd in *.
        intros; simpl.
        specialize (H4 inum0 off bn).
        destruct H4.
        destruct H2.
        eexists x0.
        intuition.
        intuition.
        exists {| BFILE.BFData := BFILE.BFData f; BFILE.BFAttr := attr |}.
        erewrite find_update_subtree; eauto.
        rewrite H1 in H6.
        inversion H6.
        split; eauto.
        eapply dirtree_block_belong_to_file_setattr_fwd in H as Hbelong; eauto.
        rewrite <- H8; eassumption.
        rewrite <- H8; eassumption.
      * unfold treeseq_safe_bwd in *; intros.
        specialize (H5 inum off bn).
        destruct (lt_dec off (Datatypes.length (BFILE.BFData f))).
        destruct H5.
        eexists f.
        split; eauto.
        simpl in *.
        intuition.
        eapply dirtree_block_belong_to_file_setattr_bwd; eauto.
        destruct H2.
        erewrite find_update_subtree in H2.
        intuition.
        inversion H5; eauto.
        eassumption.
        destruct H5.
        intuition.
        left.
        eexists x0.
        rewrite <- e in *.
        simpl in *.
        destruct H2.
        erewrite find_update_subtree in H2.
        intuition.
        inversion H5.
        rewrite H9 in *; eauto.
        inversion H5.
        rewrite H9 in *; eauto.
        eassumption.
        right; eauto.
        right; eauto.
        rewrite <- e in *.
        (* XXX contradiction from H2 follows that off < BFData f *)
        destruct H2.
        intuition.
        simpl in *.
        erewrite find_update_subtree in H6.
        inversion H6.
        rewrite H8 in *.
        (* XXX from H7 we must be able conclude that off < BFData f *)
        exfalso.
        admit.
        eassumption.
     - unfold treeseq_safe in *.
      intuition; simpl.
      * unfold treeseq_safe_fwd in *; simpl.
        (* we updated pathname, but pathname' is still safe, if it was safe. *)
        erewrite find_subtree_update_subtree_ne_path; eauto.
        intros.
        specialize (H4 inum0 off bn).
        destruct H4.
        destruct H2.
        eexists x0.
        eassumption.
        eexists x0.
        split. intuition.
        intuition.
        eapply dirtree_block_belong_to_file_update_ne_fwd with (tree := (TStree ts !!)); eauto.
      * unfold treeseq_safe_bwd in *; simpl.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        intros.
        specialize (H5 inum0 off bn).
        destruct H5.
        destruct H2.
        eexists x0.
        split.
        intuition.
        intuition.
        eapply dirtree_block_belong_to_file_update_ne_bwd with (tree := (TStree ts !!)); eauto.
        destruct H5.
        left.
        eexists x0.
        eassumption.
        right; eauto. 
  Admitted.

  Theorem treeseq_file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
     [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
     [[ (Ftree * pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs', ok)
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = true  ]] * exists d ds' ts' tree' ilist' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' (TSfree ts !!)) ]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') (TStree ts!!) ]] *
        [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
        [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
        [[ (Ftree * pathname |-> Some (inum, f'))%pred (dir2flatmem2 tree') ]])
  XCRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_set_attr fsxp inum attr mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_set_attr_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl.
    rewrite H4 in H11.
    eassumption.
    rewrite H4 in *.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred.
    eapply treeseq_safe_pushd_attr; eauto.
    eapply dir2flatmem2_find_subtree_ptsto in H0; eauto.
    distinct_names.
    eapply dir2flatmem2_update_subtree.
    distinct_names'.
    eassumption.
  Qed.


  (* A more restricted version intended to be used with treeseq_safe_upd. This restricted
   * version allows only extending a file by one block. It promises that if treeseq_upd_safe holds
   * afterwards. 
   *)
  Theorem treeseq_file_grow_ok : forall fsxp inum newlen mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
     [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ newlen >= Datatypes.length (BFILE.BFData f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) 1 ($0, nil)) (BFILE.BFAttr f) ]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * pathname |-> Some (inum, f'))%pred (dir2flatmem2 tree') ]])
  XCRASH:hm'
    LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_truncate fsxp inum newlen mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_truncate_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl in *.
    rewrite H0 in H12.
    eassumption.
    erewrite pushd_latest; simpl.
    eapply treeseq_upd_safe_truncate; eauto.
    rewrite H0; eauto.
    distinct_names'.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
  Qed.

  Fact block_belong_to_file_bn_eq: forall tree bn bn0 inum off,
    BFILE.block_belong_to_file tree bn inum off ->
    BFILE.block_belong_to_file tree bn0 inum off ->
    bn = bn0.
  Proof.
    intros;
    unfold BFILE.block_belong_to_file in *.
    intuition.
  Qed.

(*
  Lemma treeseq_upd_safe_upd: forall Fm fsxp Ftop mscs Ftree Fd ts ds d' pathname f f' off vs v inum bn,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum f') (TStree ts !!)) (TSilist ts !!)
         (fst (TSfree ts !!), snd (TSfree ts !!)))%pred (list2nmem (dsupd ds bn (v, vsmerge vs)) !!)->
    (Ftree ✶ pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts !!)) -> 
    (Fd ✶ off |-> vs)%pred (list2nmem (BFILE.BFData f)) ->
    (Fd ✶ off |-> (v, vsmerge vs))%pred (list2nmem (BFILE.BFData f')) ->
    BFILE.block_belong_to_file (TSilist ts !!) bn inum off ->
    treeseq_upd_safe pathname off (MSAlloc mscs) ts !! d' ->
    tree_names_distinct (TStree ts !!) ->
    treeseq_upd_safe pathname off (MSAlloc mscs)
      (treeseq_one_upd ts !! pathname off (v, vsmerge vs))
      (treeseq_one_upd d' pathname off (v, vsmerge vs)).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'; eauto.
    unfold treeseq_one_upd.
    erewrite dir2flatmem2_find_subtree_ptsto; eauto.
    case_eq (DIRTREE.find_subtree pathname (TStree d')).
    - (* case 1: a directory or a file *)
      intros; subst.
      destruct d.
      + (* a file *)
        destruct (lt_dec off (Datatypes.length (BFILE.BFData b))).
        * (* block is present *) 
          unfold treeseq_upd_safe in *. simpl in *; intros.
          erewrite find_update_subtree in H7; eauto.
          inversion H7; subst.
          right.
          exists {|
             BFILE.BFData := (BFILE.BFData b) ⟦ off := (v, vsmerge vs) ⟧;
             BFILE.BFAttr := BFILE.BFAttr b |}.
          specialize (H4 bn inum0 f H0' H3).
          rewrite H6 in H4.
          destruct H4; auto.
          (* case 1 of H4: block is in unused in old tree *)
          intuition.
          omega.
          omega.
           (* case 2 of H4: block is in use in old tree *)
          destruct H4.
          erewrite find_update_subtree; eauto.
          intuition.
          inversion H9; eauto.
          eapply block_belong_to_file_bn_eq in H8; eauto.
          subst; eauto.
        * (* block isn't present *)
          unfold treeseq_upd_safe in *. simpl in *. intros.
          erewrite find_update_subtree in H7; eauto.
          inversion H7; subst.
          specialize (H4 bn inum0 f H0' H3).
          destruct H4.
          rewrite H6 in H4 at 1.
          destruct H4.
          left.
          (* case 1 of H4: block is unused *)
          eapply block_belong_to_file_bn_eq in H8; eauto.
          subst; eauto.
          erewrite find_update_subtree; eauto.
          split; eauto.
          intuition.
          erewrite updN_oob; eauto.
          (* case 2 of H4: block is in use *)
          right.
          destruct H4.
          exists x.
          erewrite updN_oob; eauto.
          erewrite find_update_subtree; eauto.
          intuition.
          inversion H9.
          rewrite H6.
          f_equal.
          f_equal.
          destruct b; eauto.
          eapply block_belong_to_file_bn_eq in H8; eauto.
          subst; eauto.
          omega.
       + (* a directory *)
        unfold treeseq_upd_safe in H4.
        specialize (H4 bn inum f H0' H3).
        rewrite H6 in H4.
        destruct H4.
        (* first case *)
        intuition.
        (* second case *)
        destruct H4.
        intuition.
        inversion H7.
    - (* case 2: non existing *)
      unfold treeseq_upd_safe in *. simpl in *; intros.
      erewrite find_update_subtree in H7; eauto.
      inversion H7; subst.
      specialize (H4 bn inum0 f H0' H3).
      rewrite H6 in H4.
      left.
      destruct H4.
      (* case 1 of H4: block is unused *)
      split.
      eapply block_belong_to_file_bn_eq in H8; eauto.
      subst; eauto.
      intuition.
      rewrite H6; eauto.
     (* case 2 of H4: block is in use in a file *)
      destruct H4.
      intuition.
      exfalso.
      inversion H9.
      inversion H9.
   Qed.
*)

  (* A less general version of AFS.update_fblock_d, but easier to use for applications.
   * It requires treeseq_upd_safe for the trees in the treeseq 
   *)
  Theorem treeseq_update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists ts' f' ds' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
       [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ (Ftree * pathname |-> Some (inum, f'))%pred (dir2flatmem2 (TStree ts' !!)) ]] *
       [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists ds' ts' mscs' bn,
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
         [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
         [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
         [[ BFILE.block_belong_to_file (TSilist ts !!) bn inum off ]]
   >} AFS.update_fblock_d fsxp inum off v mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.update_fblock_d_ok.
    safecancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.


    pose proof (list2nmem_array (BFILE.BFData f)).
    pred_apply.
    erewrite arrayN_except with (i := off).
    cancel.

    eapply list2nmem_inbound; eauto.

    safestep.

    eapply list2nmem_sel in H5 as H5'.
    rewrite <- H5'.
    eapply treeseq_in_ds_upd; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    reflexivity.

(*
    unfold BFILE.diskset_was in H20.
    intuition.
    clear H5'.
    subst; eauto.
    (* should be impossible once haogang gets rid of [diskset_was] *)
    admit.
    reflexivity. *)

    admit.

    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H6; deex; intuition.
    eapply NEforall_d_in in H7; try eassumption.
    unfold tsupd; rewrite d_map_latest.

    eapply treeseq_upd_safe_upd; eauto.
    eapply list2nmem_sel in H5 as H5'.
    rewrite <- H5' in *; eauto.

    pred_apply.
    rewrite arrayN_ex_frame_pimpl; eauto.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'.
    cancel.

    rewrite H17; eauto.
    distinct_names'.
    
    instantiate (1 := f').
    unfold tsupd.
    erewrite d_map_latest.
    unfold treeseq_one_upd.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'.
    destruct (find_subtree pathname (TStree ts !!)); try congruence.
    destruct d; try congruence; simpl.
    inversion H0'.
    assert( f' = {|
           BFILE.BFData := (BFILE.BFData f) ⟦ off := (v, vsmerge vs) ⟧;
           BFILE.BFAttr := BFILE.BFAttr f |}).
    destruct f'.
    f_equal.
    simpl in H14.
    eapply list2nmem_array_updN in H14.
    rewrite H14.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; auto.
    eapply list2nmem_ptsto_bound in H5 as H5'; eauto.
    eauto.
    rewrite H6.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    distinct_names'.
    simpl; eauto.
    pred_apply.
    rewrite arrayN_ex_frame_pimpl; eauto.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'.
    cancel.
    assumption.

    xcrash_rewrite.
    xcrash_rewrite.
    xform_norm.
    cancel.
    or_r.
    eapply pimpl_exists_r; eexists.
    repeat (xform_deex_r).
    xform_norm; safecancel.
    eapply treeseq_in_ds_upd; eauto.
    eapply dir2flatmem2_find_subtree_ptsto; eauto.
    distinct_names'.
    eassumption.
    Unshelve.
    all: exact ($0, nil).
  Admitted.

  (* XXX maybe inum should be an argument and the TreeFile case should be split into two cases. *)
  Definition treeseq_one_file_sync (t: treeseq_one) pathname :=
      match find_subtree pathname (TStree t) with
      | None => t
      | Some (TreeFile inum f) => 
        mk_tree (update_subtree pathname (TreeFile inum (BFILE.synced_file f)) (TStree t)) (TSilist t) (TSfree t)
      | Some (TreeDir _ _) => t
      end.

  Definition ts_file_sync pathname (ts: treeseq) :=
    d_map (fun t => treeseq_one_file_sync t pathname) ts.

  Theorem dirtree_update_safe_pathname_vssync_vecs_file:
    forall pathname f tree fsxp F F0 ilist freeblocks inum m al,
    let tree_newest := update_subtree pathname (TreeFile inum (BFILE.synced_file f)) tree in
    find_subtree pathname tree = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file ilist (selN al i 0) inum i) ->
    (F0 * rep fsxp F tree ilist freeblocks)%pred (list2nmem m) ->
    (F0 * rep fsxp F tree_newest ilist freeblocks)%pred (list2nmem (vssync_vecs m al)).
  Proof.
    induction al using rev_ind; simpl; intros.
    - intuition. simpl. pred_apply.
      (* H3 implies length of BFILE.sync_file is also 0 *)
      admit.
    - Search vssync_vecs.
  Admitted.

(*
  Lemma tree_rep_nth_file_sync: forall Fm Ftop fsxp mscs ds ts n al pathname inum off f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs) ts !!) ts ->
    tree_rep Fm Ftop fsxp (treeseq_one_file_sync (nthd n ts) pathname) (list2nmem (vssync_vecs (nthd n ds) al)).
  Proof.
    intros.
    eapply NEforall_d_in in H4 as H4'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_upd_safe in H4'.
    edestruct H4'; eauto.
    admit.  (* H1 *)
    - (* block is unused in nth tree *) 
      intuition.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
      case_eq d; intros; subst.
      + (* nth tree has a file for pathname *)
        rewrite H5 in H8. 
        unfold treeseq_one_file_sync.
        rewrite H5; simpl.
        unfold tree_rep. simpl.
        (* XXX with al = all blocks in f, not al = all block in latest *)
        eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.
        (* XXX should treeseq_up_safe say that all blocks of f' are in f.
         * then, we can prove that al covers all the blocks of f'. *)
        admit.
        admit.
      + (* nth tree has a directory at pathname *)
        rewrite H5 in H8.
        exfalso. eauto.
      + (* nth tree has no file *)
        rewrite H5 in H8.
        unfold treeseq_one_file_sync.
        rewrite H5.
        (* XXX need to conclude al = [], maybe from updated treeseq_upd_safe *)
        admit.
    - (* block belongs in nth tree *)
      destruct H5.
      intuition.
      unfold treeseq_one_file_sync.
      rewrite H1.
      eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.
      admit.  (* XXX same as above *)
      admit.
  Admitted.

  Lemma tree_safe_file_sync: forall Fm Ftop fsxp mscs ds ts mscs' n al pathname inum off f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs) ts !!) ts ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) 
     (d_map (fun t : treeseq_one => treeseq_one_file_sync t pathname) ts) !! mscs'.
  Proof.
    intros.
    rewrite d_map_latest.
    eapply NEforall_d_in in H3 as H3'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_upd_safe in H3'.
    edestruct H3'; eauto.
    admit.  (* H1 *)
    - (* block is unused in nth tree *) 
      intuition.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
      case_eq d; intros; subst.
      + (* nth tree has a file for pathname *)
        unfold treeseq_one_file_sync. rewrite H5; simpl. rewrite H; simpl.
        rewrite H5 in H8.
        intuition.
        subst; simpl.
        admit.
      + (* nth trree has a directory for pathname, but shorter *)
        rewrite H5 in H8. exfalso. eauto.
      + (* nth tree has nothing for pathname *) 
        rewrite H5 in H8.
        unfold treeseq_one_file_sync; simpl.
        rewrite H; simpl.
        rewrite H5; simpl.
        unfold treeseq_one_safe; simpl.
        admit.
    - (* block is in nth three *)
      destruct H5.
      intuition.
      unfold treeseq_one_file_sync.
      rewrite H1; simpl.
      rewrite H; simpl.
  Admitted.

  Lemma treeseq_in_ds_file_sync: forall  Fm Ftop fsxp mscs mscs' ds ts al pathname inum off f,
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs) ts !!) ts ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (BFILE.BFData f) ->
    (length al = length (BFILE.BFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
    treeseq_in_ds Fm Ftop fsxp mscs' (ts_file_sync pathname ts) (dssync_vecs ds al).
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold ts_file_sync, dssync_vecs.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_file_sync; eauto.
    eapply tree_safe_file_sync; eauto.
  Qed.
*)

  (* A less general version of AFS.file_sync, but easier to use for applications.
   * It requires treeseq_upd_safe for the trees in the treeseq 
   *)
  Theorem treeseq_file_sync_ok : forall fsxp inum mscs,
    {< ds ts Fm Ftop Ftree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> Some (inum, f))%pred (dir2flatmem2 (TStree ts!!)) ]]
    POST:hm' RET:^(mscs')
      exists ts' ds' al,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = dssync_vecs ds al]] *
       [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i ]] *
       [[ ts' = ts_file_sync pathname ts ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ (Ftree * pathname |-> Some (inum, (BFILE.synced_file f)))%pred (dir2flatmem2 (TStree ts' !!)) ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.file_sync fsxp inum mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_sync_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.
    eapply treeseq_in_ds_file_sync; eauto.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'.
    eassumption.
    distinct_names'.
    unfold ts_file_sync.
    rewrite d_map_latest.
    unfold treeseq_one_file_sync.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'; eauto.
    destruct (find_subtree pathname (TStree ts!!)).
    destruct d.
    simpl.
    inversion H4'.
    subst; simpl.
    eapply dir2flatmem2_update_subtree.
    distinct_names'.
    eassumption.
    inversion H4'.
    inversion H4'.
    distinct_names'.
  Qed.

  Lemma treeseq_latest: forall (ts : treeseq),
    (ts !!, []) !! = ts !!.
  Proof.
    intros.
    unfold latest.
    simpl; reflexivity.
  Qed.

  Theorem treeseq_tree_sync_ok : forall fsxp mscs,
    {< ds ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]]
    POST:hm' RET:^(mscs')
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ((ts !!), nil) (ds!!, nil)]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.tree_sync fsxp mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.tree_sync_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H5 as Hpred; eauto.
    step.
    unfold treeseq_in_ds.
    unfold NEforall2.
    simpl in *.
    split.
    split.
    unfold treeseq_in_ds in H5.
    eapply NEforall2_latest in H5.
    intuition.
    simpl.
    unfold treeseq_in_ds in H5.
    eapply NEforall2_latest in H5.
    intuition.
    unfold treeseq_one_safe in *.
    simpl in *.
    rewrite H9; simpl.
    erewrite treeseq_latest.
    eapply dirtree_safe_refl.
    constructor.
  Qed.


Lemma find_subtree_find_dirlist_eq: forall name inum dents ,
  find_subtree [name] (TreeDir inum dents) = find_dirlist name dents.
Proof.
  intros.
Admitted.

  Theorem treeseq_rename_ok : forall fsxp dnum srcbase (srcname:string) dstbase dstname mscs,
    {< ds ts Fm Ftop Ftree cwd tree_elem srcnum dstnum srcfile dstfile,
    PRE:hm
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ DIRTREE.find_subtree cwd (TStree ts !!) = Some (DIRTREE.TreeDir dnum tree_elem) ]] *
      [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Some (srcnum, srcfile)
                * (cwd ++ dstbase ++ [dstname]) |-> Some (dstnum, dstfile))%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
       [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           pathname' <> cwd ++ srcbase ++ [srcname] ->
           pathname' <> cwd ++ dstbase ++ [dstname] ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = (pushd d ds) ]] *
       [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
       [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
       [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> None
                 * (cwd ++ dstbase ++ [dstname]) |-> Some (srcnum, srcfile))%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} AFS.rename fsxp dnum srcbase srcname dstbase dstname mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.rename_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eassumption.
    step.
    unfold AFS.rename_rep.
    cancel.
    or_r.

    (* a few obligations need: subtree = (TreeFile srcnum srcfile) using H0 *)
    eapply sep_star_split_l in H0 as H0'.
    destruct H0'.
    eapply dir2flatmem2_find_subtree_ptsto in H5.
    erewrite find_subtree_app in H5.
    2: eassumption.
    erewrite find_subtree_find_dirlist_eq in H5.
    rewrite H14 in H5.
    inversion H5.
    rewrite H11 in *.

    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    rewrite H4 in H9.
    eassumption.
    eapply dirents2mem2_graft_file'.
    admit.  (* XXX distinct names *)
    eapply dirents2mem2_prune_file.
    admit. (* XXX distinct names *)
    pred_apply.
    cancel.
    cancel.
    admit. (* XXX distinct names *)
  Admitted.

  (* restricted to deleting files *)
  Theorem treeseq_delete_ok : forall fsxp dnum name mscs,
    {< ds ts pathname Fm Ftop Ftree tree_elem finum file,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ DIRTREE.find_subtree pathname (TStree ts !!) = Some (DIRTREE.TreeDir dnum tree_elem) ]] *
      [[ (Ftree * ((pathname++[name])%list) |-> Some (finum, file))%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      [[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm \/
      [[ ok = OK tt ]] * exists d ds' ts' tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ forall pathname',
           pathname' <> pathname ++ [name] ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
        [[ tree' = DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name]) |-> None)%pred (dir2flatmem2 (TStree ts' !!)) ]]
    CRASH:hm
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm
    >} AFS.delete fsxp dnum name mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.delete_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eassumption.
    step.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold treeseq_one_safe; simpl.
    rewrite H0 in H12.
    eassumption.
    eapply dir2flatmem2_delete_file; eauto.
    distinct_names'.
  Qed.


  Hint Extern 1 ({{_}} Bind (AFS.file_get_attr _ _ _) _) => apply treeseq_file_getattr_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.lookup _ _ _ _) _) => apply treeseq_lookup_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.read_fblock _ _ _ _) _) => apply treeseq_read_fblock_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_set_attr _ _ _ _) _) => apply treeseq_file_set_attr_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.update_fblock_d _ _ _ _ _) _) => apply treeseq_update_fblock_d_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_sync _ _ _ ) _) => apply treeseq_file_sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_truncate _ _ _ _) _) => apply treeseq_file_grow_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.tree_sync _ _ ) _) => apply treeseq_tree_sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.rename _ _ _ _ _ _ _) _) => apply treeseq_rename_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.delete _ _ _ _) _) => apply treeseq_delete_ok : prog.

End TREESEQ.

