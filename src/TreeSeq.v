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
Require Import DirTreePath.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreePred.
Require Import DirTreeNames.
Require Import DirTreeInodes.
Require Import DirTreeSafe.


Import DIRTREE.
Import ListNotations.

Module TREESEQ.

  (**
   * A layer over AFS that provides the same functions but with treeseq
   * and dirsep specs. This layer provides the treeseq_safe property (see below),
   * which makes it easier for application writers to reason about the file system,
   * compared to using the AFS specs directly.
   *)

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Record treeseq_one := mk_tree {
    TStree  : dirtree;
    TSilist : list INODE.inode;
    TSfree  : list addr * list addr
  }.

  Definition treeseq_one_safe t1 t2 mscs :=
    dirtree_safe (TSilist t1) (BFILE.pick_balloc (TSfree t1) (MSAlloc mscs)) (TStree t1)
                         (TSilist t2) (BFILE.pick_balloc (TSfree t2) (MSAlloc mscs)) (TStree t2).

  Theorem treeseq_one_safe_refl : forall t mscs,
    treeseq_one_safe t t mscs.
  Proof.
    intros.
    apply dirtree_safe_refl.
  Qed.

  Theorem treeseq_one_safe_trans : forall t1 t2 t3 mscs,
    treeseq_one_safe t1 t2 mscs ->
    treeseq_one_safe t2 t3 mscs ->
    treeseq_one_safe t1 t3 mscs.
  Proof.
    unfold treeseq_one_safe; intros.
    eapply dirtree_safe_trans; eauto.
  Qed.

  Definition treeseq := nelist treeseq_one.

  Definition tree_rep F Ftop fsxp t :=
    (exists bfms sm,
     F * rep fsxp Ftop (TStree t) (TSilist t) (TSfree t) bfms sm)%pred.

  Definition tree_rep_latest F Ftop fsxp sm t bfms :=
    (F * rep fsxp Ftop (TStree t) (TSilist t) (TSfree t) bfms sm)%pred.

  Definition treeseq_in_ds F Ftop fsxp sm mscs (ts : treeseq) (ds : diskset) :=
    NEforall2
      (fun t d => tree_rep F Ftop fsxp t (list2nmem d) /\
                  treeseq_one_safe t (latest ts) mscs)
      ts ds /\
    tree_rep_latest F Ftop fsxp sm (ts!!) mscs (list2nmem ds!!).

  Definition treeseq_pred (p : treeseq_one -> Prop) (ts : treeseq) := NEforall p ts.

  Theorem treeseq_pred_pushd : forall (p : treeseq_one -> Prop) t ts,
    p t ->
    treeseq_pred p ts ->
    treeseq_pred p (pushd t ts).
  Proof.
    unfold treeseq_pred, NEforall, pushd; simpl; intros.
    intuition.
  Qed.

  Theorem treeseq_in_ds_pushd : forall F Ftop fsxp sm mscs ts ds t mscs' d,
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    tree_rep_latest F Ftop fsxp sm t mscs' (list2nmem d) ->
    treeseq_one_safe (latest ts) t mscs ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs ->
    treeseq_in_ds F Ftop fsxp sm mscs' (pushd t ts) (pushd d ds).
  Proof.
    unfold treeseq_in_ds; simpl; intuition.
    apply NEforall2_pushd; intuition.
    rewrite latest_pushd.
    eapply NEforall2_impl; eauto.
    intuition.
    intuition.
    unfold treeseq_one_safe in *; intuition.
    rewrite H2 in *.
    eapply dirtree_safe_trans; eauto.
    unfold tree_rep; unfold tree_rep_latest in *. pred_apply; cancel.
    eapply dirtree_safe_refl.
  Qed.

  Definition treeseq_one_upd (t: treeseq_one) pathname off v :=
    match find_subtree pathname (TStree t) with
    | None => t
    | Some (TreeFile inum f) => mk_tree (update_subtree pathname 
                                  (TreeFile inum (mk_dirfile (updN (DFData f) off v) (DFAttr f))) (TStree t))
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

  Theorem treeseq_pred_impl : forall ts (p q : treeseq_one -> Prop),
    treeseq_pred p ts ->
    (forall t, p t -> q t) ->
    treeseq_pred q ts.
  Proof.
    unfold treeseq_pred; intros.
    eapply NEforall_impl; eauto.
  Qed.

  (**
   * [treeseq_safe] helps applications prove their own correctness properties, at
   * the cost of placing some restrictions on how the file system interface should
   * be used by the application.
   *
   * The two nice things about [treeseq_safe] is that, first, it names files by
   * pathnames (and, in particular, [treeseq_safe] for a file does not hold after
   * that file has been renamed).  Second, [treeseq_safe] avoids the shrink-and-regrow
   * problem that might arise if we were to [fdatasync] a file that has been shrunk
   * and re-grown.  Without [treeseq_safe], [fdatasync] on a shrunk-and-regrown file
   * would fail to sync the blocks that were shrunk and regrown, because the current
   * inode no longer points to those old blocks.  As a result, the contents of the
   * file on disk remains unsynced; this makes the spec of [fdatasync] complicated
   * in the general case when the on-disk inode block pointers differ from the in-memory
   * inode block pointers.
   *
   * [treeseq_safe] solves shrink-and-regrow by requiring that files monotonically
   * grow (or, otherwise, [treeseq_safe] does not hold).  When [treeseq_safe] stops
   * holding, the application can invoke [fsync] to flush metadata and, trivially,
   * re-establish [treeseq_safe] because there is only one tree in the sequence now.
   *
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
    treeseq_safe_fwd pathname tnewest tolder /\
    treeseq_safe_bwd pathname flag tnewest tolder /\
    BFILE.ilist_safe (TSilist tolder)  (BFILE.pick_balloc (TSfree tolder)  flag)
                     (TSilist tnewest) (BFILE.pick_balloc (TSfree tnewest) flag).

  Theorem treeseq_safe_trans: forall pathname flag t0 t1 t2,
    treeseq_safe pathname flag t0 t1 ->
    treeseq_safe pathname flag t1 t2 ->
    treeseq_safe pathname flag t0 t2.
  Proof.
    unfold treeseq_safe; intuition.
    - unfold treeseq_safe_fwd in *; intuition.
    - unfold treeseq_safe_bwd in *; intuition.
      specialize (H0 _ _ _ H3).
      inversion H0; eauto.
      right.
      unfold BFILE.ilist_safe in H5; destruct H5.
      eapply In_incl.
      apply H6.
      eauto.
    - eapply BFILE.ilist_safe_trans; eauto.
  Qed.

  Lemma tree_file_flist: forall F Ftop flist tree pathname inum f,
    find_subtree pathname tree = Some (TreeFile inum f) ->
    (F * tree_pred Ftop tree)%pred (list2nmem flist) ->
    tree_names_distinct tree ->
    exists c,
    selN flist inum BFILE.bfile0 = dirfile_to_bfile f c.
  Proof.
    intros.
    rewrite subtree_extract with (fnlist := pathname) (subtree := (TreeFile inum f)) in H0; eauto.
    unfold tree_pred in H0.
    destruct_lift H0.
    eapply list2nmem_sel in H0; eauto.
  Qed.


  Ltac distinct_names :=
    match goal with
      [ H: (_ * rep _ _ ?tree _ _ _ _)%pred (list2nmem _) |- tree_names_distinct ?tree ] =>
        eapply rep_tree_names_distinct; eapply H
    end.

  Ltac distinct_inodes :=
    match goal with
      [ H: (_ * rep _ _ ?tree _ _ _)%pred (list2nmem _) |- tree_inodes_distinct ?tree ] => 
        eapply rep_tree_inodes_distinct; eapply H
    end.

  Lemma tree_file_length_ok: forall F Ftop fsxp ilist frees mscs sm d tree pathname off bn inum f,
      (F * rep Ftop fsxp tree ilist frees mscs sm)%pred d ->
      find_subtree pathname tree = Some (TreeFile inum f) ->
      BFILE.block_belong_to_file ilist bn inum off ->
      off < Datatypes.length (DFData f).
  Proof.
    intros.
    eapply rep_tree_names_distinct in H as Hdistinct.
    apply BFILE.block_belong_to_file_inum_ok in H1 as H1'.

    unfold rep in H.
    unfold BFILE.rep in H.
    destruct_lift H.

    denote find_subtree as Hf.
    denote tree_pred as Ht.
    eapply tree_file_flist in Hf; eauto.
    2: eapply pimpl_apply; [| exact Ht]; cancel.
    2: eassign Ftop; cancel.
    deex.

    erewrite listmatch_extract with (i := inum) in H.
    unfold BFILE.file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFILE.BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    unfold BFILE.datatype, datatype in *.
    unfold BFILE.block_belong_to_file in H1.
    intuition.
    subst.
    denote dirfile_to_bfile as Hd.
    rewrite Hd in *.
    unfold dirfile_to_bfile in *. cbn in *.
    simplen.

    rewrite listmatch_length_pimpl in H.
    destruct_lift H.
    simplen.
  Qed.


  Lemma treeseq_in_ds_tree_pred_latest: forall Fm Ftop fsxp sm mscs ts ds,
   treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
   (Fm ✶ rep fsxp Ftop (TStree ts !!) (TSilist ts!!) (TSfree ts!!) mscs sm)%pred (list2nmem ds !!).
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    intuition.
  Qed.

  Lemma treeseq_in_ds_tree_pred_nth: forall Fm Ftop fsxp sm mscs ts ds n,
   treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
   (exists bfms,
    Fm ✶ rep fsxp Ftop (TStree (nthd n ts)) (TSilist (nthd n ts)) (TSfree (nthd n ts)) bfms sm)%pred (list2nmem (nthd n ds)).
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    intuition.
    unfold tree_rep in H0.
    eapply NEforall2_d_in with (x := nthd n ts) in H0 as H0'.
    intuition.
    eassumption.
    reflexivity.
    reflexivity.
  Qed.


  Lemma treeseq_safe_refl : forall pathname flag tree,
   treeseq_safe pathname flag tree tree.
  Proof.
    intros.
    unfold treeseq_safe, treeseq_safe_fwd, treeseq_safe_bwd.
    intuition.
    apply BFILE.ilist_safe_refl.
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
    eapply treeseq_safe_refl.
    eapply NEforall_d_in; eauto.
  Qed.


  Ltac distinct_names' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ ?ts _ |- tree_names_distinct (TStree ?ts !!) ] => 
        eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        destruct_lift Hpred;
        eapply rep_tree_names_distinct; eassumption
      | [ H: treeseq_in_ds _ _ _ _ ?ts _ |- tree_names_distinct (TStree (nthd ?n ?ts)) ] => 
        eapply treeseq_in_ds_tree_pred_nth in H as Hpred;
        destruct_lift Hpred;
        eapply rep_tree_names_distinct; eassumption
    end.

  Theorem treeseq_file_getattr_ok : forall fsxp inum mscs,
  {< ds sm ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
         [[ r = DFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm'
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
    step.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.
  Qed.

  Theorem treeseq_lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds sm ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ dirtree_inum (TStree ts !!) = dnum ]] *
      [[ dirtree_isdir (TStree ts !!) = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ (isError r /\ None = find_name fnlist (TStree ts !!)) \/
         (exists v, r = OK v /\ Some v = find_name fnlist (TStree ts !!))%type ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm'
     >} AFS.lookup fsxp dnum fnlist mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.lookup_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    step.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.
  Qed.

  Theorem treeseq_read_fblock_ok : forall fsxp inum off mscs,
    {< ds sm ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]] *
           [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm'
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
    step.

    unfold treeseq_in_ds in *; intuition.
    eapply NEforall2_impl; eauto; intros; simpl in *; intuition.
    unfold treeseq_one_safe in *; msalloc_eq; eauto.
  Qed.

  Lemma treeseq_block_belong_to_file: forall F Ftop fsxp t d pathname inum f off,
    tree_rep F Ftop fsxp t (list2nmem d) ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f)  ->
    off < Datatypes.length (DFData f) ->
    exists bn, BFILE.block_belong_to_file (TSilist t) bn inum off.
  Proof.
    unfold BFILE.block_belong_to_file.
    intros.
    eexists; intuition.
    unfold tree_rep in H; destruct_lift H.
    eapply rep_tree_names_distinct in H as Hdistinct.
    unfold rep in H; destruct_lift H.

    rewrite subtree_extract in H3; eauto.
    simpl in H3.
    destruct_lift H3.
    assert (inum < Datatypes.length dummy0).
    eapply list2nmem_inbound. 
    pred_apply; cancel.

    replace (DFData f) with (BFILE.BFData {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy3 |}) in H1 by reflexivity.

    erewrite list2nmem_sel with (x := {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy3 |}) (i := inum) (l := dummy0) in H1.
    2: pred_apply; cancel.

    clear H2.
    unfold BFILE.rep in H; destruct_lift H.
    rewrite listmatch_extract in H; eauto.

    unfold BFILE.file_match at 2 in H.
    erewrite listmatch_length_pimpl with (a := (BFILE.BFData dummy0 ⟦ inum ⟧)) in H.
    destruct_lift H.

    rewrite H16 in H1.
    rewrite map_length in H1.
    eauto.

  Grab Existential Variables.
    exact BFILE.bfile0.
  Qed.

  (* BFILE *)
  Fact block_belong_to_file_bn_eq: forall tree bn bn0 inum off,
    BFILE.block_belong_to_file tree bn inum off ->
    BFILE.block_belong_to_file tree bn0 inum off ->
    bn = bn0.
  Proof.
    intros;
    unfold BFILE.block_belong_to_file in *.
    intuition.
  Qed.

  Lemma find_subtree_none_not_pathname_prefix_1 : forall t pn1 pn2 inum2 f2,
    find_subtree pn2 t = Some (TreeFile inum2 f2) ->
    find_subtree pn1 t = None ->
    ~ pathname_prefix pn1 pn2.
  Proof.
    unfold pathname_prefix; intros. intro; deex.
    erewrite find_subtree_app_none in H.
    inversion H.
    eauto.
  Qed.

  Lemma find_subtree_dir_not_pathname_prefix_2 : forall t pn1 pn2 inum f dnum d,
      pn1 <> pn2 ->
      find_subtree pn1 t = Some (TreeDir dnum d) ->
      find_subtree pn2 t = Some (TreeFile inum f) ->
      ~ pathname_prefix pn2 pn1.
  Proof.
      unfold pathname_prefix; intros. intro; deex.
      erewrite find_subtree_app in H0; eauto.
      destruct suffix.
      eapply H. rewrite app_nil_r; eauto.
      rewrite find_subtree_file_none in H0.
      inversion H0.
  Qed.

  Lemma find_subtree_file_not_pathname_prefix : forall t pn1 pn2 inum1 f1 inum2 f2,
    find_subtree pn1 t = Some (TreeFile inum1 f1) ->
    find_subtree pn2 t = Some (TreeFile inum2 f2) ->
    pn1 <> pn2 ->
    ~ pathname_prefix pn1 pn2.
  Proof.
    intros. unfold pathname_prefix; intro.
    deex.
    erewrite find_subtree_app in H0 by eauto.
    destruct suffix; simpl in *; try congruence.
    rewrite app_nil_r in *; eauto.
  Qed.

  Lemma find_subtree_update_subtree_file_not_pathname_prefix_1 : forall t pn1 old pn2 inum1 f1 inum2 f2,
    find_subtree pn2 (update_subtree pn1 (TreeFile inum1 f1) t) = Some (TreeFile inum2 f2) ->
    find_subtree pn1 t = Some old ->
    pn1 <> pn2 ->
    ~ pathname_prefix pn1 pn2.
  Proof.
    unfold pathname_prefix; intros. intro; deex.
    erewrite find_subtree_app in * by eauto.
    destruct suffix; simpl in *; try congruence.
    rewrite app_nil_r in *; eauto.
  Qed.

  Lemma find_subtree_update_subtree_file_not_pathname_prefix_2 : forall t pn1 old pn2 inum1 f1 inum2 f2,
    find_subtree pn2 (update_subtree pn1 (TreeFile inum1 f1) t) = Some (TreeFile inum2 f2) ->
    find_subtree pn1 t = Some old ->
    pn1 <> pn2 ->
    ~ pathname_prefix pn2 pn1.
  Proof.
    unfold pathname_prefix; intros. intro; deex.
    case_eq (find_subtree pn2 t); intros.
    destruct d.
    erewrite find_subtree_app in * by eauto. destruct suffix; simpl in *; try congruence. rewrite app_nil_r in *; eauto.
    erewrite find_subtree_update_subtree_child in * by eauto.
    destruct suffix; simpl in *; try congruence. rewrite app_nil_r in *; eauto.
    erewrite find_subtree_app_none in * by eauto. congruence.
  Qed.

  Lemma treeseq_safe_pushd_update_subtree : forall Ftree ts pathname ilist' f f' inum  mscs pathname' free2,
    let tree' := {|
        TStree := update_subtree pathname
                    (TreeFile inum f') 
                    (TStree ts !!);
        TSilist := ilist';
        TSfree := free2 |} in
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    Datatypes.length ilist' = Datatypes.length (TSilist ts!!) ->
    (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) ->
    BFILE.ilist_safe (TSilist ts!!) (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs))
                     ilist' (BFILE.pick_balloc free2 (MSAlloc mscs)) ->
    BFILE.treeseq_ilist_safe inum (TSilist ts!!) ilist' ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (pushd tree' ts) !!) (pushd tree' ts).
  Proof.
    intros.
    subst tree'.
    eapply dir2flatmem2_find_subtree_ptsto in H as Hfind; eauto.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H5.
    2: instantiate (1 := x); eauto.
    destruct (list_eq_dec string_dec pathname pathname'); simpl.
    - rewrite e in *; simpl.
      unfold treeseq_safe in *.
      intuition; simpl.
      * unfold treeseq_safe_fwd in *.
        intros; simpl.
        specialize (H7 inum0 off bn).
        destruct H7.
        destruct H8.
        eexists x0.
        intuition.
        intuition.
        exists f'.
        erewrite find_update_subtree; eauto.
        rewrite Hfind in H10.
        inversion H10.
        unfold BFILE.treeseq_ilist_safe in *.
        intuition.
        specialize (H7 off bn).
        destruct H7.
        subst.
        eauto.
        subst.
        split; eauto.
      * unfold treeseq_safe_bwd in *; intros.
        destruct (BFILE.block_is_unused_dec (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs)) bn).
        ++ deex.
           right.
           unfold BFILE.ilist_safe in H9; intuition.
           eapply In_incl.
           apply b.
           eauto.

        ++ 
        specialize (H5 inum off bn).
        destruct H5.
        ** eexists f.
        split; eauto.
        simpl in *.
        subst.
        erewrite find_update_subtree in H8 by eauto.
        deex.
        inversion H8.
        unfold BFILE.ilist_safe in H3.
        intuition.
        specialize (H13 inum off bn).
        subst.
        destruct H13; eauto.

        exfalso. eauto.

        ** 
        destruct H5.
        simpl in *.
        erewrite find_update_subtree in H8.
        intuition. deex.
        inversion H8; eauto.
        subst.
        left.
        eauto.
        eauto.
        **
        right; eauto.

     * eapply BFILE.ilist_safe_trans; eauto.

     - unfold treeseq_safe in *.
      intuition; simpl.
      (* we updated pathname, but pathname' is still safe, if it was safe. *)
      * unfold treeseq_safe_fwd in *; simpl.
        intros; deex.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        intros.
        edestruct H7; eauto.
        intuition.
        eexists.
        intuition. eauto.
        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso. apply n.
          eapply find_subtree_inode_pathname_unique; eauto.

        **
        unfold BFILE.treeseq_ilist_safe in H4; intuition.
        unfold BFILE.block_belong_to_file.
        rewrite <- H14.
        apply H13.
        intuition.
        **
          unfold pathname_prefix; intro; deex.
          edestruct H7; eauto; intuition.
          erewrite find_subtree_app in H12 by eauto.
          destruct suffix; simpl in *; try congruence.
          rewrite app_nil_r in *; eauto.
        **
          unfold pathname_prefix; intro; deex.
          edestruct H7; eauto; intuition.
          erewrite find_subtree_app in Hfind by eauto.
          destruct suffix; simpl in *; try congruence.
          rewrite app_nil_r in *; eauto.
      * unfold treeseq_safe_bwd in *; simpl; intros.
        deex; intuition.
        erewrite find_subtree_update_subtree_ne_path in *; eauto.

        destruct (addr_eq_dec inum inum0).
        ** subst.
          exfalso. apply n.
          eapply find_subtree_inode_pathname_unique; eauto.
        **

        eapply H5.
        eexists. intuition eauto.

        unfold BFILE.treeseq_ilist_safe in H4; intuition.
        unfold BFILE.block_belong_to_file.
        rewrite H12.
        apply H11.
        intuition.
        **
          unfold pathname_prefix; intro; deex.
          erewrite find_subtree_app in * by eauto.
          destruct suffix; simpl in *; try congruence.
          rewrite app_nil_r in *; eauto.
        **
          eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
      * eapply BFILE.ilist_safe_trans; eauto.
  Qed.

  Ltac xcrash_solve :=
    repeat match goal with
           | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => eapply pimpl_trans; try apply H; cancel
           | [ |- crash_xform (LOG.rep _ _ _ _ _) =p=> _ ] => rewrite LOG.notxn_intact; cancel
           | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => rewrite H; xform_norm
           end.


  Lemma mscs_same_except_log_tree_rep_latest : forall mscs mscs' F Ftop fsxp t sm,
    BFILE.mscs_same_except_log mscs mscs' ->
    tree_rep_latest F Ftop fsxp sm t mscs =p=>
    tree_rep_latest F Ftop fsxp sm t mscs'.
  Proof.
    unfold tree_rep_latest; intros.
    rewrite mscs_same_except_log_rep by eassumption.
    cancel.
  Qed.

  Lemma mscs_parts_eq_tree_rep_latest : forall mscs mscs' F Ftop fsxp t sm,
    MSCache mscs' = MSCache mscs ->
    MSICache mscs' = MSICache mscs ->
    MSAllocC mscs' = MSAllocC mscs ->
    MSIAllocC mscs' = MSIAllocC mscs ->
    MSDBlocks mscs' = MSDBlocks mscs ->
    tree_rep_latest F Ftop fsxp t sm mscs =p=>
    tree_rep_latest F Ftop fsxp t sm mscs'.
  Proof.
    unfold tree_rep_latest; intros.
    unfold rep. unfold Balloc.IAlloc.rep. unfold Balloc.IAlloc.Alloc.rep; simpl.
    msalloc_eq.
    apply pimpl_refl.
  Qed.

  Lemma mscs_same_except_log_treeseq_one_safe : forall mscs mscs' t t',
    BFILE.mscs_same_except_log mscs mscs' ->
    treeseq_one_safe t t' mscs ->
    treeseq_one_safe t t' mscs'.
  Proof.
    unfold BFILE.mscs_same_except_log, treeseq_one_safe; intuition msalloc_eq.
    eauto.
  Qed.

  Lemma mscs_same_except_log_rep_treeseq_in_ds : forall F Ftop fsxp sm mscs mscs' ts ds,
    BFILE.mscs_same_except_log mscs mscs' ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    treeseq_in_ds F Ftop fsxp sm mscs' ts ds.
  Proof.
    unfold treeseq_in_ds.
    intuition eauto.
    eapply NEforall2_impl; eauto.
    intuition. intuition. intuition.
    eapply mscs_same_except_log_treeseq_one_safe; eauto.
    eapply mscs_same_except_log_tree_rep_latest; eauto.
  Qed.

  Lemma treeseq_in_ds_eq: forall Fm Ftop fsxp sm mscs a ts ds,
    BFILE.mscs_same_except_log a mscs ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds <->
    treeseq_in_ds Fm Ftop fsxp sm a ts ds.
  Proof.
    split; eapply mscs_same_except_log_rep_treeseq_in_ds; eauto.
    apply BFILE.mscs_same_except_log_comm; eauto.
  Qed.

  Lemma treeseq_in_ds_mscs' : forall Fm Ftop fsxp sm mscs mscs' ts ds,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    (Fm * rep fsxp Ftop (TStree ts !!) (TSilist ts !!) (TSfree ts !!) mscs' sm)%pred (list2nmem ds !!) ->
    MSAlloc mscs = MSAlloc mscs' ->
    treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds.
  Proof.
    unfold treeseq_in_ds, tree_rep_latest; intuition.
    eapply NEforall2_impl; eauto.
    intros; intuition.
    intuition.
    unfold treeseq_one_safe in *; intuition msalloc_eq.
    eauto.
  Qed.

  Theorem treeseq_file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds sm ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs', ok)
     [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
      [[ ok = OK tt  ]] * exists d ds' ts' tree' ilist' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' (TSfree ts !!) mscs' sm) ]]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts!!) ]] *
        [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
        [[ f' = mk_dirfile (DFData f) attr ]] *
        [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]])
   XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm' \/
       exists d ds' ts' mscs' tree' ilist' f',
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' sm hm' *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds' ]] *
         [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = pushd d ds ]] *
         [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' (TSfree ts !!) mscs' sm) ]]] *
         [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts!!) ]] *
         [[ ts' = pushd (mk_tree tree' ilist' (TSfree ts !!)) ts ]] *
         [[ f' = mk_dirfile (DFData f) attr ]] *
         [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]]
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
    or_l. cancel.
    eapply treeseq_in_ds_eq; eauto.
    unfold BFILE.mscs_same_except_log; intuition.
    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl.
    rewrite H in H12.
    eassumption.
    rewrite H in *.
    eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred.
    eapply treeseq_safe_pushd_update_subtree; eauto.
    distinct_names.
    distinct_inodes.
    rewrite rep_length in Hpred; destruct_lift Hpred.
    rewrite rep_length in H10; destruct_lift H10.
    congruence.

    unfold dirtree_safe in *.
    intuition.

    eapply dir2flatmem2_update_subtree.
    distinct_names'.
    eassumption.

    xcrash_solve.
    - xform_normr.
      or_l. cancel.
    - or_r. cancel. repeat (progress xform_norm; safecancel).
      eassumption.
      5: reflexivity.
      5: reflexivity.
      5: reflexivity.
      eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe.
      simpl.
      repeat rewrite <- surjective_pairing in *.
      rewrite H4 in *; eauto.
      eapply treeseq_in_ds_tree_pred_latest in H6 as Hpred.
      eapply treeseq_safe_pushd_update_subtree; eauto.
      distinct_names.
      distinct_inodes.
      rewrite rep_length in Hpred; destruct_lift Hpred.
      rewrite rep_length in H5; destruct_lift H5.
      congruence.
      unfold dirtree_safe in *.
      repeat rewrite <- surjective_pairing in *.
      rewrite H4 in *; eauto.
      intuition.
      eauto.
      repeat rewrite <- surjective_pairing in *.
      eauto.
      eapply dir2flatmem2_update_subtree.
      distinct_names'.
      eassumption.
  Qed.

  Theorem treeseq_file_grow_ok : forall fsxp inum newlen mscs,
  {< ds sm ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
     [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
     [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
     [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
     [[ newlen >= Datatypes.length (DFData f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ isError ok ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
      [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm)]]] *
        [[ f' = mk_dirfile (setlen (DFData f) newlen ($0, nil)) (DFAttr f) ]] *
        [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]])
  XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm' \/
       exists d ds' sm' ts' mscs' tree' ilist' f' frees',
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' sm' hm' *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
         [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = pushd d ds ]] *
         [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
         [[ f' = mk_dirfile (setlen (DFData f) newlen ($0, nil)) (DFAttr f) ]] *
         [[ tree' = update_subtree pathname (TreeFile inum f') (TStree ts !!) ]] *
         [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
         [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 tree') ]]
  >} AFS.file_truncate fsxp inum newlen mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_truncate_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred; eauto.
    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.
    step.

    or_l. cancel.
    eapply treeseq_in_ds_mscs'; eauto.

    or_r.
    cancel.
    eapply treeseq_in_ds_pushd; eauto.
    unfold tree_rep.
    unfold treeseq_one_safe.
    simpl in *.
    rewrite H in H14.
    eassumption.
    eapply treeseq_safe_pushd_update_subtree; eauto.
    distinct_names'.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
    distinct_inodes.
    eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
    rewrite rep_length in Hpred; destruct_lift Hpred.
    rewrite rep_length in H12; destruct_lift H12.
    congruence. 

    unfold dirtree_safe in *.
    intuition.
    rewrite H in H10; eauto.

    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    xcrash_solve.
    - xform_normr. or_l. cancel.
    - or_r. cancel. repeat (progress xform_norm; safecancel).
      eassumption.
      5: reflexivity.
      5: reflexivity.
      5: reflexivity.
      eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe.
      simpl in *.
      rewrite H4 in *.
      repeat rewrite <- surjective_pairing in *.
      eassumption.
      eapply treeseq_safe_pushd_update_subtree; eauto.
      distinct_names'.
      eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
      distinct_inodes.
      eapply treeseq_in_ds_tree_pred_latest in H8 as Hpred.
      rewrite rep_length in Hpred; destruct_lift Hpred.
      rewrite rep_length in H6; destruct_lift H6.
      congruence. 
      unfold dirtree_safe in *.
      repeat rewrite <- surjective_pairing in *.
      rewrite H4 in *; eauto.
      intuition.
      eauto.
      repeat rewrite <- surjective_pairing in *.
      eauto.
      eapply dir2flatmem2_update_subtree; eauto.
      distinct_names'.
  Qed.

  Lemma block_is_unused_xor_belong_to_file : forall F Ftop fsxp t m flag bn inum off,
    tree_rep F Ftop fsxp t m ->
    BFILE.block_is_unused (BFILE.pick_balloc (TSfree t) flag) bn ->
    BFILE.block_belong_to_file (TSilist t) bn inum off ->
    False.
  Proof.
    unfold tree_rep; intros.
    destruct t; simpl in *.
    unfold rep in H; destruct_lift H.
    eapply BFILE.block_is_unused_xor_belong_to_file with (m := m); eauto.
    pred_apply.
    cancel.
  Qed.

  Lemma tree_rep_nth_upd: forall F Ftop fsxp sm mscs ts ds n pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    tree_rep F Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep F Ftop fsxp (treeseq_one_upd (nthd n ts) pathname off v) (list2nmem (nthd n ds) ⟦ bn := v ⟧).
  Proof.
    intros.
    eapply NEforall_d_in in H3 as H3'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_safe in H3'.
    intuition.
    unfold treeseq_one_upd.
    unfold treeseq_safe_bwd in *.
    edestruct H6; eauto.
    - repeat deex.
      rewrite H8.
      unfold tree_rep; simpl.
      unfold tree_rep in H2. destruct_lift H2.
      eapply dirtree_update_block with (bn := bn) (m := (nthd n ds)) (v := v) in H2 as H2'; eauto.
      pred_apply.
      erewrite dirtree_update_inode_update_subtree; eauto.
      cancel.
      eapply rep_tree_inodes_distinct; eauto.
      eapply rep_tree_names_distinct; eauto.
      eapply tree_file_length_ok.
      eapply H2.
      eauto.
      eauto.
    - unfold tree_rep in *. destruct_lift H2.
      eapply dirtree_update_free with (bn := bn) (v := v) in H2 as H2'; eauto.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros; [ destruct d | ]; eauto.
      2: pred_apply; cancel.
      2: pred_apply; cancel.
      rewrite updN_oob.
      erewrite update_subtree_same; eauto.
      unfold tree_rep. pred_apply. cancel.
      eapply rep_tree_names_distinct; eauto.
      destruct d; simpl in *; eauto.

      destruct (lt_dec off (Datatypes.length (DFData d))); try omega.
      exfalso.
      edestruct treeseq_block_belong_to_file; eauto.
      eassign (nthd n ds). unfold tree_rep. pred_apply; cancel.

      unfold treeseq_safe_fwd in H4.
      edestruct H4; eauto; intuition.
      rewrite H11 in H; inversion H; subst.
      eapply block_belong_to_file_bn_eq in H0; [ | apply H12 ].
      subst.
      eapply block_is_unused_xor_belong_to_file; eauto.
      eassign (list2nmem (nthd n ds)). unfold tree_rep. pred_apply; cancel.
  Qed.

  Lemma tree_rep_latest_upd: forall F Ftop fsxp sm mscs ts ds pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    tree_rep_latest F Ftop fsxp sm (ts !!) mscs (list2nmem (ds !!)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep_latest F Ftop fsxp sm (treeseq_one_upd (ts !!) pathname off v) mscs (list2nmem (ds !!) ⟦ bn := v ⟧).
  Proof.
    intros.
    eapply NEforall_d_in in H3 as H3'; [ | apply latest_in_ds ].
    unfold treeseq_safe in H3'.
    intuition.
    unfold treeseq_one_upd.
    unfold treeseq_safe_bwd in *.
    edestruct H6; eauto.
    - repeat deex.
      rewrite H8.
      unfold tree_rep; simpl.
      unfold tree_rep in H2. destruct_lift H2.
      eapply dirtree_update_block with (bn := bn) (m := (ds !!)) (v := v) in H2 as H2'; eauto.
      pred_apply.
      erewrite dirtree_update_inode_update_subtree; eauto.
      eapply rep_tree_inodes_distinct; eauto.
      eapply rep_tree_names_distinct; eauto.
      eapply tree_file_length_ok.
      eapply H2.
      eauto.
      eauto.
    - unfold tree_rep in *. destruct_lift H2.
      eapply dirtree_update_free with (bn := bn) (v := v) in H2 as H2'; eauto.
      case_eq (find_subtree pathname (TStree (ts !!))); intros; [ destruct d | ]; eauto.
      rewrite updN_oob.
      erewrite update_subtree_same; eauto.
      eapply rep_tree_names_distinct; eauto.
      destruct d; simpl in *; eauto.

      destruct (lt_dec off (Datatypes.length (DFData d))); try omega.
      exfalso.
      edestruct treeseq_block_belong_to_file; eauto.
      eassign (ds !!). unfold tree_rep. pred_apply; cancel.

      unfold treeseq_safe_fwd in H4.
      edestruct H4; eauto; intuition.
      rewrite H8 in H; inversion H; subst.
      eapply block_belong_to_file_bn_eq in H0; [ | apply H9 ].
      subst.
      eapply block_is_unused_xor_belong_to_file; eauto.
      eassign (list2nmem (ds !!)). pred_apply. unfold tree_rep, tree_rep_latest. cancel.
  Qed.

  Lemma treeseq_one_upd_alternative : forall t pathname off v,
    treeseq_one_upd t pathname off v =
    mk_tree (match find_subtree pathname (TStree t) with
             | Some (TreeFile inum f) => update_subtree pathname (TreeFile inum (mk_dirfile (updN (DFData f) off v) (DFAttr f))) (TStree t)
             | Some (TreeDir _ _) => TStree t
             | None => TStree t
             end) (TSilist t) (TSfree t).
  Proof.
    intros.
    unfold treeseq_one_upd.
    case_eq (find_subtree pathname (TStree t)); intros.
    destruct d; auto.
    destruct t; auto.
    destruct t; auto.
  Qed.

  Lemma treeseq_one_safe_dsupd_1 : forall tolder tnewest mscs mscs' pathname off v inum f,
    tree_names_distinct (TStree tolder) ->
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (treeseq_one_upd tolder pathname off v) tnewest mscs'.
  Proof.
    unfold treeseq_one_safe; intros.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H2; clear H2 mscs'.
    unfold dirtree_safe in *; intuition.
    destruct (list_eq_dec string_dec pathname0 pathname); subst.
    - edestruct H3; eauto.
      left.
      intuition.
      repeat deex.
      exists pathname'.
      case_eq (find_subtree pathname (TStree tolder)); intros; eauto.
      destruct d; eauto.
      destruct (list_eq_dec string_dec pathname' pathname); subst.
      + erewrite find_update_subtree; eauto.
        rewrite H5 in H7; inversion H7. eauto.
      + rewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
    - edestruct H3; eauto.
      left.
      intuition.
      repeat deex.
      exists pathname'.
      case_eq (find_subtree pathname (TStree tolder)); intros; eauto.
      destruct d; eauto.
      destruct (list_eq_dec string_dec pathname' pathname); subst.
      + erewrite find_update_subtree; eauto.
        rewrite H5 in H7; inversion H7. eauto.
      + rewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
        eapply find_subtree_file_not_pathname_prefix; eauto.
  Qed.

  Lemma treeseq_one_safe_dsupd_2 : forall tolder tnewest mscs mscs' pathname off v inum f,
    tree_names_distinct (TStree tnewest) ->
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe tolder (treeseq_one_upd tnewest pathname off v) mscs'.
  Proof.
    unfold treeseq_one_safe; intros.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H1; simpl.
    rewrite H2; clear H2 mscs'.
    unfold dirtree_safe in *; intuition.
    destruct (list_eq_dec string_dec pathname0 pathname); subst.
    - erewrite find_update_subtree in H0; eauto.
      inversion H0; subst.
      edestruct H2; eauto.
    - rewrite find_subtree_update_subtree_ne_path in H0.
      edestruct H2; eauto.
      eassumption.
      eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
      eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
  Qed.

  Lemma treeseq_one_safe_dsupd : forall tolder tnewest mscs mscs' pathname off v inum f,
    tree_names_distinct (TStree tolder) ->
    tree_names_distinct (TStree tnewest) ->
    treeseq_one_safe tolder tnewest mscs ->
    find_subtree pathname (TStree tnewest) = Some (TreeFile inum f) ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (treeseq_one_upd tolder pathname off v)
      (treeseq_one_upd tnewest pathname off v) mscs'.
  Proof.
    intros.
    eapply treeseq_one_safe_trans.
    eapply treeseq_one_safe_dsupd_1; eauto.
    eapply treeseq_one_safe_dsupd_2; eauto.
    eapply treeseq_one_safe_refl.
  Qed.

  Theorem treeseq_in_ds_upd : forall F Ftop fsxp sm mscs ts ds mscs' pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname  (BFILE.MSAlloc mscs) (ts !!)) ts ->
    MSAlloc mscs = MSAlloc mscs' ->
    (F * rep fsxp Ftop (TStree (tsupd ts pathname off v) !!) (TSilist ts !!) (TSfree ts !!) mscs' sm)%pred
      (list2nmem (dsupd ds bn v) !!) ->
    treeseq_in_ds F Ftop fsxp sm mscs' (tsupd ts pathname off v) (dsupd ds bn v).
  Proof.
    intros.
    unfold treeseq_in_ds in *; intuition.
    unfold tsupd.
    unfold dsupd.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_upd; eauto.
    unfold treeseq_in_ds; intuition eauto.
    rewrite d_map_latest.
    unfold tree_rep in H9. destruct_lift H9.
    eapply treeseq_one_safe_dsupd; eauto.
    eapply rep_tree_names_distinct.
    eapply H1.
    eapply rep_tree_names_distinct.
    eapply H6.

    unfold tsupd in *. rewrite d_map_latest in *.
    unfold dsupd in *. rewrite d_map_latest in *.
    unfold tree_rep_latest.
    unfold treeseq_one_upd at 2.
    unfold treeseq_one_upd at 2.
    destruct (find_subtree pathname (TStree ts !!)); [ destruct d | ]; simpl in *; eauto.
  Qed.

  Theorem treeseq_in_ds_upd' : forall F Ftop fsxp sm mscs ts ds pathname bn off v inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist (ts !!)) bn inum off ->
    treeseq_in_ds F Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname  (BFILE.MSAlloc mscs) (ts !!)) ts ->
    treeseq_in_ds F Ftop fsxp sm mscs (tsupd ts pathname off v) (dsupd ds bn v).
  Proof.
    intros.
    unfold treeseq_in_ds in *; intuition.
    unfold tsupd.
    unfold dsupd.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_upd; eauto.
    unfold treeseq_in_ds; intuition eauto.
    rewrite d_map_latest.
    unfold tree_rep in H7. destruct_lift H7.
    eapply treeseq_one_safe_dsupd; eauto.
    eapply rep_tree_names_distinct.
    eapply H1.
    eapply rep_tree_names_distinct.
    eapply H4.

    unfold tsupd. rewrite d_map_latest.
    unfold dsupd. rewrite d_map_latest.
    eapply tree_rep_latest_upd; eauto.
    unfold treeseq_in_ds; intuition eauto.
  Qed.

  Lemma seq_upd_safe_upd_fwd_ne: forall pathname pathname' inum n ts off v f mscs,
    pathname' <> pathname ->
    tree_names_distinct (TStree (nthd n ts)) ->
    tree_names_distinct (TStree ts !!) ->
     find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_fwd pathname ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname' ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname'
      {|
      TStree := update_subtree pathname
                  (TreeFile inum
                     {|
                     DFData := (DFData f) ⟦ off := v ⟧;
                     DFAttr := DFAttr f |}) (TStree ts !!);
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0
                         {|
                         DFData := (DFData f0) ⟦ off := v ⟧;
                         DFAttr := DFAttr f0 |}) (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
  Proof.
    unfold treeseq_safe_fwd in *; simpl in *; eauto. 
    intros.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    erewrite find_subtree_update_subtree_ne_path; eauto.
    rewrite H7 in H6.
    erewrite find_subtree_update_subtree_ne_path in H6; eauto.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
    rewrite H7 in H6.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
    rewrite H7 in H6.
    deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
    (* directory *)
    rewrite H7 in H6.
    deex.
    {
      destruct (pathname_decide_prefix pathname pathname'). deex. subst.
      +
       edestruct H5.
       eexists.
       intuition eauto.
       intuition.
       destruct suffix. rewrite app_nil_r in *. try congruence.
       erewrite find_subtree_app in H10 by eauto.
       simpl in *. try congruence.

      + erewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_dir_not_pathname_prefix_2; eauto.
    }
    (* None *)
    rewrite H7 in H6.
    deex.
    {
      destruct (pathname_decide_prefix pathname' pathname). deex. subst.
      +  (* pathname' was a directory and now a file. *)
        edestruct H5.
        eexists.
        intuition eauto.
        intuition.
        destruct suffix. rewrite app_nil_r in *. try congruence.
        erewrite find_subtree_app in H2 by eauto.
        simpl in *; congruence.

      + erewrite find_subtree_update_subtree_ne_path; eauto.
        eapply find_subtree_none_not_pathname_prefix_1; eauto.
    }
  Qed.

Lemma seq_upd_safe_upd_bwd_ne: forall pathname pathname' inum n ts off v f mscs,
    pathname' <> pathname ->
    tree_names_distinct (TStree (nthd n ts)) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_fwd pathname ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname' ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs)
      {|
      TStree := update_subtree pathname
                  (TreeFile inum
                     {|
                     DFData := (DFData f) ⟦ off := v ⟧;
                     DFAttr := DFAttr f |}) (TStree ts !!);
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0
                         {|
                         DFData := (DFData f0) ⟦ off := v ⟧;
                         DFAttr := DFAttr f0 |}) (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
  Proof.
    unfold treeseq_safe_bwd in *; simpl; intros.
    deex; intuition.
    destruct (pathname_decide_prefix pathname pathname'). deex.
    destruct suffix. rewrite app_nil_r in *. try congruence.
    erewrite find_subtree_app in H9 by eauto.
    simpl in *; congruence.
    destruct (pathname_decide_prefix pathname' pathname). deex.
    destruct suffix. rewrite app_nil_r in *. try congruence.
    case_eq (find_subtree pathname' (TStree ts!!)); intros.
    destruct d.
    erewrite find_subtree_app in H3 by eauto.
    simpl in *. congruence.

    edestruct find_subtree_update_subtree_oob_general.
    exact H8.
    eassumption.
    intuition.
    rewrite H11 in H13; inversion H13; subst.
    simpl in *. congruence.

    rewrite find_subtree_app_none in H3 by eauto. congruence.
    assert (~ pathname_prefix pathname pathname').
    unfold pathname_prefix.
    intro. deex. eauto.
    assert (~ pathname_prefix pathname' pathname).
    unfold pathname_prefix.
    intro. deex. eauto.
    erewrite find_subtree_update_subtree_ne_path in *; eauto.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    erewrite find_subtree_update_subtree_ne_path; eauto.
    specialize (H7 inum0 off0 bn).
    edestruct H7.
    eexists.
    split; eauto.
    destruct (addr_eq_dec inum inum0).
    ** subst.
      exfalso.
      eapply find_subtree_inode_pathname_unique in H2; eauto.
    ** destruct H15.
      left.
      exists x; eauto.
    ** right; eauto.
    ** 
      specialize (H7 inum0 off0 bn).
      edestruct H7.
      exists f'.
      split; eauto.
      destruct H15.
      intuition.
      left.
      exists x.
      split; eauto.
      right; eauto.
  Qed.

  Lemma treeseq_upd_safe_upd: forall Fm fsxp Ftop mscs mscs' Ftree sm ts ds n pathname pathname' f f' off v inum bn,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum f') (TStree ts !!)) (TSilist ts !!)
         (fst (TSfree ts !!), snd (TSfree ts !!)) mscs' sm)%pred (list2nmem (dsupd ds bn v) !!) ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) -> 
    MSAlloc mscs = MSAlloc mscs' ->
    True ->
    BFILE.block_belong_to_file (TSilist ts !!) bn inum off ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_safe pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_safe pathname' (MSAlloc mscs)
      (treeseq_one_upd ts !! pathname off v)
      (treeseq_one_upd (nthd n ts) pathname off v).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'; eauto.
    repeat rewrite treeseq_one_upd_alternative; simpl.
    rewrite H0' in *; simpl.
    destruct (list_eq_dec string_dec pathname' pathname); subst; simpl in *.
    - unfold treeseq_safe in *.
      intuition.
      + unfold treeseq_safe_fwd in *; intros; simpl in *.
        erewrite find_update_subtree in *; eauto.
        exists {|
             DFData := (DFData f) ⟦ off := v ⟧;
             DFAttr := DFAttr f; |}.
        specialize (H9 inum0 off0 bn0).
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
        destruct d.
        -- rewrite H12 in *; simpl in *.
          erewrite find_update_subtree in *; eauto.
          destruct H10.
          intuition.
          inversion H13; subst. clear H13.
          edestruct H9.
          eexists d.
          split; eauto.
          intuition.
          rewrite H0' in H13.
          inversion H13; subst; eauto.
          edestruct H9.
          eexists d.
          intuition.
          inversion H13; subst; eauto.
          intuition.
        -- (* a directory *)
          rewrite H12 in *; subst; simpl in *.
          exfalso.
          edestruct H10.
          intuition.
          rewrite H12 in H14; inversion H14.
        -- (* None *)
          rewrite H12 in *; subst; simpl in *.
          exfalso.
          edestruct H10.
          intuition.
          rewrite H12 in H14; inversion H14.
      + unfold treeseq_safe_bwd in *. intros; simpl in *.
        erewrite find_update_subtree in *; eauto.
        destruct H10.
        intuition.
        inversion H12.
        subst.
        clear H12.
        case_eq (find_subtree pathname (TStree (nthd n ts))).
        intros.
        destruct d.
        -- (* a file *)
          specialize (H5 inum0 off0 bn0).
          destruct H5.
          eexists f.
          intuition.
 
          destruct H5.
          unfold BFILE.ilist_safe in H11.
          intuition.
          specialize (H14 inum0 off0 bn0).
          destruct H14; auto.

          left.
          eexists.
          split.
          intuition.
          rewrite H10 in H11.
          inversion H11; subst.
          eauto.
          intuition.

          right; eauto.

        -- (* a directory *)
        destruct (BFILE.block_is_unused_dec (BFILE.pick_balloc (TSfree ts!!) (MSAlloc mscs)) bn0).
        ++ right.
          unfold BFILE.ilist_safe in H11; intuition.
          eapply In_incl.
          apply b.
          eauto.
        ++ 
          specialize (H5 inum0 off0 bn0).
          destruct H5.
          eexists.
          split; eauto.
          destruct H5.
          intuition.
          rewrite H10 in H12.
          exfalso; inversion H12.
          right; eauto.

        -- (* None *)
          intros.
          right.
          specialize (H5 inum0 off0 bn0).
          edestruct H5.
          exists f; eauto.
          deex.
          exfalso.
          rewrite H10 in H14; congruence.
          eassumption.
   - (* different pathnames, but pathname' is still safe, if it was safe. *)
     unfold treeseq_safe in *.
     unfold treeseq_pred in H4.
     eapply NEforall_d_in with (x := (nthd n ts)) in H4 as H4'.  
     2: eapply nthd_in_ds.
     unfold tree_rep in H8; destruct_lift H8.
     intuition; simpl.
      *
        eapply seq_upd_safe_upd_fwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H8.
      * 
        eapply seq_upd_safe_upd_bwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H8.
  Qed.

  Theorem treeseq_update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds sm ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> File inum f)%pred  (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ (DFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists ts' f' ds' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
       [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ MSCache mscs' = MSCache mscs ]] *
       [[ MSAllocC mscs' = MSAllocC mscs ]] *
       [[ MSIAllocC mscs' = MSIAllocC mscs ]] *
       [[ (Ftree * pathname |-> File inum f')%pred (dir2flatmem2 (TStree ts' !!)) ]] *
       [[[ (DFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ DFAttr f' = DFAttr f ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm' \/
       exists ds' sm' ts' mscs' bn,
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' sm' hm' *
         [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
         [[ MSAlloc mscs' = MSAlloc mscs ]] *
         [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
         [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds' ]] *
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


    pose proof (list2nmem_array (DFData f)).
    pred_apply.
    erewrite arrayN_except with (i := off).
    cancel.

    eapply list2nmem_inbound; eauto.

    safestep.


    eapply treeseq_in_ds_upd; eauto.

    eapply dir2flatmem2_find_subtree_ptsto.
    distinct_names'.
    eassumption.

    unfold tsupd. rewrite d_map_latest.
    unfold treeseq_one_upd.
    erewrite dir2flatmem2_find_subtree_ptsto; eauto; simpl.
    2: distinct_names'.
    denote! (DFAttr _ = DFAttr _) as Hx; rewrite <- Hx; clear Hx.
    erewrite <- list2nmem_array_updN; eauto.
    destruct f'; eassumption.
    simplen.

    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H4; deex; intuition.
    eapply NEforall_d_in in H7 as H7'; try eassumption.
    unfold tsupd; rewrite d_map_latest.
    unfold treeseq_in_ds in H8.
    eapply d_in_nthd in H6 as H6'; deex.
    eapply NEforall2_d_in  with (x := (nthd n ts)) in H9 as Hd'; eauto.
    intuition.
    eapply treeseq_upd_safe_upd; eauto.
    unfold tree_rep_latest in *; distinct_names.
    unfold tree_rep_latest in *; distinct_inodes.

    unfold tsupd.
    unfold treeseq_one_upd.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.

    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    3: eassumption.

    unfold tsupd.
    erewrite d_map_latest; eauto.
    unfold treeseq_one_upd.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'.
    rewrite H0'; simpl.

    eapply list2nmem_sel in H5 as H5'.
    rewrite <- H5'.

    assert( f' = {|
           DFData := (DFData f) ⟦ off := (v, vsmerge vs) ⟧;
           DFAttr := DFAttr f |}).
    destruct f'.
    f_equal.
    simpl in H15.
    eapply list2nmem_array_updN in H15.
    rewrite H15.
    subst; eauto.
    eapply list2nmem_ptsto_bound in H5 as H5''; eauto.
    eauto.
    eauto.
    rewrite H4.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
    distinct_names'.

    pred_apply.
    rewrite arrayN_ex_frame_pimpl; eauto.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'.
    cancel.

    xcrash_rewrite.
    xcrash_rewrite.
    xform_norm.
    cancel.
    or_r.
    eapply pimpl_exists_r; eexists.
    repeat (xform_deex_r).
    xform_norm; safecancel.
    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    eauto.

    eapply list2nmem_sel in H5 as H5'.
    rewrite H5'; eauto.
    eapply treeseq_in_ds_upd'; eauto.

    eapply dir2flatmem2_find_subtree_ptsto; eauto.
    distinct_names'.

    eassumption.

  Grab Existential Variables.
    all: eauto.
  Qed.

  (* XXX maybe inum should be an argument and the TreeFile case should be split into two cases. *)
  Definition treeseq_one_file_sync (t: treeseq_one) pathname :=
      match find_subtree pathname (TStree t) with
      | None => t
      | Some (TreeFile inum f) => 
        mk_tree (update_subtree pathname (TreeFile inum (synced_dirfile f)) (TStree t)) (TSilist t) (TSfree t)
      | Some (TreeDir _ _) => t
      end.

  Definition ts_file_sync pathname (ts: treeseq) :=
    d_map (fun t => treeseq_one_file_sync t pathname) ts.

  Fixpoint synced_up_to_n n (vsl : list valuset) : list valuset :=
    match n with
    | O => vsl
    | S n' =>
      match vsl with
      | nil => nil
      | vs :: vsl' => (fst vs, nil) :: (synced_up_to_n n' vsl')
      end
    end.

  Theorem synced_list_up_to_n : forall vsl,
    synced_list (map fst vsl) = synced_up_to_n (length vsl) vsl.
  Proof.
    induction vsl; eauto.
    simpl.
    unfold synced_list; simpl.
    f_equal.
    eauto.
  Qed.

  Lemma length_synced_up_to_n : forall n vsl,
    length vsl = length (synced_up_to_n n vsl).
  Proof.
    induction n; simpl; eauto; intros.
    destruct vsl; eauto.
    simpl; eauto.
  Qed.

  Lemma synced_up_to_n_nil : forall n, synced_up_to_n n nil = nil.
  Proof.
    induction n; eauto.
  Qed.

  Lemma synced_up_to_n_too_long : forall vsl n,
    n >= Datatypes.length vsl ->
    synced_up_to_n n vsl = synced_up_to_n (Datatypes.length vsl) vsl.
  Proof.
    induction vsl; simpl; intros; eauto.
    rewrite synced_up_to_n_nil; eauto.
    destruct n; try omega.
    simpl; f_equal.
    eapply IHvsl.
    omega.
  Qed.

  Lemma cons_synced_up_to_n' : forall synclen d l default,
    synclen <= Datatypes.length l ->
    (fst d, []) :: synced_up_to_n synclen l =
    synced_up_to_n synclen (d :: l) ⟦ synclen := (fst (selN (d :: l) synclen default), nil) ⟧.
  Proof.
    induction synclen; simpl; intros; eauto.
    f_equal.
    destruct l; simpl.
    rewrite synced_up_to_n_nil; eauto.
    erewrite IHsynclen; simpl in *; eauto.
    omega.
  Qed.

  Lemma cons_synced_up_to_n : forall synclen d l default,
    (fst d, []) :: synced_up_to_n synclen l =
    synced_up_to_n synclen (d :: l) ⟦ synclen := (fst (selN (d :: l) synclen default), nil) ⟧.
  Proof.
    intros.
    destruct (le_dec synclen (Datatypes.length l)).
    eapply cons_synced_up_to_n'; eauto.
    rewrite updN_oob by (simpl; omega).
    rewrite synced_up_to_n_too_long by omega. rewrite <- synced_list_up_to_n.
    rewrite synced_up_to_n_too_long by (simpl; omega). rewrite <- synced_list_up_to_n.
    firstorder.
  Qed.

  Fixpoint synced_file_alt_helper f off :=
    match off with
    | O => f
    | S off' =>
      let f' := mk_dirfile (updN (DFData f) off' (fst (selN (DFData f) off' ($0, nil)), nil)) (DFAttr f) in
      synced_file_alt_helper f' off'
    end.

  Fixpoint synced_file_alt_helper2 f off {struct off} :=
    match off with
    | O => f
    | S off' =>
      let f' := synced_file_alt_helper2 f off' in
      mk_dirfile (updN (DFData f') off' (fst (selN (DFData f') off' ($0, nil)), nil)) (DFAttr f')
    end.

  Lemma synced_file_alt_helper2_oob : forall off f off' v,
    let f' := synced_file_alt_helper f off in
    off' >= off ->
    (mk_dirfile (updN (DFData f') off' v) (DFAttr f')) =
    synced_file_alt_helper (mk_dirfile (updN (DFData f) off' v) (DFAttr f)) off.
  Proof.
    induction off; simpl; intros; eauto.
    - rewrite IHoff by omega; simpl.
      f_equal.
      f_equal.
      rewrite updN_comm by omega.
      rewrite selN_updN_ne by omega.
      auto.
  Qed.

  Lemma synced_file_alt_helper_selN_oob : forall off f off' default,
    off' >= off ->
    selN (DFData (synced_file_alt_helper f off)) off' default =
    selN (DFData f) off' default.
  Proof.
    induction off; simpl; eauto; intros.
    rewrite IHoff by omega; simpl.
    rewrite selN_updN_ne by omega.
    auto.
  Qed.

  Theorem synced_file_alt_helper_helper2_equiv : forall off f,
    synced_file_alt_helper f off = synced_file_alt_helper2 f off.
  Proof.
    induction off; intros; simpl; auto.
    rewrite <- IHoff; clear IHoff.
    rewrite synced_file_alt_helper2_oob by omega.
    f_equal.
    f_equal.
    rewrite synced_file_alt_helper_selN_oob by omega.
    auto.
  Qed.

  Lemma synced_file_alt_helper2_selN_oob : forall off f off' default,
    off' >= off ->
    selN (DFData (synced_file_alt_helper2 f off)) off' default =
    selN (DFData f) off' default.
  Proof.
    intros.
    rewrite <- synced_file_alt_helper_helper2_equiv.
    eapply synced_file_alt_helper_selN_oob; auto.
  Qed.

  Lemma synced_file_alt_helper2_length : forall off f,
    Datatypes.length (DFData (synced_file_alt_helper2 f off)) = Datatypes.length (DFData f).
  Proof.
    induction off; simpl; intros; auto.
    rewrite length_updN.
    eauto.
  Qed.

  Definition synced_file_alt f :=
    synced_file_alt_helper f (Datatypes.length (DFData f)).

  Theorem synced_file_alt_equiv : forall f,
    synced_dirfile f = synced_file_alt f.
  Proof.
    unfold synced_dirfile, synced_file_alt; intros.
    rewrite synced_list_up_to_n.
    unfold datatype.
    remember (@Datatypes.length valuset (DFData f)) as synclen.
    assert (synclen <= Datatypes.length (DFData f)) by simplen.
    clear Heqsynclen.
    generalize dependent f.
    induction synclen; simpl; intros.
    - destruct f; eauto.
    - rewrite <- IHsynclen; simpl.
      f_equal.
      destruct (DFData f).
      simpl in *; omega.
      eapply cons_synced_up_to_n.
      rewrite length_updN. omega.
  Qed.

  Lemma treeseq_one_upd_noop : forall t pathname off v inum f def,
    tree_names_distinct (TStree t) ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    off < Datatypes.length (DFData f) ->
    selN (DFData f) off def = v ->
    t = treeseq_one_upd t pathname off v.
  Proof.
    unfold treeseq_one_upd; intros.
    rewrite H0.
    destruct t; simpl in *; f_equal.
    rewrite update_subtree_same; eauto.
    rewrite H0.
    f_equal.
    f_equal.
    destruct f; simpl in *.
    f_equal.
    rewrite <- H2.
    rewrite updN_selN_eq; eauto.
  Qed.

  Fixpoint treeseq_one_file_sync_alt_helper (t : treeseq_one) (pathname : list string) off fdata :=
    match off with
    | O => t
    | S off' =>
      let t' := treeseq_one_upd t pathname off' (selN fdata off' $0, nil) in
      treeseq_one_file_sync_alt_helper t' pathname off' fdata
    end.

  Definition treeseq_one_file_sync_alt (t : treeseq_one) (pathname : list string) :=
    match find_subtree pathname (TStree t) with
    | None => t
    | Some (TreeDir _ _) => t
    | Some (TreeFile inum f) =>
      treeseq_one_file_sync_alt_helper t pathname (length (DFData f)) (map fst (DFData f))
    end.

  Lemma treeseq_one_file_sync_alt_equiv : forall t pathname,
    tree_names_distinct (TStree t) ->
    treeseq_one_file_sync t pathname = treeseq_one_file_sync_alt t pathname.
  Proof.
    unfold treeseq_one_file_sync, treeseq_one_file_sync_alt; intros.
    case_eq (find_subtree pathname (TStree t)); eauto.
    destruct d; eauto.
    intros.
    rewrite synced_file_alt_equiv. unfold synced_file_alt.
    remember (@Datatypes.length datatype (DFData d)) as synclen; intros.
    assert (synclen <= Datatypes.length (DFData d)) by simplen.
    clear Heqsynclen.

    remember (map fst (DFData d)) as synced_blocks.
    generalize dependent synced_blocks.
    generalize dependent t.
    generalize dependent d.
    induction synclen; intros.
    - simpl.
      destruct t; destruct d; simpl in *; f_equal.
      eapply update_subtree_same; eauto.
    - simpl.
      erewrite <- IHsynclen.
      f_equal.
      + unfold treeseq_one_upd. rewrite H0; simpl.
        rewrite update_update_subtree_same. reflexivity.
      + unfold treeseq_one_upd. rewrite H0. destruct t; eauto.
      + unfold treeseq_one_upd. rewrite H0. destruct t; eauto.
      + simpl. rewrite length_updN. omega.
      + unfold treeseq_one_upd. rewrite H0. simpl.
        eapply tree_names_distinct_update_subtree.
        eauto. constructor.
      + subst; simpl.
        unfold treeseq_one_upd. rewrite H0; simpl.
        erewrite selN_map.
        erewrite find_update_subtree; eauto.
        unfold datatype in *; omega.
      + subst; simpl.
        rewrite map_updN; simpl.
        erewrite selN_eq_updN_eq; eauto.
        erewrite selN_map; eauto.
  Grab Existential Variables.
    exact $0.
  Qed.

  Lemma treeseq_one_file_sync_alt_equiv_d_map : forall pathname ts,
    NEforall (fun t => tree_names_distinct (TStree t)) ts ->
    d_map (fun t => treeseq_one_file_sync t pathname) ts =
    d_map (fun t => treeseq_one_file_sync_alt t pathname) ts.
  Proof.
    unfold d_map; destruct ts; intros.
    f_equal; simpl.
    - eapply treeseq_one_file_sync_alt_equiv.
      eapply H.
    - eapply map_ext_in; intros.
      eapply treeseq_one_file_sync_alt_equiv.
      destruct H; simpl in *.
      eapply Forall_forall in H1; eauto.
  Qed.

  Theorem dirtree_update_safe_pathname_vssync_vecs_file:
    forall pathname f tree fsxp F F0 ilist freeblocks mscs sm inum m al,
    let tree_newest := update_subtree pathname (TreeFile inum (synced_dirfile f)) tree in
    find_subtree pathname tree = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (forall i, i < length al -> BFILE.block_belong_to_file ilist (selN al i 0) inum i) ->
    (F0 * rep fsxp F tree ilist freeblocks mscs sm)%pred (list2nmem m) ->
    (F0 * rep fsxp F tree_newest ilist freeblocks mscs sm)%pred (list2nmem (vssync_vecs m al)).
  Proof.
    intros.
    subst tree_newest.
    rewrite synced_file_alt_equiv.
    unfold synced_file_alt.
    rewrite synced_file_alt_helper_helper2_equiv.
    rewrite <- H0.
    assert (Datatypes.length al <= Datatypes.length (DFData f)) by omega.
    clear H0.

    induction al using rev_ind; simpl; intros.
    - rewrite update_subtree_same; eauto.
      distinct_names.
    - rewrite vssync_vecs_app.
      unfold vssync.
      erewrite <- update_update_subtree_same.
      eapply pimpl_trans; [ apply pimpl_refl | | ].
      2: eapply dirtree_update_block.
      erewrite dirtree_update_inode_update_subtree.
      rewrite app_length; simpl.
      rewrite plus_comm; simpl.

      rewrite synced_file_alt_helper2_selN_oob by omega.
      replace (selN (vssync_vecs m al) x ($0, nil)) with
              (selN (DFData f) (Datatypes.length al) ($0, nil)).

      reflexivity.

      erewrite <- synced_file_alt_helper2_selN_oob.
      eapply dirtree_rep_used_block_eq.
      eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      erewrite find_update_subtree. reflexivity. eauto.
      {
        specialize (H1 (Datatypes.length al)).
        rewrite selN_last in H1 by omega.
        eapply H1. rewrite app_length. simpl. omega.
      }
      omega.

      3: eapply find_update_subtree; eauto.

      eapply rep_tree_inodes_distinct. eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      eapply rep_tree_names_distinct. eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      {
        rewrite synced_file_alt_helper2_length.
        rewrite app_length in *; simpl in *; omega.
      }

      eapply IHal.
      {
        intros. specialize (H1 i).
        rewrite selN_app1 in H1 by omega.
        eapply H1. rewrite app_length. omega.
      }
      rewrite app_length in *; omega.

      eapply find_update_subtree; eauto.
      specialize (H1 (Datatypes.length al)).
      rewrite selN_last in * by auto.
      eapply H1.
      rewrite app_length; simpl; omega.
  Qed.

  Lemma block_belong_to_file_off_ok : forall Fm Ftop fsxp sm mscs ts t ds inum off pathname f,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    d_in t ts ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    off < Datatypes.length (DFData f) ->
    BFILE.block_belong_to_file
      (TSilist t)
      (wordToNat (selN (INODE.IBlocks (selN (TSilist t) inum INODE.inode0)) off $0))
      inum off.
  Proof.
    intros.
    edestruct d_in_nthd; eauto; subst.
    unfold treeseq_in_ds in H; intuition.
    eapply NEforall2_d_in in H3; try reflexivity; intuition.
    unfold tree_rep in H.
    unfold rep in H.
    destruct_lift H.
    rewrite subtree_extract in H6 by eauto.
    simpl in *.
    destruct_lift H6.
    eapply BFILE.block_belong_to_file_off_ok; eauto.
    eapply pimpl_apply; [ | exact H ]. cancel.
    pred_apply.
    cancel.
    simpl; eauto.
  Qed.

  Lemma block_belong_to_file_bfdata_length : forall Fm Ftop fsxp mscs sm ts ds inum off t pathname f bn,
    treeseq_in_ds Fm Ftop fsxp mscs sm ts ds ->
    d_in t ts ->
    find_subtree pathname (TStree t) = Some (TreeFile inum f) ->
    BFILE.block_belong_to_file (TSilist t) bn inum off ->
    off < Datatypes.length (DFData f).
  Proof.
    intros.
    edestruct d_in_nthd; eauto; subst.
    unfold treeseq_in_ds in H; intuition.
    eapply NEforall2_d_in in H3; try reflexivity; intuition.
    unfold tree_rep in H.
    unfold rep in H.
    destruct_lift H.
    rewrite subtree_extract in H6 by eauto.
    simpl in *.
    destruct_lift H6.
    replace (DFData f) with (BFILE.BFData {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy3 |}) by reflexivity.
    erewrite list2nmem_sel with (x := {|
             BFILE.BFData := DFData f;
             BFILE.BFAttr := DFAttr f;
             BFILE.BFCache := dummy3 |}).
    eapply BFILE.block_belong_to_file_bfdata_length; eauto.
    eapply pimpl_apply; [ | exact H ]; cancel.
    pred_apply; cancel.
  Qed.

  Lemma treeseq_safe_fwd_length : forall Fm Ftop fsxp mscs sm ts ds n inum inum' f b pathname,
    treeseq_in_ds Fm Ftop fsxp mscs sm ts ds ->
    treeseq_safe_fwd pathname (ts !!) (nthd n ts) ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    find_subtree pathname (TStree (nthd n ts)) = Some (TreeFile inum' b) ->
    length (DFData b) <= length (DFData f).
  Proof.
    intros.
    case_eq (length (DFData b)); intros; try omega.
    edestruct H0; intuition.
    eexists; intuition eauto.
    eapply block_belong_to_file_off_ok with (off := n0); eauto; try omega.
    eapply nthd_in_ds.

    eapply Nat.le_succ_l.
    eapply block_belong_to_file_bfdata_length; eauto.
    eapply latest_in_ds.

    rewrite H1 in H5; inversion H5; subst.
    eauto.
  Qed.

  Lemma tree_rep_nth_file_sync: forall Fm Ftop fsxp mscs sm ds ts n al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep Fm Ftop fsxp (treeseq_one_file_sync (nthd n ts) pathname) (list2nmem (vssync_vecs (nthd n ds) al)).
  Proof.
    intros.
    eapply NEforall_d_in in H4 as H4'; [ | apply nthd_in_ds with (n := n) ].
    unfold treeseq_safe in H4'.
    unfold treeseq_one_file_sync.
    intuition.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    destruct d.
    - (* a file *)
      unfold tree_rep; simpl.

      rewrite <- firstn_skipn with (l := al) (n := length (DFData d)).
      remember (skipn (Datatypes.length (DFData d)) al) as al_tail.

      assert (forall i, i < length al_tail -> selN al_tail i 0 = selN al (length (DFData d) + i) 0).
      subst; intros.
      apply skipn_selN.

      assert (length (DFData d) + length al_tail <= length al).
      subst.
      rewrite <- firstn_skipn with (l := al) (n := (length (DFData d))) at 2.
      rewrite app_length.
      eapply Plus.plus_le_compat; try omega.
      rewrite firstn_length.
      rewrite H0.
      rewrite min_l; eauto.
      eapply treeseq_safe_fwd_length; eauto.

      clear Heqal_tail.

      induction al_tail using rev_ind.

      + (* No more tail remaining; all blocks correspond to file [b] *)
        clear H9.
        rewrite app_nil_r.
        unfold tree_rep in H3; destruct_lift H3.
        eexists.
        eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.

        * rewrite firstn_length.
          rewrite Nat.min_l; eauto.

          case_eq (Datatypes.length (DFData d)); intros; try omega.

        * intros.
          rewrite firstn_length in H9.
          apply PeanoNat.Nat.min_glb_lt_iff in H9.
          intuition.

          rewrite selN_firstn by auto.
          edestruct H7.
          eexists; intuition eauto.

          **
            deex.
            rewrite H6 in H13. inversion H13; subst.
            eauto.

          **
            exfalso.
            edestruct H5; intuition.
            eexists; intuition eauto.
            eapply block_belong_to_file_off_ok with (off := i); eauto; try omega.
            eapply nthd_in_ds.

            rewrite H in H14; inversion H14; subst.
            eapply block_belong_to_file_bn_eq in H15.
            2: eapply H1; eauto.
            rewrite H15 in H9.

            eapply block_is_unused_xor_belong_to_file; eauto.
            eassign (list2nmem (nthd n ds)). unfold tree_rep; pred_apply; cancel.
            eapply block_belong_to_file_off_ok; eauto.
            eapply nthd_in_ds.

      + unfold tree_rep in H3; destruct_lift H3.
        rewrite app_assoc. rewrite vssync_vecs_app.
        unfold vssync.
        edestruct IHal_tail.
        shelve. shelve.
        eexists.
        eapply dirtree_update_free.
        eassumption.
        shelve.
        Unshelve.
        intros.
        specialize (H9 i).
        rewrite selN_app1 in H9 by omega. apply H9. rewrite app_length. omega.

        rewrite app_length in *; simpl in *; omega.

        shelve.

        edestruct H7 with (off := length (DFData d) + length al_tail).
        eexists. intuition eauto.
        eapply H1.
        rewrite app_length in *; simpl in *; omega.

        (* [treeseq_safe_bwd] says that the block is present in the old file.  Should be a contradiction. *)
        deex.
        eapply block_belong_to_file_bfdata_length in H14; eauto.
        rewrite H13 in H6; inversion H6; subst. omega.
        eapply nthd_in_ds.

        (* [treeseq_safe_bwd] says the block is unused. *)
        rewrite <- H9 in H12.
        rewrite selN_last in H12 by omega.
        eapply H12.
        rewrite app_length. simpl. omega.

    - (* TreeDir *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      edestruct IHal. shelve. shelve. eexists.
      eapply dirtree_update_free.
      eassumption.
      shelve. Unshelve.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      shelve.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H10; eauto.

    - (* None *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      edestruct IHal. shelve. shelve. eexists.
      eapply dirtree_update_free.
      eassumption.
      shelve. Unshelve.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      shelve.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H10; eauto.
  Qed.

  Lemma tree_rep_latest_file_sync: forall Fm Ftop fsxp mscs sm ds ts al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    tree_rep_latest Fm Ftop fsxp sm (ts !!) mscs (list2nmem (ds !!)) ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    tree_rep_latest Fm Ftop fsxp sm (treeseq_one_file_sync (ts !!) pathname) mscs (list2nmem (vssync_vecs (ds !!) al)).
  Proof.
    intros.
    eapply NEforall_d_in in H4 as H4'; [ | apply latest_in_ds ].
    unfold treeseq_safe in H4'.
    unfold treeseq_one_file_sync.
    intuition.
    case_eq (find_subtree pathname (TStree (ts !!))); intros.
    destruct d.
    - (* a file *)
      unfold tree_rep; simpl.

      rewrite <- firstn_skipn with (l := al) (n := length (DFData d)).
      remember (skipn (Datatypes.length (DFData d)) al) as al_tail.

      assert (forall i, i < length al_tail -> selN al_tail i 0 = selN al (length (DFData d) + i) 0).
      subst; intros.
      apply skipn_selN.

      assert (length (DFData d) + length al_tail <= length al).
      subst.
      rewrite <- firstn_skipn with (l := al) (n := (length (DFData d))) at 2.
      rewrite app_length.
      eapply Plus.plus_le_compat; try omega.
      rewrite firstn_length.
      rewrite H0.
      rewrite min_l; eauto.
      eapply treeseq_safe_fwd_length; eauto.

      rewrite <- latest_nthd; eauto.
      rewrite <- latest_nthd; eauto.

      clear Heqal_tail.

      induction al_tail using rev_ind.

      + (* No more tail remaining; all blocks correspond to file [b] *)
        clear H9.
        rewrite app_nil_r.
        unfold tree_rep in H3; destruct_lift H3.
        eapply dirtree_update_safe_pathname_vssync_vecs_file; eauto.

        * rewrite firstn_length.
          rewrite Nat.min_l; eauto.

          case_eq (Datatypes.length (DFData d)); intros; try omega.

        * intros.
          rewrite firstn_length in H9.
          apply PeanoNat.Nat.min_glb_lt_iff in H9.
          intuition.
          simpl.

          rewrite selN_firstn by auto.
          edestruct H7.
          exists f; intuition eauto.

          **
            deex.
            rewrite H6 in H13. inversion H13; subst.
            eauto.

          **
            exfalso.
            edestruct H5; intuition.
            eexists; intuition eauto.
            eapply block_belong_to_file_off_ok with (off := i); eauto; try omega.
            eapply latest_in_ds.

            rewrite H in H14; inversion H14; subst.
            eapply block_belong_to_file_bn_eq in H15.
            2: eapply H1; eauto.
            rewrite H15 in H9.

            eapply block_is_unused_xor_belong_to_file; eauto.
            eassign (list2nmem (ds !!)). pred_apply. unfold tree_rep, tree_rep_latest. cancel.
            eapply block_belong_to_file_off_ok; eauto.
            eapply latest_in_ds.

      + rewrite app_assoc. rewrite vssync_vecs_app.
        unfold vssync.
        eapply dirtree_update_free.
        eapply IHal_tail.
        intros.
        specialize (H9 i).
        rewrite selN_app1 in H9 by omega. apply H9. rewrite app_length. omega.

        rewrite app_length in *; simpl in *; omega.

        edestruct H7 with (off := length (DFData d) + length al_tail).
        exists f. intuition eauto.
        eapply H1.
        rewrite app_length in *; simpl in *; omega.

        (* [treeseq_safe_bwd] says that the block is present in the old file.  Should be a contradiction. *)
        deex.
        eapply block_belong_to_file_bfdata_length in H13; eauto.
        rewrite H12 in H6; inversion H6; subst. omega.
        eapply latest_in_ds.

        (* [treeseq_safe_bwd] says the block is unused. *)
        rewrite <- H9 in H11.
        rewrite selN_last in H11 by omega.
        eapply H11.
        rewrite app_length. simpl. omega.

    - (* TreeDir *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      eapply dirtree_update_free.
      eapply IHal.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H0; eauto.

    - (* None *)
      assert (length al <= length (DFData f)) by omega.
      clear H0.
      induction al using rev_ind; simpl; eauto.

      rewrite vssync_vecs_app.
      unfold vssync.
      eapply dirtree_update_free.
      eapply IHal.
      intros. specialize (H1 i).
      rewrite selN_app1 in H1 by omega. apply H1. rewrite app_length. omega.
      rewrite app_length in *; simpl in *; omega.

      edestruct H7.
      eexists; intuition eauto.
      eapply H1 with (i := length al); rewrite app_length; simpl; omega.

      deex; congruence.
      rewrite selN_last in H0; eauto.
  Qed.

  Lemma tree_safe_file_sync_1 : forall Fm Ftop fsxp mscs sm ds ts mscs' pathname,
    (exists inum f, find_subtree pathname (TStree ts !!) = Some (TreeFile inum f)) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (ts !!) (treeseq_one_file_sync (ts !!) pathname) mscs'.
  Proof.
    intros.
    rewrite treeseq_one_file_sync_alt_equiv.
    unfold treeseq_one_file_sync_alt.
    inversion H.
    destruct H2.
    rewrite H2.
    remember (Datatypes.length (DFData x0)) as len; clear Heqlen.
    remember (ts !!) as y. rewrite Heqy at 1.

    assert (tree_names_distinct (TStree y)) as Hydistinct.
    rewrite Heqy.
    distinct_names'.

    assert (treeseq_one_safe ts !! y mscs').
    subst; eapply treeseq_one_safe_refl.
    clear Heqy. clear H2.
    generalize dependent y.
    induction len; simpl; intros; eauto.
    eapply IHlen.

    repeat deex.
    do 2 eexists.
    unfold treeseq_one_upd.
    rewrite H; simpl.
    erewrite find_update_subtree; eauto.

    repeat deex.

    unfold treeseq_one_upd.
    rewrite H; simpl.
    eapply tree_names_distinct_update_subtree; eauto.
    constructor.
 
    repeat deex.
    eapply treeseq_one_safe_dsupd_2; eauto.
    distinct_names'.
  Qed.

  Lemma treeseq_in_ds_one_safe : forall Fm Ftop fsxp mscs mscs' sm ts ds n,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    MSAlloc mscs' = MSAlloc mscs ->
    treeseq_one_safe (nthd n ts) ts !! mscs'.
  Proof.
    unfold treeseq_in_ds; intros.
    intuition.
    eapply NEforall2_d_in in H1; intuition.
    unfold treeseq_one_safe.
    rewrite H0.
    eauto.
  Qed.

  Lemma tree_safe_file_sync_2 : forall Fm Ftop fsxp mscs sm ds ts mscs' n pathname,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) (ts !!) mscs'.
  Proof.
    intros.
    rewrite treeseq_one_file_sync_alt_equiv.
    unfold treeseq_one_file_sync_alt.
    case_eq (find_subtree pathname (TStree (nthd n ts))); intros.
    2: eapply treeseq_in_ds_one_safe; eauto.
    destruct d.
    2: eapply treeseq_in_ds_one_safe; eauto.

    remember (Datatypes.length (DFData d)) as len; clear Heqlen.
    remember (nthd n ts) as y.
    assert (treeseq_one_safe y (nthd n ts) mscs').
    subst; eapply treeseq_one_safe_refl.
    remember H1 as H1'. clear HeqH1'. rewrite Heqy in H1'.

    assert (tree_names_distinct (TStree y)) as Hydistinct.
    rewrite Heqy.
    distinct_names'.

    clear Heqy.

    assert (exists b0, find_subtree pathname (TStree y) = Some (TreeFile n0 b0) (* /\ map fst (BFILE.BFData b) = map fst (BFILE.BFData b0) *)).
    eexists; intuition eauto.
    clear H1.

    generalize dependent y.
    induction len; simpl; intros; eauto.

    eapply treeseq_one_safe_trans; eauto.
    eapply treeseq_in_ds_one_safe; eauto.

    eapply IHlen.
    destruct H3; intuition.
    eapply treeseq_one_safe_dsupd_1; eauto.

    destruct H3; intuition.

    unfold treeseq_one_upd.
    rewrite H1; simpl.
    eapply tree_names_distinct_update_subtree; eauto.
    constructor.
 
    destruct H3.
    eexists.
    unfold treeseq_one_upd.
    rewrite H1; simpl.
    erewrite find_update_subtree by eauto. reflexivity.

    distinct_names'.
  Qed.

  Lemma tree_safe_file_sync: forall Fm Ftop fsxp mscs sm ds ts mscs' n al pathname inum f,
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    BFILE.MSAlloc mscs' = BFILE.MSAlloc mscs -> 
    treeseq_one_safe (treeseq_one_file_sync (nthd n ts) pathname) 
     (d_map (fun t : treeseq_one => treeseq_one_file_sync t pathname) ts) !! mscs'.
  Proof.
    intros.
    rewrite d_map_latest.
    eapply treeseq_one_safe_trans.
    eapply tree_safe_file_sync_2; eauto.
    eapply tree_safe_file_sync_1; eauto.
  Qed.

  Lemma treeseq_in_ds_file_sync: forall  Fm Ftop fsxp mscs mscs' sm ds ts al pathname inum  f,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    MSAlloc mscs = MSAlloc mscs' ->
    (Fm * rep fsxp Ftop (TStree (ts_file_sync pathname ts) !!) (TSilist ts !!) (TSfree ts !!) mscs' sm)%pred
        (list2nmem (dssync_vecs ds al) !!) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs' (ts_file_sync pathname ts) (dssync_vecs ds al).
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold ts_file_sync, dssync_vecs.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
    eapply tree_safe_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.

    unfold dssync_vecs in *; rewrite d_map_latest in *.
    unfold ts_file_sync in *; rewrite d_map_latest in *.
    unfold tree_rep_latest.
    unfold treeseq_one_file_sync at 2.
    unfold treeseq_one_file_sync at 2.
    destruct (find_subtree pathname (TStree ts !!)); [ destruct d | ]; simpl in *; eauto.
  Qed.

  Lemma treeseq_in_ds_file_sync' : forall  Fm Ftop fsxp sm mscs ds ts al pathname inum  f,
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    treeseq_pred (treeseq_safe pathname (MSAlloc mscs) ts !!) ts ->
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_in_ds Fm Ftop fsxp sm mscs (ts_file_sync pathname ts) (dssync_vecs ds al).
  Proof.
    unfold treeseq_in_ds.
    intros.
    simpl; intuition.
    unfold ts_file_sync, dssync_vecs.
    eapply NEforall2_d_map; eauto.
    simpl; intros.
    intuition; subst.
    eapply tree_rep_nth_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
    eapply tree_safe_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
    unfold BFILE.mscs_same_except_log in *; intuition eauto.

    unfold dssync_vecs; rewrite d_map_latest.
    unfold ts_file_sync; rewrite d_map_latest.
    eapply tree_rep_latest_file_sync; eauto.
    unfold treeseq_in_ds; intuition eauto.
  Qed.

  Lemma treeseq_one_file_sync_alternative : forall t pathname,
    treeseq_one_file_sync t pathname =
    mk_tree (match find_subtree pathname (TStree t) with
             | Some (TreeFile inum f) => update_subtree pathname (TreeFile inum (synced_dirfile f)) (TStree t)
             | Some (TreeDir _ _) => TStree t
             | None => TStree t
             end) (TSilist t) (TSfree t).
  Proof.
    intros.
    unfold treeseq_one_file_sync.
    case_eq (find_subtree pathname (TStree t)); intros.
    destruct d; auto.
    destruct t; auto.
    destruct t; auto.
  Qed.

  Lemma treeseq_safe_fwd_ne: forall pathname pathname' n ts inum f,
    pathname <> pathname' ->
    tree_names_distinct (TStree ts !!) ->
    tree_names_distinct (TStree (nthd n ts)) -> 
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_fwd pathname ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname' ts !! (nthd n ts) ->
    treeseq_safe_fwd pathname'
      {|
      TStree := match find_subtree pathname (TStree ts !!) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0)) (TStree ts !!)
                | Some (TreeDir _ _) => TStree ts !!
                | None => TStree ts !!
                end;
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0))
                      (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
  Proof.
      unfold treeseq_safe_fwd in *; simpl in *; eauto. 
      intros.
      case_eq (find_subtree pathname (TStree ts!!)); intros.
      destruct d.
      specialize (H4 inum0 off bn).
      edestruct H4.
      case_eq (find_subtree pathname (TStree (nthd n ts))); intros.        
      destruct d0.
      rewrite H7 in H5.
      erewrite find_subtree_update_subtree_ne_path in H5; eauto.
      deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
      deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
      rewrite H7 in H5.
      deex; eauto.
      rewrite H7 in H5.
      deex; eauto.
      intuition.
      erewrite find_subtree_update_subtree_ne_path; eauto.
      deex. eapply find_subtree_file_not_pathname_prefix with (pn1 := pathname) (pn2 := pathname'); eauto.
      deex. eapply find_subtree_file_not_pathname_prefix with (pn1 := pathname') (pn2 := pathname) in H8; eauto.
      rewrite H2 in H6.
      exfalso.
      inversion H6.
      rewrite H2 in H6.
      exfalso.
      inversion H6.
  Qed.

  Lemma treeseq_safe_bwd_ne: forall pathname pathname' ts n inum f mscs,
    pathname <> pathname' ->
    tree_names_distinct (TStree ts !!) ->
    tree_names_distinct (TStree (nthd n ts)) -> 
    find_subtree pathname (TStree ts !!) = Some (TreeFile inum f) ->
    treeseq_safe_bwd pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs) ts !! (nthd n ts) ->
    treeseq_safe_bwd pathname' (MSAlloc mscs)
      {|
      TStree := match find_subtree pathname (TStree ts !!) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0)) (TStree ts !!)
                | Some (TreeDir _ _) => TStree ts !!
                | None => TStree ts !!
                end;
      TSilist := TSilist ts !!;
      TSfree := TSfree ts !! |}
      {|
      TStree := match find_subtree pathname (TStree (nthd n ts)) with
                | Some (TreeFile inum0 f0) =>
                    update_subtree pathname
                      (TreeFile inum0 (synced_dirfile f0))
                      (TStree (nthd n ts))
                | Some (TreeDir _ _) => TStree (nthd n ts)
                | None => TStree (nthd n ts)
                end;
      TSilist := TSilist (nthd n ts);
      TSfree := TSfree (nthd n ts) |}.
  Proof.
        unfold treeseq_safe_bwd in *; simpl in *; eauto.
        intros.
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros.        
        destruct d.
        erewrite find_subtree_update_subtree_ne_path; eauto.
        specialize (H4 inum0 off bn).
        edestruct H4.      
        case_eq (find_subtree pathname (TStree ts!!)); intros.
        destruct d0.
        rewrite H7 in H5.
        deex; eauto.
        erewrite find_subtree_update_subtree_ne_path in H8; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        deex.
        left.
        exists f0; eauto.
        right; eauto.
        rewrite H2 in H5.
        deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        rewrite H2 in H5.
        deex. eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        (* directory *)
        case_eq (find_subtree pathname (TStree ts!!)); intros.
        destruct d.
        rewrite H7 in H5.
        deex.
        erewrite find_subtree_update_subtree_ne_path in H8; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        (* None *)
        case_eq (find_subtree pathname (TStree ts!!)); intros.
        destruct d.
        rewrite H7 in H5.
        deex.
        erewrite find_subtree_update_subtree_ne_path in H8; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_1; eauto.
        eapply find_subtree_update_subtree_file_not_pathname_prefix_2; eauto.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
        rewrite H2 in H7.
        exfalso.
        inversion H7.
  Qed.

  Lemma treeseq_sync_safe_sync: forall Fm fsxp Ftop mscs sm Ftree ts ds n pathname pathname' f inum al,
    (Fm ✶ rep fsxp Ftop (update_subtree pathname (TreeFile inum (synced_dirfile f)) (TStree ts !!))
           (TSilist ts !!) (fst (TSfree ts !!), snd (TSfree ts !!)) mscs sm)%pred
        (list2nmem (dssync_vecs ds al) !!) ->
    (Ftree ✶ pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts !!)) -> 
    Datatypes.length al = Datatypes.length (DFData f) ->
    (length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i) ->
    treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
    treeseq_safe pathname (MSAlloc mscs) ts !! (nthd n ts) ->
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    tree_rep Fm Ftop fsxp (nthd n ts) (list2nmem (nthd n ds)) ->
    treeseq_safe pathname' (MSAlloc mscs) 
      (treeseq_one_file_sync ts !! pathname)
      (treeseq_one_file_sync (nthd n ts) pathname).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as H0'; eauto.
    repeat rewrite treeseq_one_file_sync_alternative; simpl.
    destruct (list_eq_dec string_dec pathname' pathname); subst; simpl in *.
    - unfold treeseq_safe in *.
      intuition.
      + unfold treeseq_safe_fwd in *; intros; simpl in *.
        intuition.
        specialize (H2 inum0 off bn).
        deex.
        case_eq (find_subtree pathname (TStree (nthd n ts))); intros; simpl.
        destruct d.
        -- (* a file *)
          rewrite H10 in H12; simpl.
          erewrite find_update_subtree in H12; eauto.
          inversion H12.
          subst n0; subst f0; clear H12.
          edestruct H2.
          eexists d.
          intuition.
          intuition.
          rewrite H14.
          exists (synced_dirfile x); eauto.
       -- (* a directory *)
          rewrite H10 in H12; simpl.
          exfalso.
          rewrite H10 in H12.
          inversion H12.
       -- (* None *)
          rewrite H10 in H12; simpl.
          exfalso.
          rewrite H10 in H12.
          inversion H12.
      + unfold treeseq_safe_bwd in *; intros; simpl in *.
        destruct H10.
        specialize (H4 inum0 off bn).
        case_eq (find_subtree pathname (TStree ts!!)); intros; simpl.
        destruct d.
        -- (* a file *)
          rewrite H12 in H10; simpl.
          erewrite find_update_subtree in H10; eauto.
          intuition.
          inversion H13.
          subst n0; subst x.
          clear H13.
          edestruct H4.
          eexists d.
          intuition; eauto.
          deex.
          rewrite H13.
          left.
          exists (synced_dirfile f0).
          erewrite find_update_subtree; eauto.
          right; eauto.
        -- (* a directory *)
          rewrite H12 in H10.
          intuition.
          exfalso.
          rewrite H13 in H12.
          inversion H12.
        -- (* None *)
          rewrite H12 in H10.
          intuition.
          exfalso.
          rewrite H13 in H12.
          inversion H12.
    - (* different pathnames, but pathname' is still safe, if it was safe. *)
      unfold treeseq_safe in *.
      unfold treeseq_pred in H3.
      eapply NEforall_d_in with (x := (nthd n ts)) in H3 as H3'.  
      2: eapply nthd_in_ds.
      unfold tree_rep in H7; destruct_lift H7.
      intuition; simpl.
      + 
        eapply treeseq_safe_fwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H7.
      + 
        eapply treeseq_safe_bwd_ne; eauto.
        eapply rep_tree_names_distinct; eapply H7.
  Qed.

  Ltac distinct_inodes' :=
    repeat match goal with
      | [ H: treeseq_in_ds _ _ _ _ ?ts _ |- tree_inodes_distinct (TStree ?ts !!) ] => 
        eapply treeseq_in_ds_tree_pred_latest in H as Hpred;
        eapply rep_tree_inodes_distinct; eapply Hpred
    end.

  Theorem treeseq_file_sync_ok : forall fsxp inum mscs,
    {< ds sm ts Fm Ftop Ftree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe pathname (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> File inum f)%pred (dir2flatmem2 (TStree ts!!)) ]]
    POST:hm' RET:^(mscs')
      exists ds' al,
       let ts' := ts_file_sync pathname ts in
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
         [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
          [[ forall pathname',
             treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
             treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
         [[ ds' = dssync_vecs ds al]] *
         [[ length al = length (DFData f) /\ forall i, i < length al ->
                BFILE.block_belong_to_file (TSilist ts !!) (selN al i 0) inum i ]] *
         [[ MSAlloc mscs = MSAlloc mscs' ]] *
         [[ (Ftree * pathname |-> File inum (synced_dirfile f))%pred (dir2flatmem2 (TStree ts' !!)) ]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm'
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

    unfold ts_file_sync. rewrite d_map_latest.
    unfold treeseq_one_file_sync.
    erewrite dir2flatmem2_find_subtree_ptsto; try eassumption.
    distinct_names'.

    unfold ts_file_sync.
    rewrite d_map_latest.

    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H8; deex; intuition.
    eapply NEforall_d_in in H6 as H6'; try eassumption.
    eapply d_in_nthd in H9 as H9'; deex.

    msalloc_eq.
    eapply treeseq_sync_safe_sync.
    denote dssync_vecs as Hx; exact Hx.
    all: eauto.
    distinct_names.
    distinct_inodes.

    unfold treeseq_in_ds in H7. intuition.
    eapply NEforall2_d_in  with (x := (nthd n ts)) in H as Hd'; eauto.
    intuition.

    unfold ts_file_sync.
    rewrite d_map_latest.
    unfold treeseq_one_file_sync.
    eapply dir2flatmem2_find_subtree_ptsto in H4 as H4'; eauto.
    rewrite H4'; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    distinct_names'.
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
    {< ds sm ts Fm Ftop,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]]
    POST:hm' RET:^(mscs')
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ((ts !!), nil) (ds!!, nil)]]
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm'
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
    unfold treeseq_in_ds in H5; intuition;
      eapply NEforall2_latest in H0; intuition.
    eapply treeseq_one_safe_refl.
    unfold treeseq_in_ds in H5; intuition;
      eapply NEforall2_latest in H0; intuition.
    eapply mscs_parts_eq_tree_rep_latest; eauto.
    unfold treeseq_in_ds in H5; intuition.
  Qed.

  Lemma treeseq_safe_rename: forall pathname' mscs cwd dstnum0 dstents 
    dstbase dstname srcnum0 srcents srcbase srcname dnum tree_elem ts
      frees'_1 frees'_2 ilist' subtree,
    tree_names_distinct (TStree ts!!) ->
    tree_inodes_distinct (TStree ts!!) ->
    find_subtree cwd (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
    find_subtree srcbase (TreeDir dnum tree_elem) = Some (TreeDir srcnum0 srcents) ->
    find_dirlist srcname srcents = Some subtree ->
    find_subtree dstbase
            (tree_prune srcnum0 srcents srcbase srcname (TreeDir dnum tree_elem)) =
          Some (TreeDir dstnum0 dstents) ->
    (forall inum' def', inum' <> srcnum0 -> inum' <> dstnum0 ->
               In inum' (tree_inodes
           (update_subtree cwd
              (tree_graft dstnum0 dstents dstbase dstname subtree
                 (tree_prune srcnum0 srcents srcbase srcname
                    (TreeDir dnum tree_elem))) (TStree ts !!))) ->
               selN (TSilist ts !!) inum' def' = selN ilist' inum' def') ->
    (~pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname') ->
    (~pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname') ->
    dirtree_safe (TSilist ts !!)
            (BFILE.pick_balloc (fst (TSfree ts !!), snd (TSfree ts !!))
               (MSAlloc mscs)) (TStree ts !!) ilist'
            (BFILE.pick_balloc (frees'_1, frees'_2) (MSAlloc mscs))
            (update_subtree cwd
               (tree_graft dstnum0 dstents dstbase dstname subtree
                  (tree_prune srcnum0 srcents srcbase srcname
                     (TreeDir dnum tree_elem))) (TStree ts !!)) ->
    treeseq_safe pathname' (MSAlloc mscs)
      {|
      TStree := update_subtree cwd
                  (tree_graft dstnum0 dstents dstbase dstname subtree
                     (tree_prune srcnum0 srcents srcbase srcname
                        (TreeDir dnum tree_elem))) (TStree ts !!);
      TSilist := ilist';
      TSfree := (frees'_1, frees'_2) |} ts !!.
  Proof.
    unfold treeseq_safe; intuition.

    - unfold treeseq_safe_fwd.
      intros; simpl.
      deex.
      exists f; eauto.
      intuition.
      eapply find_rename_oob; eauto.

      unfold BFILE.block_belong_to_file in *.
      rewrite H5 in *; eauto.

      intro. subst.

      erewrite <- find_subtree_app in H2 by eassumption.
      assert (pathname' = cwd ++ srcbase).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.

      intro. subst.
      eapply find_subtree_before_prune in H4.
      deex.
      erewrite <- find_subtree_app in H4 by eassumption.
      assert (pathname' = cwd ++ dstbase).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.
      eapply find_subtree_tree_names_distinct; eauto.
      eauto.

      eapply tree_inodes_in_rename_oob; eauto.

    - unfold treeseq_safe_bwd in *.
      intros.
      left.
      repeat deex; intuition.
      denote pathname' as Hp.
      eexists f'; intuition; simpl in *.
      eapply find_rename_oob'. 7: eauto.
      all: auto.
      unfold BFILE.block_belong_to_file in *.
      rewrite H5 in *; eauto.
      -- intro. subst.
        destruct (pathname_decide_prefix cwd pathname').
        + deex.
          erewrite find_subtree_app in Hp by eauto.
          eapply find_subtree_graft_subtree_oob' in Hp.
          2: eauto.
          eapply find_subtree_prune_subtree_oob' in Hp.
          2: eauto.
          assert (srcbase = suffix).
          eapply find_subtree_inode_pathname_unique with (tree := (TreeDir dnum tree_elem)); eauto.
          eapply find_subtree_tree_inodes_distinct; eauto.
          eapply find_subtree_tree_names_distinct; eauto.
          congruence.
          intro; apply H6.  apply pathname_prefix_trim; eauto.
          intro; apply H7.  apply pathname_prefix_trim; eauto.
        + 
          eapply find_subtree_update_subtree_oob' in Hp.
          assert (cwd++srcbase = pathname').

          erewrite <- find_subtree_app in H2 by eauto.
          eapply find_subtree_inode_pathname_unique; eauto.
          contradiction H9; eauto.
          eauto.
      -- intro. subst.
       destruct (pathname_decide_prefix cwd pathname').
        + deex.
          erewrite find_subtree_app in Hp by eauto.
          eapply find_subtree_graft_subtree_oob' in Hp.
          2: eauto.
          eapply find_subtree_prune_subtree_oob' in Hp.
          2: eauto.
          eapply find_subtree_before_prune in H4; eauto.
          deex.
          assert (dstbase = suffix).
          eapply find_subtree_inode_pathname_unique with (tree := (TreeDir dnum tree_elem)); eauto.
          eapply find_subtree_tree_inodes_distinct; eauto.
          eapply find_subtree_tree_names_distinct; eauto.
          congruence.
          eapply find_subtree_tree_names_distinct; eauto.
          intro; apply H6.  apply pathname_prefix_trim; eauto.
          intro; apply H7.  apply pathname_prefix_trim; eauto.
        + 
          eapply find_subtree_update_subtree_oob' in Hp.
          eapply find_subtree_before_prune in H4; eauto.
          deex.
          assert (cwd++dstbase = pathname').
          erewrite <- find_subtree_app in H4 by eauto.
          eapply find_subtree_inode_pathname_unique; eauto.
          contradiction H9; eauto.
          eapply find_subtree_tree_names_distinct; eauto.
          eauto.
      --
        replace inum with (dirtree_inum (TreeFile inum f')) by reflexivity.
        eapply find_subtree_inum_present; eauto.
    - simpl.
      unfold dirtree_safe in *; intuition.
  Qed.


  Theorem treeseq_rename_ok : forall fsxp dnum srcbase (srcname:string) dstbase dstname mscs,
    {< ds sm ts Fm Ftop Ftree cwd tree_elem srcnum dstnum srcfile dstfile,
    PRE:hm
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ find_subtree cwd (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
      [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> File srcnum srcfile
                * (cwd ++ dstbase ++ [dstname]) |-> File dstnum dstfile)%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
       [[ ok = OK tt ]] * exists d ds' ts' ilist' frees' tree',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
       [[ forall pathname',
           ~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname' ->
           ~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = (pushd d ds) ]] *
       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
       [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
       [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Nothing
                 * (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm' \/
       exists d ds' ts' ilist' frees' tree' mscs',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' sm hm' *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
       [[ forall pathname',
           ~ pathname_prefix (cwd ++ srcbase ++ [srcname]) pathname' ->
           ~ pathname_prefix (cwd ++ dstbase ++ [dstname]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
       [[ ds' = (pushd d ds) ]] *
       [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
       [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
       [[ (Ftree * (cwd ++ srcbase ++ [srcname]) |-> Nothing
                 * (cwd ++ dstbase ++ [dstname]) |-> File srcnum srcfile)%pred (dir2flatmem2 (TStree ts' !!)) ]]
   >} AFS.rename fsxp dnum srcbase srcname dstbase dstname mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.rename_ok.
    cancel. 
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eassumption.
    step.

    or_l. cancel. eapply treeseq_in_ds_mscs'; eauto.

    unfold AFS.rename_rep, AFS.rename_rep_inner.
    cancel.
    or_r.

    (* a few obligations need subtree *)
    eapply sep_star_split_l in H4 as H4'.
    destruct H4'.
    eapply dir2flatmem2_find_subtree_ptsto in H8.
    erewrite find_subtree_app in H8.
    2: eassumption.
    erewrite find_subtree_app in H8.
    2: eassumption.
    2: distinct_names'.

    cancel.

    - eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe; simpl.
      rewrite H in H11.
      eassumption.

    - eapply treeseq_safe_pushd; eauto.
      eapply NEforall_d_in'; intros.
      eapply NEforall_d_in in H13; eauto.
      eapply treeseq_safe_trans; eauto.

      (* clear all goals mentioning x0 *)
      clear H13 H15 x0.

      eapply treeseq_safe_rename; eauto.
      distinct_names'.
      distinct_inodes'.
      rewrite H in *; eauto.

    - eapply dir2flatmem2_rename; eauto.
      distinct_names'.
      distinct_inodes'.

    - unfold AFS.rename_rep_inner in *.
      xcrash_solve.
      or_l. cancel. xform_normr. cancel.
      or_r. cancel. repeat (progress xform_norm; safecancel).

      eassumption.
      3: reflexivity.
      4: reflexivity.
      3: pred_apply; cancel.

      + eapply treeseq_in_ds_pushd; eauto.
        unfold treeseq_one_safe; simpl.
        rewrite <- surjective_pairing in H11.
        rewrite H0 in H11.
        eassumption.

      + eapply treeseq_safe_pushd; eauto.
        eapply NEforall_d_in'; intros.
        eapply NEforall_d_in in H22; eauto.
        eapply treeseq_safe_trans; eauto.

        eapply treeseq_safe_rename; eauto.
        distinct_names'.
        distinct_inodes'.
        rewrite H0 in *; eauto.

      + eapply dir2flatmem2_rename; eauto.
        distinct_names'.
        distinct_inodes'.
  Qed.

  Lemma treeseq_safe_delete: forall pathname' pathname name dnum tree_elem ts ilist' mscs 
    frees'_1 frees'_2 Ftree file finum,
    tree_names_distinct (TStree ts !!) ->
    tree_inodes_distinct (TStree ts !!) ->
    (Ftree ✶ (pathname ++ [name]) |-> File finum file)%pred(dir2flatmem2 (TStree ts !!)) ->
    find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ->
    (forall inum def',
        (inum = dnum -> False) ->
        In inum (tree_inodes (TStree ts !!)) ->
        In inum
          (tree_inodes
             (update_subtree pathname
                (TreeDir dnum (delete_from_list name tree_elem)) (TStree ts !!))) ->
        selN (TSilist ts !!) inum def' = selN ilist' inum def')  ->
     dirtree_safe (TSilist ts !!)
          (BFILE.pick_balloc (fst (TSfree ts !!), snd (TSfree ts !!))
             (MSAlloc mscs)) (TStree ts !!) ilist'
          (BFILE.pick_balloc (frees'_1, frees'_2) (MSAlloc mscs))
          (update_subtree pathname
             (TreeDir dnum (delete_from_list name tree_elem)) (TStree ts !!)) ->
     (~pathname_prefix (pathname ++ [name]) pathname') -> 
     treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) ts !!) ts ->
     treeseq_pred
        (treeseq_safe pathname' (MSAlloc mscs)
           (pushd
              {|
              TStree := update_subtree pathname
                          (TreeDir dnum (delete_from_list name tree_elem))
                          (TStree ts !!);
              TSilist := ilist';
              TSfree := (frees'_1, frees'_2) |} ts) !!)
        (pushd
           {|
           TStree := update_subtree pathname
                       (TreeDir dnum (delete_from_list name tree_elem))
                       (TStree ts !!);
           TSilist := ilist';
           TSfree := (frees'_1, frees'_2) |} ts).
  Proof.
    intros.
    eapply treeseq_safe_pushd; eauto.
    eapply NEforall_d_in'; intros.
    eapply NEforall_d_in in H6; eauto.
    eapply treeseq_safe_trans; eauto.
    unfold treeseq_safe; intuition.
    - unfold treeseq_safe_fwd.
      intros; simpl.
      deex.
      exists f; eauto.
      intuition.

      eapply find_subtree_prune_subtree_oob in H9; eauto.

      unfold BFILE.block_belong_to_file in *.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique; eauto.
      congruence.

      replace inum with (dirtree_inum (TreeFile inum f)) by reflexivity.
      eapply find_subtree_inum_present; eauto.

      eapply tree_inodes_in_delete_oob; eauto.

    - unfold treeseq_safe_bwd.
      intros.
      left.
      deex.
      eexists f'; intuition; simpl in *.
      eapply find_subtree_prune_subtree_oob' in H9; eauto. 

      unfold BFILE.block_belong_to_file in *.
      rewrite H3 in *; eauto.
      intros; subst.
      assert (pathname' = pathname).
      eapply find_subtree_inode_pathname_unique with (tree := 
        (update_subtree pathname 
                    (TreeDir dnum 
                     (delete_from_list name tree_elem)) (TStree ts !!))); eauto.

      destruct (TStree ts !!).

      eapply find_subtree_file_dir_exfalso in H2.
      exfalso; eauto.
      eapply tree_inodes_distinct_prune; eauto.
      eapply tree_names_distinct_prune_subtree'; eauto.
      subst.
      erewrite find_update_subtree in H9; eauto.
      congruence.

      apply find_subtree_inum_present in H9; simpl in H9.
      eapply In_incl; eauto.
      eapply incl_appr'.
      eapply incl_count_incl.
      eapply permutation_incl_count.
      eapply tree_inodes_after_prune'; eauto.

      erewrite <- find_subtree_dirlist.
      erewrite <- find_subtree_app with (p0 := pathname); eauto.
      eapply dir2flatmem2_find_subtree_ptsto with (tree := TStree ts !!).
      eauto.
      pred_apply; cancel.

      replace inum with (dirtree_inum (TreeFile inum f')) by reflexivity.
      eapply find_subtree_inum_present; eauto.

    - simpl.
      unfold dirtree_safe in *; intuition.
  Qed.

  (* restricted to deleting files *)
  Theorem treeseq_delete_ok : forall fsxp dnum name mscs,
    {< ds sm ts pathname Fm Ftop Ftree tree_elem finum file,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ find_subtree pathname (TStree ts !!) = Some (TreeDir dnum tree_elem) ]] *
      [[ (Ftree * ((pathname++[name])%list) |-> File finum file)%pred (dir2flatmem2 (TStree ts !!)) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ isError ok ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') sm hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts ds ]] \/
       [[ ok = OK tt ]] * exists d ds' ts' tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm hm' *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           ~ pathname_prefix (pathname ++ [name]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
        [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name]) |-> Nothing)%pred (dir2flatmem2 (TStree ts' !!)) ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds sm hm' \/
      exists d ds' ts' mscs' tree' ilist' frees',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' sm hm' *
        [[ MSAlloc mscs' = MSAlloc mscs ]] *
        [[ treeseq_in_ds Fm Ftop fsxp sm mscs' ts' ds']] *
        [[ forall pathname',
           ~ pathname_prefix (pathname ++ [name]) pathname' ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts !!)) ts ->
           treeseq_pred (treeseq_safe pathname' (MSAlloc mscs) (ts' !!)) ts' ]] *
        [[ ds' = pushd d ds ]] *
        [[[ d ::: (Fm * rep fsxp Ftop tree' ilist' frees' mscs' sm) ]]] *
        [[ tree' = update_subtree pathname
                      (delete_from_dir name (TreeDir dnum tree_elem)) (TStree ts !!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' frees') ts) ]] *
        [[ (Ftree * (pathname ++ [name]) |-> Nothing)%pred (dir2flatmem2 (TStree ts' !!)) ]]

    >} AFS.delete fsxp dnum name mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.delete_ok.
    cancel.
    eapply treeseq_in_ds_tree_pred_latest in H7 as Hpred; eauto.
    eassumption.
    step.
    or_l. cancel.
    eapply treeseq_in_ds_mscs'; eauto.
    or_r. cancel.

    - eapply treeseq_in_ds_pushd; eauto.
      unfold treeseq_one_safe; simpl.
      rewrite H in H13.
      eassumption.

    - eapply treeseq_safe_delete; eauto.
      distinct_names'.
      distinct_inodes'.
      rewrite H in *.
      eauto.

    - eapply dir2flatmem2_delete_file; eauto; distinct_names'.

    - xcrash_solve.
      or_l. cancel. xform_normr. cancel.
      or_r. cancel. repeat (progress xform_norm; safecancel).
      eassumption.
      3: reflexivity.
      4: reflexivity.
      4: reflexivity.
      3: pred_apply; cancel.
      clear H1. clear H2. clear H.

      + eapply treeseq_in_ds_pushd; eauto.
        unfold treeseq_one_safe; simpl.
        rewrite <- surjective_pairing in H11.
        rewrite H5 in *; eauto.

      + eapply treeseq_safe_delete; eauto.
        distinct_names'.
        distinct_inodes'.
        rewrite H5 in *; eauto.

      + eapply dir2flatmem2_delete_file; eauto; distinct_names'.
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

