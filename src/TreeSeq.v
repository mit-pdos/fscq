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


Import DIRTREE.
Import ListNotations.


Module TREESEQ.

  (* a layer over AFS that provides the same functions but with treeseq and dirsep specs *)

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

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
    (forall i, i < List.length al -> BFILE.block_belong_to_file (TSilist (latest ts)) (selN al i 0) inum i) ->
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

    (* lift from DirUtil: edestruct dirtree_update_safe_pathname_vssync_vecs. *)
  Admitted.


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
     find_subtree pathname (TStree tolder) = Some (TreeFile inum' f') /\ off < List.length (BFILE.BFData f')
     )
    \/
    (exists f',
     find_subtree pathname (TStree tolder) = Some (TreeFile inum f') /\
     BFILE.block_belong_to_file (TSilist tolder) bn inum off).


  Lemma update_subtree_same: forall pn tree subtree,
    tree_names_distinct tree ->
    find_subtree pn tree = Some subtree ->
    update_subtree pn subtree tree = tree.
  Proof.
    induction pn; simpl; intros.
    - inversion H0; reflexivity.
    - destruct tree; eauto.
      f_equal.
      induction l.
      + simpl; eauto.
      + erewrite map_cons.
        unfold update_subtree_helper at 1.
        destruct a0.
        destruct (string_dec s a).
        rewrite IHpn.
        erewrite update_subtree_notfound; eauto.
        admit.
        admit.
        admit.
        f_equal.
        rewrite IHl; eauto.
        admit. (* follows from H0. *)
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
    destruct (lt_dec off (List.length (BFILE.BFData b))).
    exfalso; eauto.

    (* off out of bounds *)
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
    destruct (lt_dec off (List.length (BFILE.BFData b))).

    (* cannot be in-range *)
    exfalso; eauto.

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

  Theorem treeseq_file_getattr_ok : forall fsxp inum mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ (Ftree * pathname |-> (inum, f))%pred  (dir2flatmem [] (TStree ts!!)) ]] 
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
    unfold treeseq_in_ds in H6.
    intuition.
    unfold tree_rep in H.
    eassumption.
    eapply dir2flatmem_find_subtree_ptsto.
    unfold treeseq_in_ds in H6.
    intuition.
    unfold tree_rep in H.
    distinct_names.
    eassumption.
  Qed.

 Theorem treeseq_read_fblock_ok : forall fsxp inum off mscs,
    {< ds ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ (Ftree * pathname |-> (inum, f))%pred  (dir2flatmem [] (TStree ts!!)) ]] *
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
    unfold treeseq_in_ds in H7.
    intuition.
    unfold tree_rep in H.
    eassumption.
    eapply dir2flatmem_find_subtree_ptsto.
    unfold treeseq_in_ds in H7.
    intuition.
    unfold tree_rep in H.
    distinct_names.
    eassumption.
    eassumption.
  Qed.

  Theorem treeseq_file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds ts pathname Fm Ftop Ftree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
     [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
     [[ (Ftree * pathname |-> (inum, f))%pred  (dir2flatmem [] (TStree ts!!)) ]] 
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = true  ]] * exists ds' ts' mscs' tree' f' ilist',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') (TStree ts!!) ]] *
        [[ ts' = (pushd (mk_tree tree' ilist' (TSfree ts !!)) ts) ]] *
        [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
        [[ (Ftree * pathname |-> (inum, f'))%pred (dir2flatmem [] tree') ]])
  XCRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} AFS.file_set_attr fsxp inum attr mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.file_set_attr_ok.
    cancel.
    unfold treeseq_in_ds in H6.
    intuition.
    unfold tree_rep in H.
    eassumption.
    eapply dir2flatmem_find_subtree_ptsto.
    unfold treeseq_in_ds in H6.
    intuition.
    unfold tree_rep in H.
    distinct_names.
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
    eapply dir2flatmem_update_subtree.
    unfold treeseq_in_ds in H6.
    intuition.
    unfold tree_rep in H5.
    distinct_names.
    eassumption.
  Qed.

  (* A less general version of AFS.update_fblock_d, but easier to use for applications.
   * This version puts additional constraints on the trees in the treeseq.
   *)
  Theorem treeseq_update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds ts Fm Ftop Ftree pathname f Fd vs,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * pathname |-> (inum, f))%pred  (dir2flatmem [] (TStree ts!!)) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists ts' f' ds',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds']] *
       [[ ts' = tsupd ts pathname off (v, vsmerge vs) ]] *
       [[ treeseq_pred (treeseq_upd_safe pathname off (MSAlloc mscs') (ts' !!)) ts' ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       [[ (Ftree * pathname |-> (inum, f'))%pred (dir2flatmem []  (TStree ts' !!)) ]] *
       [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    XCRASH:hm'
      (* XXX update to use treeseq *)
(*
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       exists bn ilist, [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (dsupd ds bn (v, vsmerge vs)) hm'
*)
      any
   >} AFS.update_fblock_d fsxp inum off v mscs.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply AFS.update_fblock_d_ok.
    cancel.

    unfold treeseq_in_ds, tree_rep in H8.
    eapply NEforall2_d_in in H8.
    intuition eauto.
    eauto.
    rewrite nthd_oob; eauto.

    eapply dir2flatmem_find_subtree_ptsto.
    2: rewrite nthd_oob; eauto.
    2: admit.
    admit.

    eauto.

    step.
    eapply treeseq_in_ds_upd; eauto.
    eapply dir2flatmem_find_subtree_ptsto.
    admit.
    eauto.
    rewrite nthd_oob in H18; eauto.
    admit.

    unfold BFILE.diskset_was in H20.
    intuition.
    subst; eauto.
    (* should be impossible once haogang gets rid of [diskset_was] *)
    admit.

Lemma NEforall_d_in':
  forall T (p : T -> Prop) l, (forall x, d_in x l -> p x) -> NEforall p l.
Admitted.

    eapply NEforall_d_in'; intros.
    apply d_in_d_map in H4; deex; intuition.
    eapply NEforall_d_in in H7; try eassumption.
    unfold tsupd; rewrite d_map_latest.

    unfold treeseq_one_upd at 1.
    erewrite dir2flatmem_find_subtree_ptsto.
    3: eauto.

    case_eq (DIRTREE.find_subtree pathname (TStree d')); intros; subst;
    [ destruct d; [ destruct (lt_dec off (Datatypes.length (BFILE.BFData b))) | ] | ];
    unfold treeseq_one_upd; rewrite H4; simpl;
    unfold treeseq_upd_safe in *; simpl in *; intros.

    (* XXX *)
    

    unfold treeseq_upd_safe in *.

    unfold treeseq_pred.
    unfold tsupd.

    admit.  (* by assumption *)
    admit.  (* bn0 = bn? *)
    admit.  (* XXX need a lemma about tsupd. *)
    admit.

    xcrash.
    or_r.
    eapply pimpl_exists_r; eexists.
    repeat (xform_deex_r).
    xform_norm; cancel.
    eassumption.
  Admitted.

  Hint Extern 1 ({{_}} Bind (AFS.file_get_attr _ _ _) _) => apply treeseq_file_getattr_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.read_fblock _ _ _ _) _) => apply treeseq_read_fblock_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.file_set_attr _ _ _ _) _) => apply treeseq_file_set_attr_ok : prog.
  Hint Extern 1 ({{_}} Bind (AFS.update_fblock_d _ _ _ _ _) _) => apply treeseq_update_fblock_d_ok : prog.

End TREESEQ.

