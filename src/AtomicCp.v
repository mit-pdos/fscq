Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
Require Import Hashmap.   (* must go before basicprog, because notation using hashmap *)
Require Import BasicProg.
Require Import Bool.
Require Import Pred PredCrash.
Require Import DirName.
Require Import Hoare.
Require Import GenSepN.
Require Import ListPred.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List ListUtils.
Require Import Balloc.
Require Import Bytes.
Require Import DirTree.
Require Import Rec.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Errno.
Require Import AsyncDisk.
Require Import GroupLog.
Require Import SuperBlock.
Require Import DiskSet.
Require Import AsyncFS.
Require Import String.
Require Import DirTreeDef.
Require Import DirTreeRep.
Require Import DirTreeNames.
Require Import DirTreeSafe.
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.

Import TREESEQ.
Import DTCrash.
Import ListNotations.

Set Implicit Arguments.

(**
 * Atomic copy: create a copy of file [src_fn] in the root directory [the_dnum],
 * with the new file name [dst_fn].
 *
 *)


Module ATOMICCP.

  Parameter the_dnum : addr.
  Parameter cachesize : nat.
  Axiom cachesize_ok : cachesize <> 0.
  Hint Resolve cachesize_ok.


  Definition temp_fn := ".temp"%string.
  Definition Off0 := 0.
  
  (** Programs **)

  (* copy an existing src into an existing, empty dst. *)

  Definition copydata fsxp src_inum tinum mscs :=
    let^ (mscs, attr) <- AFS.file_get_attr fsxp src_inum mscs;
    let^ (mscs, b) <- AFS.read_fblock fsxp src_inum Off0 mscs;
    let^ (mscs) <- AFS.update_fblock_d fsxp tinum Off0 b mscs;
    let^ (mscs) <- AFS.file_sync fsxp tinum mscs;   (* sync blocks *)
    let^ (mscs, ok) <- AFS.file_set_attr fsxp tinum attr mscs;
    Ret ^(mscs, ok).


  Definition copy2temp fsxp src_inum tinum mscs :=
    let^ (mscs, ok) <- AFS.file_truncate fsxp tinum 1 mscs;  (* XXX type error when passing sz *)
    match ok with
    | Err e =>
      Ret ^(mscs, false)
    | OK _ =>
      let^ (mscs, ok) <- copydata fsxp src_inum tinum mscs;
      match ok with
      | Err _ => Ret ^(mscs, false)
      | OK _ => Ret ^(mscs, true)
      end
    end.


  Definition copy_and_rename fsxp src_inum tinum (dstbase:list string) (dstname:string) mscs :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum tinum mscs;
    match ok with
      | false =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        (* Just for a simpler spec: the state is always (d, nil) after this function *)
        Ret ^(mscs, false)
      | true =>
        let^ (mscs, r) <- AFS.rename fsxp the_dnum [] temp_fn dstbase dstname mscs;
        match r with
        | OK _ =>
          let^ (mscs) <- AFS.tree_sync fsxp mscs;
          Ret ^(mscs, true)
        | Err e =>
          let^ (mscs) <- AFS.tree_sync fsxp mscs;
          Ret ^(mscs, false)
        end
    end.

  Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, r) <- AFS.create fsxp the_dnum temp_fn mscs;
    match r with
      | Err _ => Ret ^(mscs, false)
      | OK tinum =>
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.

  (** recovery programs **)

  (* top-level recovery function: call AFS recover and then atomic_cp's recovery *)
  Definition atomic_cp_recover :=
    recover_res <- AFS.recover cachesize;
    match recover_res with
    | Err e => Ret (Err e)
    | OK (mscs, fsxp) =>
      let^ (mscs, r) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
      match r with
      | Err _ => Ret (OK (mscs, fsxp))
      | OK (src_inum, isdir) =>
        let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        Ret (OK (mscs, fsxp))
      end
    end.

  (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.

  Definition tree_with_src Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname dstfile:  @pred _ (list_eq_dec string_dec) _ :=
        (exists dstinum,
         Ftree * nil |-> Dir the_dnum * srcpath |-> File srcinum file * tmppath |-> Nothing * 
                (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_tmp Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum tfile dstbase dstname dstfile:  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum * srcpath |-> File srcinum file * tmppath |-> File tinum tfile *
         (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_dst Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname :  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum * srcpath |-> File srcinum file * tmppath |-> Nothing *
         (dstbase ++ [dstname])%list |-> File dstinum (synced_dirfile file))%pred.

  Definition tree_rep Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum dstbase dstname dstfile t := 
    (tree_names_distinct (TStree t)) /\
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree t))))%type.

  Lemma dirents2mem2_treeseq_one_upd_tmp : forall (F: @pred _ (@list_eq_dec string string_dec) _) tree tmppath inum f off v,
    let f' := {|
             DFData := (DFData f) ⟦ off := v ⟧;
             DFAttr := DFAttr f |} in
    tree_names_distinct (TStree tree) ->
    (F * tmppath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * tmppath |-> File inum f')%pred (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as Hfind; eauto.
    unfold treeseq_one_upd.
    destruct (find_subtree tmppath (TStree tree)).
    destruct d.
    inversion Hfind; subst; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    inversion Hfind.
    inversion Hfind.
  Qed.

  Lemma treeseq_one_upd_tree_rep_tmp: forall tree Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile off v,
   let tfile' := {|
             DFData := (DFData tfile) ⟦ off := v ⟧;
             DFAttr := DFAttr tfile |} in
    tree_names_distinct (TStree tree) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    unfold tree_with_tmp in *.
    destruct_lift H0. eexists.
    eapply sep_star_comm.
    eapply sep_star_assoc.
    eapply dirents2mem2_treeseq_one_upd_tmp; eauto.
    pred_apply.
    cancel.
  Qed.

  Lemma dirents2mem2_treeseq_one_upd_src : forall (F: @pred _ (@list_eq_dec string string_dec) _) F1 tree tmppath srcpath inum f off v,
    tree_names_distinct (TStree tree) ->
    (F1 * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H1 as Hfind; eauto.
    eapply dir2flatmem2_find_subtree_ptsto_none in H0 as Hfindtmp; eauto.
    unfold treeseq_one_upd.
    intuition.
    destruct (find_subtree tmppath (TStree tree)).
    congruence.
    eassumption.
  Qed.

  Lemma treeseq_one_upd_tree_rep_src: forall tree Ftree srcpath tmppath src_inum file dstbase dstname dstfile off v,
    tree_names_distinct (TStree tree) ->
    tree_with_src Ftree srcpath tmppath src_inum file dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_src Ftree srcpath tmppath src_inum file dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_upd tree tmppath off v))).
  Proof.
    intros.
    unfold tree_with_src in *.
    destruct_lift H0. eexists.
    eapply sep_star_assoc.
    eapply sep_star_comm.
    eapply sep_star_assoc_1.
    eapply dirents2mem2_treeseq_one_upd_src; eauto.
    pred_apply.
    cancel.
    pred_apply.
    cancel.
  Qed.

  Lemma tsupd_d_in_exists: forall ts t tmppath off v,
    d_in t (tsupd ts tmppath off v) ->
    exists x, d_in x ts /\ t = (treeseq_one_upd x tmppath off v).
  Proof.
    intros.
    eapply d_in_nthd in H as Hin.
    destruct Hin.
    unfold tsupd in H0.
    rewrite d_map_nthd in H0.
    eexists (nthd x ts).
    split; eauto.
    eapply nthd_in_ds.
  Qed.

  Lemma tree_names_distinct_d_in: forall ts t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    d_in t ts ->
    tree_names_distinct (TStree t).
  Proof.
    intros.
    eapply NEforall_d_in in H as Hx.
    destruct Hx.
    apply H1.
    auto.
  Qed.

  Lemma tree_names_distinct_treeseq_one_upd: forall ts t t' off vs Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    d_in t ts -> t' = treeseq_one_upd t tmppath off vs ->
    tree_names_distinct (TStree t').
  Proof.
    intros.
    unfold treeseq_one_upd in H1.
    + destruct (find_subtree tmppath (TStree t)) eqn:D1.
      * destruct d eqn:D2.
        rewrite H1; simpl.
        eapply tree_names_distinct_update_subtree.
        eapply tree_names_distinct_d_in; eauto.
        apply TND_file.
        rewrite H1; eapply tree_names_distinct_d_in; eauto.
      * rewrite H1; eapply tree_names_distinct_d_in; eauto.
  Qed.

  Lemma treeseq_upd_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile (v0:BFILE.datatype) t0,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) (tsupd ts tmppath Off0 (fst v0, vsmerge t0)).
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    intros.
    eapply NEforall_d_in'.
    intros.
    eapply tsupd_d_in_exists in H0.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_upd; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H4.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.
    eexists {|
             DFData := (DFData x1) ⟦ Off0 := (fst v0, vsmerge t0) ⟧;
             DFAttr := DFAttr x1|}.
    eapply treeseq_one_upd_tree_rep_tmp; eauto.
    right.
    rewrite H2.
    eapply treeseq_one_upd_tree_rep_src; eauto.
  Qed.

  Lemma dirents2mem2_treeseq_one_file_sync_tmp : forall (F: @pred _ (@list_eq_dec string string_dec) _) tree tmppath inum f,
    let f' := synced_dirfile f in
    tree_names_distinct (TStree tree) ->
    (F * tmppath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * tmppath |-> File inum f')%pred (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H0 as Hfind; eauto.
    unfold treeseq_one_file_sync.
    destruct (find_subtree tmppath (TStree tree)).
    destruct d.
    inversion Hfind; subst; simpl.
    eapply dir2flatmem2_update_subtree; eauto.
    inversion Hfind.
    inversion Hfind.
  Qed.

  Lemma treeseq_one_file_sync_tree_rep_tmp: forall tree Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile,
   let tfile' := synced_dirfile tfile in
    tree_names_distinct (TStree tree) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_tmp Ftree srcpath tmppath src_inum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    unfold tree_with_tmp in *.
    destruct_lift H0. eexists.
    eapply sep_star_comm.
    eapply sep_star_assoc.
    eapply dirents2mem2_treeseq_one_file_sync_tmp; eauto.
    pred_apply.
    cancel.
  Qed.

  Lemma tssync_d_in_exists: forall ts t tmppath,
    d_in t (ts_file_sync tmppath ts) ->
    exists x, d_in x ts /\ t = (treeseq_one_file_sync x tmppath).
  Proof.
    intros.
    eapply d_in_nthd in H as Hin.
    destruct Hin.
    unfold ts_file_sync in H0.
    rewrite d_map_nthd in H0.
    eexists (nthd x ts).
    split; eauto.
    eapply nthd_in_ds.
  Qed.

  Lemma dirents2mem2_treeseq_one_file_sync_src : forall (F: @pred _ (@list_eq_dec string string_dec) _) F1 tree srcpath tmppath inum f,
    tree_names_distinct (TStree tree) ->
    (F1 * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree tree)) ->
    (F * srcpath |-> File inum f)%pred (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    eapply dir2flatmem2_find_subtree_ptsto in H1 as Hfind; eauto.
    eapply dir2flatmem2_find_subtree_ptsto_none in H0 as Hfindtmp; eauto.
    unfold treeseq_one_file_sync.
    intuition.
    destruct (find_subtree tmppath (TStree tree)).
    congruence.
    eassumption.
   Qed.

  Lemma treeseq_one_file_sync_tree_rep_src: forall tree Ftree srcpath tmppath src_inum file  tfile dstbase dstname dstfile,
    let tfile' := BFILE.synced_file tfile in
    tree_names_distinct (TStree tree) ->
    tree_with_src Ftree srcpath tmppath src_inum file  dstbase dstname dstfile (dir2flatmem2 (TStree tree)) ->
    tree_with_src Ftree srcpath tmppath src_inum file  dstbase dstname dstfile (dir2flatmem2 (TStree (treeseq_one_file_sync tree tmppath))).
  Proof.
    intros.
    unfold tree_with_src in *.
    destruct_lift H0. eexists.
    eapply sep_star_assoc.
    eapply sep_star_comm.
    eapply sep_star_assoc_1.
    eapply dirents2mem2_treeseq_one_file_sync_src; eauto.
    pred_apply.
    cancel.
    pred_apply.
    cancel.
  Qed.

  Lemma tree_names_distinct_treeseq_one_file_sync: forall ts t t' Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
      treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
      d_in t ts -> t' = treeseq_one_file_sync t tmppath ->
      tree_names_distinct (TStree t').
  Proof.
    intros.
    unfold treeseq_one_file_sync in H1.
    + destruct (find_subtree tmppath (TStree t)) eqn:D1.
      * destruct d eqn:D2.
        rewrite H1; simpl.
        eapply tree_names_distinct_update_subtree.
        eapply tree_names_distinct_d_in; eauto.
        apply TND_file.
        rewrite H1; eapply tree_names_distinct_d_in; eauto.
      * rewrite H1; eapply tree_names_distinct_d_in; eauto.
  Qed.


  Lemma treeseq_tssync_tree_rep: forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile)  (ts_file_sync tmppath ts).
  Proof.
    intros.
    unfold treeseq_pred, tree_rep in *.
    intros.
    eapply NEforall_d_in'.
    intros.
    eapply tssync_d_in_exists in H0; eauto.
    destruct H0.
    intuition.
    eapply tree_names_distinct_treeseq_one_file_sync; eauto.
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H4.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.
    eexists (synced_dirfile x1).
    eapply treeseq_one_file_sync_tree_rep_tmp; eauto.
    right.
    rewrite H2.
    eapply treeseq_one_file_sync_tree_rep_src; eauto.
    exact BFILE.bfile0.
  Qed.

  Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
    {< ds ts Fm Ftop Ftree srcpath file tfile v0 t0 dstbase dstname dstfile,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[[ DFData tfile ::: (Off0 |-> t0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
        (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' ts' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
      >} copydata fsxp srcinum tinum mscs.
   Proof.
    unfold copydata, tree_with_tmp; intros.
    step.
    eassign srcpath. cancel.
    step.
    eassign srcpath. cancel.
    pred_apply.
    cancel.
    step.
    2: eassign tmppath; cancel.
    msalloc_eq; eauto.
    pred_apply; cancel.
    step.
    denote! (forall _, treeseq_pred _ _ -> treeseq_pred _ _) as Ht.
    specialize (Ht tmppath).
    destruct Ht.
    msalloc_eq.
    eassumption.
    unfold treeseq_pred.
    unfold NEforall.
    split.
    msalloc_eq; eauto.
    msalloc_eq; eauto.
    step.

    safestep.
    2: eauto.
    or_l.
    cancel.

    eapply treeseq_tssync_tree_rep.
    eapply treeseq_upd_tree_rep.
    eauto.

    or_r.
    cancel.
    2: eauto.
    simpl.
    pred_apply. cancel.
    unfold synced_dirfile.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (DFData file)) by eauto.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (DFData f')) by eauto.
    simpl.
    cancel.

    eapply treeseq_pred_pushd.
    2: eapply treeseq_tssync_tree_rep.
    2: eapply treeseq_upd_tree_rep.
    2: eauto.

    unfold tree_rep; simpl; intuition.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    cancel.

    (* crashed during setattr  *)
    xcrash; eauto.
    eapply treeseq_tssync_tree_rep; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    eapply treeseq_pred_pushd.
    2: eapply treeseq_tssync_tree_rep; eauto.
    2: eapply treeseq_upd_tree_rep; eauto.
    unfold tree_rep; intuition.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

    (* crash during sync *)
    xcrash; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    (* crash during upd *)
    xcrash; eauto.
    rewrite H19.
    eapply treeseq_upd_tree_rep.
    eassumption.

    xcrash; eauto.

    xcrash; eauto.

  Grab Existential Variables.
    all: eauto.
    all: intros; exact True.
  Qed.

  Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.

  Hint Extern 0 (okToUnify (tree_with_tmp _ _ _ _ _ _ _ _ _) (tree_with_tmp _ _ _ _ _ _ _ _ _)) => constructor : okToUnify.

  Theorem copy2temp_ok : forall fsxp srcinum tinum mscs,
    {< Fm Ftop Ftree ds ts tmppath srcpath file tfile v0 dstbase dstname dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
        (([[ r = false ]] *
          exists f',
          [[ (tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!))) ]])
         \/ ([[ r = true ]] *
             [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
     exists ds' ts' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.
  Proof.
    unfold copy2temp; intros.
    step.
    eassign (Ftree).
    unfold tree_with_tmp; cancel.
    admit.
    admit. (* eapply list2nmem_inbound in H5. *)

    destruct a0.
    prestep. norm.

    safestep.
    intuition.

    specialize (H20 tmppath H8).
    msalloc_eq; eauto.

    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

    instantiate (1 := ($ (0), [])).
    admit. (* XXX need list2nmem_setlen? *)

    step.
    step.
    step.
    step.
    step.

    xcrash; eauto.

    step.

    xcrash; eauto.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.
  Admitted.

  Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Theorem copy_and_rename_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts srcpath tmppath file tfile v0 dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[r = false ]] *
        (exists f',
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])) \/
       ([[r = true ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' ts' mscs',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]]
    >} copy_and_rename fsxp srcinum tinum dstbase dstname mscs.
  Proof.
    unfold copy_and_rename; intros.
    step.
    step.

    admit.
    unfold tree_with_tmp; cancel.
    admit.

    step.
    step.

    edestruct dir2flatmem2_find_subtree_ptsto_dir with (tree := TStree ts' !!) (fnlist := @nil string).
    distinct_names'.
    pred_apply; cancel.

    admit.
    eassumption.



    prestep; norml; unfold stars; simpl.

    edestruct dir2flatmem2_find_subtree_ptsto_dir with (tree := TStree ts' !!) (fnlist := @nil string).
    distinct_names'.
    pred_apply; cancel.
    cancel.

    edestruct dir2flatmem2_find_subtree_ptsto_dir with (tree := TStree ts' !!) (fnlist := @nil string).
    distinct_names'.
    pred_apply; cancel.
    cancel.
    eassign (@nil string); simpl; f_equal; eauto.
    repeat rewrite app_nil_l. cancel.

    step.
    step.

    xcrash; eauto.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl.
    distinct_names.
    right. unfold tree_with_src. pred_apply. cancel.

    (* XXX broken below this point *)

    eauto.
    eauto.
    eauto.
    eapply sep_star_split_l in H11 as H11'.
    destruct H11'.
    admit.  (* implied by H6 *)
    admit.
    step.
    step.
    or_r.
    cancel.
    admit. (* eapply H19. *)

    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    admit.

    erewrite treeseq_in_ds_eq; eauto.
    step.

    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    admit.  (* XXX maybe ts' is ts *)

    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    admit.  (* XXX maybe ts' is ts *)
 
    step.

    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    admit.  (* XXX maybe ts's is ts *)
  Admitted.

  Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.


  (* specs for copy_and_rename_cleanup and atomic_cp *)

Lemma rep_tree_crash: forall Fm fsxp Ftop d t ilist frees ms d',
  (Fm * rep fsxp Ftop t ilist frees ms)%pred (list2nmem d) ->
  crash_xform (diskIs (list2nmem d)) (list2nmem d') ->
  (exists t', [[ tree_crash t t' ]] * (crash_xform Fm) * rep fsxp Ftop t' ilist frees ms)%pred (list2nmem d').
Proof.
  intros.
  eapply crash_xform_pimpl_proper in H0; [ | apply diskIs_pred; eassumption ].
  apply crash_xform_sep_star_dist in H0.
  rewrite xform_tree_rep in H0.
  destruct_lift H0.
  exists dummy.
  pred_apply.
  cancel.
Qed.

Lemma treeseq_tree_crash_exists: forall Fm Ftop fsxp mscs ts ds n d ms,
  let t := (nthd n ts) in
  treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
  crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
  (exists t', [[ tree_crash (TStree t) t' ]] *  (crash_xform Fm) * rep fsxp Ftop t' (TSilist t) (TSfree t) ms)%pred (list2nmem d).
Proof.
  intros.
  unfold treeseq_in_ds in H.
  eapply NEforall2_d_in in H.
  2: instantiate (1 := n).
  2: instantiate (1 := (nthd n ts)); eauto.
  2: instantiate (1 := (nthd n ds)); eauto.
  intuition.
  eapply rep_tree_crash.
  unfold tree_rep in H1.
  instantiate (1 := (nthd n ds)).
  pred_apply.
  cancel.
  eassumption.
Qed.

Lemma tree_rep_treeseq: forall Fm Ftop fsxp  d t a,
  TREESEQ.tree_rep Fm Ftop fsxp t (list2nmem d) ->
  treeseq_in_ds Fm Ftop fsxp a (t, []) (d, []).
Proof.
  intros.
  unfold treeseq_in_ds.
  constructor; simpl.
  intuition.
  unfold treeseq_one_safe; simpl.
  eapply dirtree_safe_refl.
  constructor.
Qed.

Lemma find_name_dirtree_inum: forall t inum,
  find_name [] t = Some (inum, true) ->
  dirtree_inum t = inum.
Proof.
  intros.
  eapply find_name_exists in H.
  destruct H.
  intuition.
  unfold find_subtree in H0.
  inversion H0; eauto.
Qed.

Lemma find_name_dirtree_isdir: forall t inum,
  find_name [] t = Some (inum, true) ->
  dirtree_isdir t = true.
Proof.
  intros.
  eapply find_name_exists in H.
  destruct H.
  intuition.
  unfold find_subtree in H0.
  inversion H0; eauto.
Qed.

(*
Theorem tree_crash_find_name : forall F fnlist t t' f f' inum,
  tree_crash t t' ->
  BFILE.file_crash f f' ->
  (F * fnlist |-> Some (inum, f))%pred (dir2flatmem2 t) ->
  (F * fnlist |-> Some (inum, f'))%pred (dir2flatmem2 t').
Proof.
  (* XXX use treecrash.v version *)
Admitted.
*)

Lemma find_dir_exists: forall pathname t inum,
  find_name pathname t = Some (inum, true) ->
  exists tree_elem, find_subtree pathname t = Some (TreeDir inum tree_elem).
Proof.
    intros.
Admitted.

  Ltac nthtree :=
    repeat match goal with 
    | [ H : NEforall _ _ |- _ ]  => 
      eapply NEforall_d_in in H; [|eapply nthd_in_ds]; destruct H; intuition; simpl
    | [ H: find_name _ (TStree (nthd _ _ )) = _ |- _ ]=>
      eapply DTCrash.tree_crash_root in H; eauto 
    | [ H: find_name [] ?x = Some (_, _) |- dirtree_inum ?x = _ ] =>
      eapply find_name_dirtree_inum; eauto
    | [ H: find_name [] ?x = Some (_, _) |- dirtree_isdir ?x = _ ] =>
      eapply find_name_dirtree_isdir; eauto
    end.

  Theorem atomic_cp_recover_ok :
    {< Fm Ftop Ftree fsxp cs mscs ds ts tmppath srcpath file srcinum tinum dstfile (dstbase: list string) (dstname:string),
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ NEforall (fun t => exists tfile,
        find_name [] (TStree t) = Some (the_dnum, true) /\
        ((tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
        (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname (dir2flatmem2 (TStree t)))))%type ts ]]
    POST:hm' RET:r
      exists n d t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs' (t, nil) (d, nil) ]] *
      [[ forall Ftree f,
         (Ftree * tmppath |-> f)%pred (dir2flatmem2 (TStree (nthd n ts))) ->
         (Ftree * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree t)) ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists n d t,
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs (t, nil) (d, nil) ]] *
      [[ forall Ftree f,
         (Ftree * tmppath |-> f)%pred (dir2flatmem2 (TStree (nthd n ts))) ->
         (Ftree * tmppath |-> Nothing)%pred (dir2flatmem2 (TStree t)) ]]
    >} atomic_cp_recover.
  Proof.
    unfold atomic_cp_recover; intros.
    prestep. norml.  (* XXX slow! *)
    safecancel.

    denote! (NEforall _ _) as Tpred.

    (* need to apply treeseq_tree_crash_exists before
     * creating evars in postcondition *)
    prestep. norm'l.

    denote! (crash_xform _ _) as Hcrash.

    eapply treeseq_tree_crash_exists in Hcrash; eauto.
    destruct Hcrash.
    destruct_lift H.
    cancel.
    instantiate (ts0 := ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts))), [])); simpl in *.

    eapply tree_rep_treeseq; eauto.

    nthtree.
    nthtree.

    destruct a1; subst; simpl.

    - (* tmp exists in x *)
      step.  (* delete *)

      instantiate (ts1 := ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts))), [])).
      eapply tree_rep_treeseq; eauto.
      instantiate (pathname0 := []).
      nthtree.
      admit. admit. (* XXX create x's direlems earlier *)
      simpl.
      eapply tree_crash_find_name; eauto.
      admit.  (* XXX fix tree_crash_find_name not to require file_crash? *)
      admit. (* follow from Tpred *)

      step.  (* sync *)

      (* two cases: delete succeeded or not *)

      (* ts1 is x with temp deleted, or is this case where rename fails *)
      admit.
      step.
      admit.
      admit.
      admit.

      step.  (* delete succeeded *)

      admit.
      admit.
      admit.
      admit.
      admit.

    - (* tmp doesn't exist *)

      step.
      instantiate (t0 := (mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)))).
      eapply tree_rep_treeseq; eauto.
      admit. (* H, but what do we know about crash_xform Fm *)
      simpl.
      admit. (* H7 and a version of tree_crash_find_name? *)

   - (* crash conditions *)


  Admitted.

End ATOMICCP.



Lemma flist_crash_exists: forall flist,
  exists flist', BFILE.flist_crash flist flist'.
Proof.
  intros.
  induction flist.
  - eexists [].
    unfold BFILE.flist_crash; simpl.
    eapply Forall2_nil.
  - edestruct file_crash_exists.
    destruct IHflist.
    exists (x :: x0).
    eapply Forall2_cons.
    eassumption.
    eassumption.
Qed.


(* this might be provable because possible_crash tells us the vs for each block 
 * on the disk. we should be able to use that vs to construct file_crash. *)
Lemma possible_crash_flist_crash: forall F bxps ixp d d' ilist frees flist c1 c2 c3,
  (F * (BFILE.rep bxps ixp flist ilist frees c1 c2 c3))%pred (list2nmem d) ->
  possible_crash (list2nmem d) (list2nmem d') ->
  exists flist', BFILE.flist_crash flist flist'.
Proof.
  intros.
  eapply flist_crash_exists.
Qed.
