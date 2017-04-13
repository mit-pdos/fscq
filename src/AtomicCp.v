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
    Ftree * nil |-> Dir the_dnum * 
            srcpath |-> File srcinum file * 
            tmppath |-> Nothing * 
            (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_tmp Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum tfile dstbase dstname dstfile:  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    [[ Datatypes.length (DFData tfile) <= 1 ]] *
    Ftree * nil |-> Dir the_dnum * 
            srcpath |-> File srcinum file * 
            tmppath |-> File tinum tfile *
            (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_dst Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname :  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum * 
            srcpath |-> File srcinum file * 
            tmppath |-> Nothing *
            (dstbase ++ [dstname])%list |-> File dstinum (synced_dirfile file))%pred.

  Definition tree_rep Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum dstbase dstname dstfile t := 
    (tree_names_distinct (TStree t)) /\
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname(dir2flatmem2 (TStree t))))%type.

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
    eapply pimpl_apply.
    2: eapply dirents2mem2_treeseq_one_upd_tmp; eauto.
    cancel.
    rewrite length_updN; eauto.
    pred_apply; cancel.
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

    right. left.
    rewrite H2.
    eapply treeseq_one_upd_tree_rep_src; eauto.

    right. right.
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
    eapply pimpl_apply.
    2: eapply dirents2mem2_treeseq_one_file_sync_tmp; eauto.
    cancel.
    2: pred_apply; cancel.
    unfold synced_list, datatype.
    rewrite combine_length_eq; rewrite map_length; eauto.
    rewrite repeat_length; eauto.
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
    right. left.
    rewrite H2.
    eapply treeseq_one_file_sync_tree_rep_src; eauto.
    exact BFILE.bfile0.
    right. right.
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
    unfold copy2temp, tree_with_tmp; intros.
    step.
    admit. (* eapply list2nmem_inbound in H5. *)

    destruct a0.
    prestep. norm.
    inv_option_eq.
    inv_option_eq.

    cancel.
    intuition.
    eassumption.
    msalloc_eq. eauto.

    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

    rewrite latest_pushd; simpl.
    unfold tree_with_tmp; pred_apply; cancel.

    eassumption.

    instantiate (1 := ($ (0), [])).
    admit. (* XXX need list2nmem_setlen? *)

    step.
    or_l. unfold tree_with_tmp in *; cancel.

    xcrash.

    step.

    xcrash.
    eassumption.
    eauto.
    eassumption.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.
  Admitted.

  Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Lemma tree_with_tmp_the_dnum: forall Fm Ftop fsxp mscs Ftree srcpath tmppath srcinum file tinum
      tfile dstbase dstname dstfile ts ds,
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstfile
          (dir2flatmem2 (TStree ts !!)) ->
    exists direlem, 
        find_subtree [] (TStree ts !!) = Some (TreeDir the_dnum direlem).
  Proof.
    intros.
    unfold tree_with_tmp in H0.
    edestruct dir2flatmem2_find_subtree_ptsto_dir with 
      (tree := TStree ts !!) (fnlist := @nil string)
      (F := (exists dstinum : addr,
          (Ftree ✶ (srcpath |-> File srcinum file)
           ✶ tmppath |-> File tinum tfile)
          ✶ (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred).
    distinct_names'.
    pred_apply; cancel.
    eexists x; auto.
  Qed.

  Lemma tree_with_tmp_tmp_dst: forall Fm Ftop fsxp mscs Ftree srcpath tmppath srcinum file tinum
      tfile dstbase dstname dstfile ts ds,
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstfile
          (dir2flatmem2 (TStree ts !!)) ->
    (exists F' dstinum, ((F' ✶ ((tmppath)%list |-> File tinum tfile)
        ✶ (dstbase ++ [dstname])%list |-> File dstinum dstfile  )%pred (dir2flatmem2 (TStree ts !!))) /\
      (F' = (Ftree ✶ ([] |-> Dir the_dnum) ✶ srcpath |-> File srcinum file)%pred)).
  Proof.
    intros.
    unfold tree_with_tmp in H0. 
    destruct H0.
    eexists (((Ftree ✶ [] |-> Dir the_dnum) ✶ srcpath |-> File srcinum file)%pred).
    eexists x.
    split.
    pred_apply. cancel.
    reflexivity.
  Qed.

  Theorem copy_and_rename_ok : forall fsxp srcinum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts srcpath file tfile v0 dstfile,
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
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]] *
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

    prestep. norml. 
    eapply tree_with_tmp_the_dnum in H14 as Hdnum; eauto. deex.
    cancel.

    eapply tree_with_tmp_the_dnum in H14 as Hdnum; eauto. deex.
    eapply tree_with_tmp_tmp_dst in H14 as Hdst; eauto. repeat deex.
    safecancel.
    eassign (@nil string). simpl. rewrite H13; eauto.
    pred_apply; cancel.
  
    step.
    step.

    or_r. unfold tree_with_dst.
    safecancel.

    unfold treeseq_pred, NEforall; simpl.
    intuition.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition.
    distinct_names.
    right. right.
    pred_apply. unfold tree_with_dst.
    cancel.

    xcrash; eauto.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl.
    distinct_names.
    right. right. 
    unfold tree_with_dst. pred_apply. cancel.

    step.
    or_l. cancel.
    unfold tree_with_tmp; cancel.

    unfold treeseq_pred, NEforall; simpl.
    intuition.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition.
    distinct_names'.
    left.
    pred_apply. unfold tree_with_tmp.
    cancel.

    xcrash.
    eassumption. eauto.
     
    xcrash.
    eassumption. eauto.

    eassumption.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl.
    distinct_names.
    right. right.
    unfold tree_with_dst. pred_apply; cancel.

    cancel.
    eassumption.
    step.
    unfold treeseq_pred, NEforall; simpl.
    intuition.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition.
    distinct_names'.
    left. eauto.
   
    xcrash.
    eassumption. eauto.

  Grab Existential Variables.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.


  (* specs for copy_and_rename_cleanup and atomic_cp *)

  Lemma rep_tree_crash: forall Fm fsxp Ftop d t ilist frees mscs d' msll',
    (Fm * rep fsxp Ftop t ilist frees mscs)%pred (list2nmem d) ->
    crash_xform (diskIs (list2nmem d)) (list2nmem d') ->
    (exists t', [[ tree_crash t t' ]] * (crash_xform Fm) *
      rep fsxp (BFileCrash.flist_crash_xform Ftop) t' ilist frees (BFILE.ms_empty msll')
    )%pred (list2nmem d').
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


  Lemma treeseq_tree_crash_exists: forall Fm Ftop fsxp mscs ts ds n d msll',
    let t := (nthd n ts) in
    treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    (exists t', [[ tree_crash (TStree t) t' ]] *
     (crash_xform Fm) * 
     rep fsxp (BFileCrash.flist_crash_xform Ftop) t' (TSilist t) (TSfree t) (BFILE.ms_empty msll')
    )%pred (list2nmem d).
  Proof.
    intros.
    unfold treeseq_in_ds in H.
    destruct H.
    eapply NEforall2_d_in in H.
    2: instantiate (1 := n).
    2: instantiate (1 := (nthd n ts)); eauto.
    2: instantiate (1 := (nthd n ds)); eauto.
    intuition.
    unfold TREESEQ.tree_rep in H2.
    destruct H2.
    eapply rep_tree_crash.
    instantiate (1 := (nthd n ds)).
    pred_apply.
    cancel.
    eassumption.
  Qed.

  Lemma treeseq_in_ds_crash: forall Fm Ftop fsxp d (t: dirtree)  n ts ms,
    BFILE.MSinitial ms ->
    (crash_xform Fm
      ✶ rep fsxp Ftop t (TSilist (nthd n ts))
          (TSfree (nthd n ts)) (BFILE.ms_empty (MSLL ms)))%pred (list2nmem d) ->
    treeseq_in_ds (crash_xform Fm) Ftop fsxp ms 
        ({| TStree := t; TSilist := TSilist (nthd n ts); TSfree := TSfree (nthd n ts) |}, []) 
        (d, []).
  Proof.
    intros.
    unfold treeseq_in_ds.
    constructor; simpl.
    split.
    unfold TREESEQ.tree_rep.
    intuition; simpl.
    pred_apply; safecancel.
    unfold treeseq_one_safe; simpl.
    eapply dirtree_safe_refl.
    constructor.
    unfold tree_rep_latest; simpl.
    pred_apply; cancel.

    replace ms with (BFILE.ms_empty (MSLL ms)).
    cancel.
    destruct ms.
    unfold ATOMICCP.MSLL.
    unfold BFILE.MSinitial in *.
    intuition. simpl in *. subst.
    unfold BFILE.ms_empty; simpl.
    reflexivity.
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

  Lemma tree_rep_find_root: forall Frest Ftree t,
    tree_names_distinct t ->
    (Frest * (Ftree ✶ [] |-> Dir the_dnum))%pred (dir2flatmem2 t) ->
    find_name [] t = Some (the_dnum , true).
  Proof.
    intros.
    assert (exists d, find_subtree [] t = Some (TreeDir the_dnum d)).
    eapply dir2flatmem2_find_subtree_ptsto_dir; eauto.
    pred_apply; cancel.
    destruct H1.
    unfold find_name.
    destruct (find_subtree [] t).
    destruct d; congruence.
    congruence.
  Qed.

  Lemma tree_pred_crash_root: forall Ftree srcpath tmppath srcinum file tinum dstbase 
      dstname dstfile ts n t',
    let t := (nthd n ts) in
    treeseq_pred
     (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    tree_crash (TStree t) t' ->
    find_name [] t' = Some (the_dnum, true).
  Proof.
    intros; subst t.
    unfold treeseq_in_ds in H; intuition.
    unfold treeseq_pred in H.
    eapply NEforall_d_in with (x := nthd n ts) in H.
    2: eapply nthd_in_ds.
    unfold tree_rep in H.
    intuition.
  
    destruct H.
    unfold tree_with_tmp in *.

    destruct H.
    eapply tree_crash_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_root with (Ftree:= Ftree); eauto.
    pred_apply; cancel.

    unfold tree_with_src in *.
    destruct H2.
    eapply tree_crash_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_root with (Ftree:= Ftree); eauto.
    pred_apply; cancel.

    unfold tree_with_dst in *.
    destruct H2.
    eapply tree_crash_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_root with (Ftree:= Ftree); eauto.
    pred_apply; cancel.
  Qed.

  Theorem atomic_cp_recover_ok :
    {< Fm Ftop Ftree fsxp cs mscs ds ts tmppath srcpath file srcinum tinum dstfile (dstbase: list string) (dstname:string),
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]]
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
      exists d t,
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs (t, nil) (d, nil) ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]]
    >} atomic_cp_recover.
  Proof.
    unfold atomic_cp_recover; intros.
    prestep. norml.
    safecancel.

    (* need to apply treeseq_tree_crash_exists before
     * creating evars in postcondition to create a
     * treeseq_in_ds on crashed disk. *)
    prestep. norm'l. 

    denote! (crash_xform _ _) as Hcrash.
    eapply treeseq_tree_crash_exists with (msll' := (MSLL ms)) in Hcrash; eauto.
    destruct Hcrash.
    destruct_lift H0.
    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
    eapply treeseq_in_ds_crash; eauto.

    (* other preconditions of lookup *)      
    eapply tree_pred_crash_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_inum; eauto.
    eapply tree_pred_crash_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_isdir; eauto.

    prestep; norm'l.
    cancel.
    instantiate (pathname0 := []).
    admit. (* follows from h9 *)
    admit. (* variant of eapply dir2flatmem2_find_name_ptsto. *)

    prestep; norm'l.
    cancel.

    eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
    eapply treeseq_in_ds_crash; eauto.

    pred_apply. unfold TREESEQ.tree_rep; cancel.

    step.  (* return *)

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
