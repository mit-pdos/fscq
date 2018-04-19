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
Require Import DirSepCrash.
Require Import SyncedMem.

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
        let^ (mscs) <- AFS.tree_sync fsxp mscs;   (* sync blocks *)
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
        match ok with
        | Err e => Ret (Err e)
        | OK _ => Ret (OK (mscs, fsxp))
        end
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
    Ftree * nil |-> Dir the_dnum * 
            srcpath |-> File srcinum file *
            tmppath |-> File tinum tfile *
            (dstbase ++ [dstname])%list |-> File dstinum dstfile)%pred.

  Definition tree_with_dst Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname :  @pred _ (list_eq_dec string_dec) _ :=
   (exists dstinum,
    Ftree * nil |-> Dir the_dnum *
            srcpath |-> File srcinum file *
            tmppath |-> Nothing *
            (dstbase ++ [dstname])%list |-> File dstinum file)%pred.

  Definition tree_rep Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) tinum dstbase dstname dstfile t := 
    (tree_names_distinct (TStree t)) /\
    (file = synced_dirfile file) /\
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree t))) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname (dir2flatmem2 (TStree t))))%type.

  Definition tree_rep_recover Ftree (srcpath: list string) tmppath (srcinum:addr) (file:dirfile) dstbase dstname dstfile t :=
    (tree_names_distinct (TStree t)) /\
    (file = synced_dirfile file) /\
    ((exists dstfile',
      tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile' *
      [[ file_crash dstfile dstfile' ]])%pred (dir2flatmem2 (TStree t)) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred (dir2flatmem2 (TStree t)))%type.

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
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H3.
    unfold tree_with_tmp in H3.
    rewrite H2.
    left.

    eexists {|
             DFData := (DFData x1) ⟦ Off0 := (fst v0, vsmerge t0) ⟧;
             DFAttr := DFAttr x1|}.
    eapply treeseq_one_upd_tree_rep_tmp; eauto.
    eauto.

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
    pred_apply; cancel.
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
    eapply NEforall_d_in in H as Hx.
    2: instantiate (1 := x0); eauto.
    intuition.
    destruct H3.
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

  Lemma length_synced_tmpfile : forall a v f,
    (a |-> v)%pred (list2nmem (DFData f)) ->
    Datatypes.length (synced_list (map fst (DFData f))) <= 1.
  Proof.
    intros.
    rewrite synced_list_length. rewrite map_length.
    eapply ptsto_a_list2nmem_mem_eq in H. rewrite H.
    simpl; omega.
  Qed.

  Hint Resolve length_synced_tmpfile.

  Lemma treerep_synced_dirfile: 
    forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile ts,
    treeseq_pred
      (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    file = synced_dirfile file.
  Proof.
    intros.
    unfold treeseq_pred, NEforall in H.
    intuition.
    unfold tree_rep in H0.
    intuition.
  Qed.

  Hint Resolve treerep_synced_dirfile.

  Theorem copydata_ok : forall fsxp srcinum tmppath tinum mscs,
    {< ds sm ts Fm Ftop Ftree srcpath file tfile v0 t0 dstbase dstname dstfile,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[[ DFData tfile ::: (Off0 |-> t0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts' sm',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
        (([[ isError r ]] *
          exists f', [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = OK tt ]] *
             [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' sm' ts' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
      >} copydata fsxp srcinum tinum mscs.
   Proof.
    unfold copydata, tree_with_tmp; intros.
    step.
    eassign srcpath. cancel.
    prestep. norm. cancel.
    eassign srcpath. intuition eauto.
    pred_apply. cancel.
    pred_apply. cancel.
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
    eauto.

    eapply treeseq_tssync_tree_rep.
    eapply treeseq_upd_tree_rep.
    eauto.
    2: eauto.

    or_r.
    cancel.
    2: eauto.
    unfold synced_dirfile.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (DFData file)) by eauto.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (DFData f')) by eauto.
    cancel.

    eapply treeseq_pred_pushd.
    2: eapply treeseq_tssync_tree_rep.
    2: eapply treeseq_upd_tree_rep.
    2: eauto.

    unfold tree_rep; simpl; intuition; eauto.
    distinct_names.

    left.
    unfold tree_with_tmp.
    pred_apply.
    cancel.
    eauto.

    (* crashed during setattr  *)
    xcrash; eauto.
    eapply treeseq_tssync_tree_rep; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    eapply treeseq_pred_pushd.
    2: eapply treeseq_tssync_tree_rep; eauto.
    2: eapply treeseq_upd_tree_rep; eauto.
    unfold tree_rep; intuition; eauto.
    distinct_names.

    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.
    eauto.

    (* crash during sync *)
    xcrash; eauto.
    eapply treeseq_upd_tree_rep; eauto.

    (* crash during upd *)
    xcrash; eauto.
    match goal with H: (_, _) = _ |- _ => rewrite H end.
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
    {< Fm Ftop Ftree ds sm ts tmppath srcpath file tfile v0 dstbase dstname dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe tmppath (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ 1 >= Datatypes.length (DFData tfile) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts' ]] *
        (([[ r = false ]] *
          exists f',
          [[ (tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!))) ]])
         \/ ([[ r = true ]] *
             [[ tree_with_tmp Ftree srcpath tmppath srcinum file tinum 
                  (synced_dirfile file) dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
     exists ds' sm' ts' mscs',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts']]
    >} copy2temp fsxp srcinum tinum mscs.
  Proof.
    unfold copy2temp, tree_with_tmp; intros.
    step.

    destruct a0.
    prestep. norm.
    inv_option_eq.
    inv_option_eq.

    cancel.
    intuition.
    eassumption.
    msalloc_eq. eauto.

    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; eauto.
    distinct_names.

    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

    rewrite latest_pushd; simpl.
    unfold tree_with_tmp; pred_apply; cancel.

    eassumption.

    simpl.
    eapply pimpl_apply.
    2: apply list2nmem_array.
    rewrite arrayN_ptsto_selN_0.
    unfold Off0; cancel.
    rewrite setlen_length; omega.

    step.
    or_l. unfold tree_with_tmp in *; cancel.

    xcrash.

    step.

    xcrash.
    eassumption.
    eauto.
    eassumption.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; eauto.
    distinct_names.
    left; unfold tree_with_tmp; simpl.
    pred_apply. cancel.

  Grab Existential Variables.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Lemma tree_with_tmp_the_dnum: forall Fm Ftop fsxp sm mscs Ftree srcpath tmppath srcinum file tinum
      tfile dstbase dstname dstfile ts ds,
    treeseq_in_ds Fm Ftop sm fsxp mscs ts ds ->
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

  Lemma tree_with_tmp_tmp_dst: forall Fm Ftop fsxp sm mscs Ftree srcpath tmppath srcinum file tinum
      tfile dstbase dstname dstfile ts ds,
    treeseq_in_ds Fm Ftop sm fsxp mscs ts ds ->
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
    {< Fm Ftop Ftree ds sm ts srcpath file tfile v0 dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                tfile dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]] *
      [[ 1 >= Datatypes.length (DFData tfile) ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]] *
       (([[r = false ]] *
        (exists f',
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum 
                f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]])) \/
       ([[r = true ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists ds' ts' sm' mscs',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]]
    >} copy_and_rename fsxp srcinum tinum dstbase dstname mscs.
  Proof.
    unfold copy_and_rename; intros.
    step.

    prestep. norml. 
    eapply tree_with_tmp_the_dnum in H15 as Hdnum; eauto. deex.
    cancel.

    eapply tree_with_tmp_the_dnum in H15 as Hdnum; eauto. deex.
    eapply tree_with_tmp_tmp_dst in H15 as Hdst; eauto. repeat deex.
    safecancel.
    eassign (@nil string). simpl. rewrite H14; eauto.
    pred_apply; cancel.

    step.
    step.

    or_r. unfold tree_with_dst.
    safecancel.
    erewrite <- treerep_synced_dirfile; eauto.

    unfold treeseq_pred, NEforall; simpl.
    intuition; eauto.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition; eauto.
    distinct_names.
    right. right.
    pred_apply. unfold tree_with_dst.
    cancel.
    erewrite <- treerep_synced_dirfile; eauto.

    xcrash; eauto.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl; eauto.
    distinct_names.
    right. right. 
    unfold tree_with_dst. pred_apply. cancel.
    erewrite <- treerep_synced_dirfile; eauto.

    step.
    or_l. cancel.
    unfold tree_with_tmp; cancel.
    eauto.

    unfold treeseq_pred, NEforall; simpl.
    intuition; eauto.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition; eauto.
    distinct_names'.

    xcrash.
    eassumption. eauto.

    xcrash.
    eassumption. eauto.

    eassumption.
    eapply treeseq_pred_pushd; eauto.
    unfold tree_rep; intuition; simpl; eauto.
    distinct_names.
    right. right.
    unfold tree_with_dst. pred_apply; cancel.

    cancel.
    erewrite <- treerep_synced_dirfile; eauto.
    cancel.

    eassumption.
    step.
    unfold treeseq_pred, NEforall; simpl.
    intuition; eauto.
    2: apply Forall_nil.
    unfold tree_rep.
    intuition; eauto.
    distinct_names'.

    xcrash.
    eassumption. eauto.

    xcrash.
    eassumption. eauto.

  Grab Existential Variables.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.


  (* specs for copy_and_rename_cleanup and atomic_cp *)

  Lemma rep_tree_crash: forall Fm fsxp Ftop d t ilist frees sm mscs d' msll',
    (Fm * rep fsxp Ftop t ilist frees mscs sm)%pred (list2nmem d) ->
    crash_xform (diskIs (list2nmem d)) (list2nmem d') ->
    (exists t', [[ tree_crash t t' ]] * (crash_xform Fm) *
      rep fsxp (BFileCrash.flist_crash_xform Ftop) t' ilist frees (BFILE.ms_empty msll') sm_synced
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


  Lemma treeseq_tree_crash_exists: forall Fm Ftop fsxp sm mscs ts ds n d msll',
    let t := (nthd n ts) in
    treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    (exists t', [[ tree_crash (TStree t) t' ]] *
     (crash_xform Fm) * 
     rep fsxp (BFileCrash.flist_crash_xform Ftop) t' (TSilist t) (TSfree t) (BFILE.ms_empty msll') sm_synced
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
    repeat (denote exis as He; destruct He).
    eapply rep_tree_crash.
    instantiate (1 := (nthd n ds)).
    pred_apply.
    subst t.
    cancel.
    eassumption.
  Qed.

  Lemma treeseq_in_ds_crash: forall Fm Ftop fsxp d (t: dirtree) n ts sm ms,
    BFILE.MSinitial ms ->
    (crash_xform Fm
      ✶ rep fsxp Ftop t (TSilist (nthd n ts))
          (TSfree (nthd n ts)) (BFILE.ms_empty (MSLL ms)) sm)%pred (list2nmem d) ->
    treeseq_in_ds (crash_xform Fm) Ftop fsxp sm ms
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


  Lemma tree_rep_find_subtree_root: forall Frest Ftree t,
    tree_names_distinct t ->
    (Frest * (Ftree ✶ [] |-> Dir the_dnum))%pred (dir2flatmem2 t) ->
    (exists elem, find_subtree [] t = Some (TreeDir the_dnum elem)).
  Proof.
    intros.
    assert (exists d, find_subtree [] t = Some (TreeDir the_dnum d)).
    eapply dir2flatmem2_find_subtree_ptsto_dir; eauto.
    pred_apply; cancel.
    eauto.
  Qed.


  Lemma tree_rep_find_name_root: forall Frest Ftree t,
    tree_names_distinct t ->
    (Frest * (Ftree ✶ [] |-> Dir the_dnum))%pred (dir2flatmem2 t) ->
    find_name [] t = Some (the_dnum , true).
  Proof.
    intros.
    eapply tree_rep_find_subtree_root in H0.
    destruct H0.
    unfold find_name.
    destruct (find_subtree [] t).
    destruct d; congruence.
    congruence.
    eauto.
  Qed.

  Lemma tree_pred_crash_find_subtree_root: forall Ftree srcpath tmppath srcinum file tinum dstbase 
      dstname dstfile ts n t',
    let t := (nthd n ts) in
    treeseq_pred
     (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    tree_crash (TStree t) t' ->
    (exists elem, find_subtree [] t' = Some (TreeDir the_dnum elem)).
  Proof.
    intros; subst t.
    unfold treeseq_in_ds in H; intuition.
    unfold treeseq_pred in H.
    eapply NEforall_d_in with (x := nthd n ts) in H.
    2: eapply nthd_in_ds.
    unfold tree_rep in H.
    intuition; eauto.

    destruct H2.
    unfold tree_with_tmp in *. 
    destruct H2.
    eapply tree_crash_find_subtree_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
    pred_apply; cancel.

    unfold tree_with_src in *. 
    destruct H3.
    eapply tree_crash_find_subtree_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
    pred_apply; cancel.

    unfold tree_with_dst in *. 
    destruct H3.
    eapply tree_crash_find_subtree_root with (t := TStree (nthd n ts)); eauto.
    eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
    pred_apply; cancel.
  Qed.


  Lemma tree_pred_crash_find_name_root: forall Ftree srcpath tmppath srcinum file tinum dstbase 
      dstname dstfile ts n t',
    let t := (nthd n ts) in
    treeseq_pred
     (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    tree_crash (TStree t) t' ->
    find_name [] t' = Some (the_dnum, true).
  Proof.
    intros; subst t.
    eapply tree_pred_crash_find_subtree_root in H; eauto.
    destruct H.
    unfold find_name.
    destruct (find_subtree [] t').
    destruct d.
    inversion H.
    inversion H; subst; eauto.
    inversion H.
  Qed.

  Lemma treeseq_pred_d_in : forall p ts t,
    treeseq_pred p ts ->
    d_in t ts ->
    p t.
  Proof.
    unfold treeseq_pred; intros.
    eapply NEforall_d_in in H; eauto.
  Qed.

  Lemma treeseq_pred_nthd : forall p ts n,
    treeseq_pred p ts ->
    p (nthd n ts).
  Proof.
    intros.
    eapply treeseq_pred_d_in; eauto.
    apply nthd_in_ds.
  Qed.

  Lemma treeseq_pred_tree_rep_dir2flatmem2 : forall ts Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
    treeseq_pred (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile) ts ->
    treeseq_pred (fun t =>
      ((exists tfile', 
        tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile) \/
       (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile) \/
       (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname))%pred
      (dir2flatmem2 (TStree t))) ts.
  Proof.
    unfold treeseq_pred, tree_rep; intros.
    eapply NEforall_impl; eauto; intros; simpl in *.
    intuition.
    - deex.
      pred_apply. cancel.
    - pred_apply; cancel.
    - pred_apply; cancel.
  Qed.

  Lemma tree_with_tmp_find_name : forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile v t,
    flatmem_crash_xform
        ((exists tfile' : dirfile,
            tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile)
        \/ tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile
        \/ tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred
        (dir2flatmem2 t) ->
    Some v = find_name tmppath t ->
    tree_names_distinct t ->
    flatmem_crash_xform
        ((exists tfile' : dirfile,
            tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile))%pred
        (dir2flatmem2 t).
  Proof.
    intros.
    apply flatmem_crash_xform_or_dist in H.
    destruct H.
    pred_apply; cancel.
    exfalso.
    apply flatmem_crash_xform_or_dist in H.
    destruct H.
    - unfold tree_with_src in H.
      apply flatmem_crash_xform_exists in H; destruct_lift H.
      apply flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_nothing in H.
      unfold find_name in H0.
      erewrite dir2flatmem2_find_subtree_ptsto_none in H0; eauto.
      congruence.
      pred_apply; cancel.
    - unfold tree_with_dst in H.
      apply flatmem_crash_xform_exists in H; destruct_lift H.
      apply flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_sep_star in H.
      rewrite flatmem_crash_xform_nothing in H.
      unfold find_name in H0.
      erewrite dir2flatmem2_find_subtree_ptsto_none in H0; eauto.
      congruence.
      pred_apply; cancel.
  Qed.

  Lemma tree_with_tmp_find_name_none : forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t,
    flatmem_crash_xform
        ((exists tfile' : dirfile,
            tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile)
        \/ tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile
        \/ tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred
        (dir2flatmem2 t) ->
    None = find_name tmppath t ->
    tree_names_distinct t ->
    flatmem_crash_xform
        (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile \/
         tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname)%pred
        (dir2flatmem2 t).
  Proof.
    intros.
    apply flatmem_crash_xform_or_dist in H.
    destruct H.
    {
      exfalso.
      apply flatmem_crash_xform_exists in H. destruct_lift H.
      unfold tree_with_tmp in H.
      apply flatmem_crash_xform_exists in H. destruct_lift H.
      eapply pimpl_apply in H.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_file.
      2: reflexivity.
      destruct_lift H.
      destruct_lift H.
      unfold find_name in H0.
      erewrite dir2flatmem2_find_subtree_ptsto in H0; eauto.
      congruence.
      pred_apply.
      cancel.
    }

    eauto.
  Qed.
  
  
Lemma in_add_to_list_or: forall  tree name name' f,
  In name' (map fst (add_to_list name f tree)) ->
  name = name' \/ In name' (map fst tree).
Proof.
  induction tree; simpl in *; intros; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.

Lemma in_add_to_list_tree_or: forall  tree name t t',
  In t (add_to_list name t' tree) ->
  t = (name, t') \/ In t tree.
Proof.
  induction tree; simpl in *; intros; auto.
  destruct H.
  left; auto.
  right; auto.
  destruct a; simpl in *.
  destruct (string_dec s name); simpl in *.
  destruct H.
  left; auto.
  right; right; auto.
  destruct H.
  right; left; auto.
  apply IHtree in H.
  destruct H.
  left; auto.
  right; right; auto.
Qed.

Lemma treeseq_pred_tree_rep_latest: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname
           dstfile ts,  
  treeseq_pred
        (tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname
           dstfile) ts ->
  tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile
  ts !!.
  Proof.
    intros.
    destruct ts; destruct l; unfold latest; simpl in *.
    destruct H; simpl in *.
    auto.
    destruct H; simpl in *.
    inversion H0; simpl in *; auto.
  Qed.
  
Lemma NoDup_add_to_list: forall tree f fname,
  NoDup (map fst tree) ->
  ~ In fname (map fst tree) ->
  NoDup (map fst (add_to_list fname f tree)).
Proof.
  induction tree; intros.
  unfold add_to_list.
  apply NoDup_cons.
  apply in_nil.
  apply NoDup_nil.
  destruct a; simpl in *.
  destruct (string_dec s fname); simpl in *.
  destruct H0; left; auto.
  apply NoDup_cons.
  unfold not; intros.
  apply in_add_to_list_or in H1; auto.
  destruct H1.
  apply H0; left; auto.
  apply NoDup_cons_iff in H.
  apply H; auto.
  apply IHtree.
  apply NoDup_cons_iff in H.
  apply H; auto.
  unfold not; intros; apply H0.
  right; auto.
Qed.



Lemma treeseq_tree_rep_sync_after_create: forall x0 (F: pred) dummy1 dummy5 srcinum dummy6 dummy4 dstbase
           dstname dummy9 temp_fn x a6 dummy3 a4 a5_1 a5_2,
  treeseq_pred
        (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy4 dstbase
           dstname dummy9) dummy3 ->
  TStree dummy3 !! = TreeDir the_dnum x ->
  (F ✶ [temp_fn]%list |-> Nothing)%pred (dir2flatmem2 (TStree dummy3 !!)) ->
  (((((dstbase ++ [dstname])%list |-> File x0 dummy9
          ✶ dummy5 |-> File srcinum dummy6) ✶ [] |-> Dir the_dnum) ✶ dummy1)
       ✶ [temp_fn]%list |-> File a6 dirfile0)%pred
        (dir2flatmem2
           (tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
              (TStree dummy3 !!))) ->
  treeseq_pred
  (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 a6 dstbase dstname
     dummy9)
  ({|
   TStree := tree_graft the_dnum x [] temp_fn (TreeFile a6 dirfile0)
               (TStree dummy3 !!);
   TSilist := a4;
   TSfree := (a5_1, a5_2) |}, []).
Proof.
  intros.
  split; eauto.
  split; simpl.
  unfold tree_graft.
  apply tree_names_distinct_update_subtree.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  simpl.
  apply TND_dir.
  rewrite Forall_forall; intros dt Hx.
  apply in_map_iff in Hx.
  deex.
  apply in_add_to_list_tree_or in H5.
  destruct H5.
  rewrite H3; simpl; apply TND_file.
  
  eapply treeseq_pred_tree_rep_latest in H as Hz. destruct Hz.
  rewrite H0 in H4.
  inversion H4.
  rewrite Forall_forall in H8.
  apply H8.
  apply in_map; auto.
  
  apply NoDup_add_to_list.
  eapply treeseq_pred_tree_rep_latest in H as Hz; destruct Hz.
  rewrite H0 in H3.
  inversion H3.
  auto.

  eapply find_subtree_none_In.
  rewrite <- H0.
  eapply dir2flatmem2_find_subtree_ptsto_none.
  eapply tree_names_distinct_d_in; eauto; apply latest_in_ds.
  pred_apply; cancel.

  split.
  eapply treerep_synced_dirfile; eauto.
  left; eexists; unfold tree_with_tmp; pred_apply; cancel.
  simpl; apply Forall_nil.
Qed.
  
  

  Ltac synced_file_eq :=
    try match goal with
    | [ H : file_crash ?f ?f |- _ ] => clear H
    end;
    match goal with
    | [ H1 : treeseq_pred (tree_rep _ _ _ _ ?file _ _ _ _) _,
        H2 : file_crash ?file ?file' |- _ ] =>
      let Hx := fresh in
      let Hy := fresh in
      eapply treerep_synced_dirfile in H1 as Hx;
      erewrite Hx in H2;
      eapply file_crash_synced in H2 as Hy;
      try rewrite Hy in *;
      try rewrite <- Hx in *;
      clear Hx; clear Hy
    end.
    
    
      Theorem atomic_cp_ok : forall fsxp srcinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds sm ts srcpath file v0 dstfile tinum,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (treeseq_safe [temp_fn] (MSAlloc mscs) (ts !!)) ts ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]] *
      [[ tree_with_src Ftree srcpath [temp_fn] srcinum file dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ DFData file ::: (Off0 |-> v0) ]]] *
      [[ dirtree_inum (TStree ts!!) = the_dnum ]]
    POST:hm' RET:^(mscs', r)
      exists ds' sm' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') sm' hm' *
       (([[r = false ]] *
        ([[ treeseq_in_ds Fm Ftop fsxp sm' mscs ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file 
                    tinum dstbase dstname dstfile) ts' ]] *
          [[ tree_with_src Ftree srcpath [temp_fn] srcinum file 
                    dstbase dstname dstfile (dir2flatmem2 (TStree ts!!)) ]] 
                \/
         (exists f' tinum',
         [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
         [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file
                     tinum' dstbase dstname dstfile) ts' ]] *
         [[ tree_with_tmp Ftree srcpath [temp_fn] srcinum file tinum' 
                    f' dstbase dstname dstfile (dir2flatmem2 (TStree ts'!!)) ]]))) 
        \/
       (exists tinum',
          [[r = true ]] *
          [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
          [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file 
                          tinum' dstbase dstname dstfile) ts' ]] *
          [[ tree_with_dst Ftree srcpath [temp_fn] srcinum file 
                    dstbase dstname (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists mscs' ds' ts' sm',
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
       ((exists tinum, [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts']])
       \/ (exists t dfile tinum', [[ ts' = pushd t ts ]] * 
       [[ treeseq_in_ds Fm Ftop fsxp sm' mscs' ts' ds' ]] *
       [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
       [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]]))
    >} atomic_cp fsxp srcinum dstbase dstname mscs.
Proof.
  unfold atomic_cp.
  prestep.
  unfold pimpl; intros.
  destruct_lift H.
  unfold tree_with_src in *.
  destruct_lift H8.
  apply sep_star_assoc in H0.
  apply sep_star_comm in H0.
  apply sep_star_assoc in H0.
  apply sep_star_comm in H0.
  apply sep_star_assoc in H0.
  apply sep_star_assoc in H0.
  eapply dir2flatmem2_find_subtree_ptsto_dir in H0 as Hx.
  deex.
  pred_apply; norm.
  unfold stars; cancel.
  intuition; eauto.
  eapply treeseq_in_ds_tree_pred_latest; eauto.
  instantiate (2:= []); eauto.
  
  simpl; step.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (1:= {| TStree:= (tree_graft the_dnum d [] temp_fn 
                            (TreeFile a0 dirfile0) (TStree dummy4 !!));
                  TSilist:= ilist';
                  TSfree:= (frees'_1, frees'_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; rewrite <- H5; eauto.
  eauto.
  
  safestep.
  eauto.
  simpl; eauto.
  rewrite pushd_latest.
  unfold latest; simpl.
  split; eauto.
  apply treeseq_safe_refl.
  simpl; apply Forall_nil.
  
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.

  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H14; auto.
  pred_apply; cancel.
  
  unfold tree_with_tmp; simpl.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eexists.
  apply sep_star_assoc.
  apply sep_star_comm.
  apply sep_star_assoc.
  apply sep_star_comm.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H14; auto.
  pred_apply; cancel.
  simpl; auto.
  pred_apply; cancel.
  rewrite pushd_latest; simpl; auto.
  unfold dirfile0; simpl; omega.
  
  safestep.
  or_l; cancel.
  eauto.
  
  or_r; cancel.
  eauto.
  eauto.
  eauto.

  or_r; cancel; eauto.
  
  xcrash.
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m1 Hx; apply H25 in Hx; pred_apply; xcrash; eauto.
  or_l; cancel; eauto.
  xcrash; eauto.
  pred_apply; cancel.
  
  unfold pimpl; intros.
  eapply H2.
  instantiate (1:= realcrash).
  intros m1 Hx; apply H12 in Hx; pred_apply; xcrash; eauto.
  or_r; xcrash.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (2:= {| TStree:= (tree_graft the_dnum d [] temp_fn 
                            (TreeFile a0 dirfile0) (TStree dummy4 !!));
                  TSilist:= ilist';
                  TSfree:= (frees'_1, frees'_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; rewrite <- H5; eauto.
  eauto.
  
  assert (A: forall x dummy9, treeseq_pred (tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy9 dstbase dstname 
  x)
  ({|
  TStree := tree_graft the_dnum d [] temp_fn (TreeFile a0 dirfile0) (TStree dummy4 !!);
  TSilist := ilist';
  TSfree := (frees'_1, frees'_2) |}, []) ->
  tree_rep dummy1 dummy5 [temp_fn] srcinum dummy6 dummy9 dstbase dstname 
  x
  {|
  TStree := tree_graft the_dnum d [] temp_fn (TreeFile a0 dirfile0) (TStree dummy4 !!);
  TSilist := ilist';
  TSfree := (frees'_1, frees'_2) |}).
  unfold treeseq_pred; simpl; intros; auto.
  inversion H14; simpl in *; auto.
  
  apply A.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H15; auto.
  pred_apply; cancel.
  eauto.
  pred_apply; cancel.
  
  eapply H2.
  instantiate (1:= realcrash).
  intros m1 Hx; apply H5 in Hx; pred_apply; xcrash; eauto.
  or_l; cancel; eauto.
  xcrash; eauto.
  or_r; xcrash.
  eapply treeseq_in_ds_pushd.
  eauto.
  unfold tree_rep_latest.
  instantiate (2:= {| TStree:= (tree_graft the_dnum d [] temp_fn 
                            (TreeFile x0 dirfile0) (TStree dummy4 !!));
                  TSilist:= x2;
                  TSfree:= (x3_1, x3_2) |}).
  simpl; eauto.
  unfold treeseq_one_safe; simpl; rewrite <- H15; eauto.
  eauto.
  eapply treeseq_tree_rep_sync_after_create; eauto.
  pred_apply; cancel.
  replace ([temp_fn]) with (([]: list string)++[temp_fn])%list by auto.
  eapply dirents2mem2_graft_file_none; simpl; eauto.
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  rewrite H14; auto.
  pred_apply; cancel.
  eauto.
  
  eapply tree_names_distinct_d_in; eauto.
  apply latest_in_ds.
  Unshelve.
  all: repeat constructor.
  all: apply any.
Qed.

  Theorem atomic_cp_recover_ok_1 :
    {< Fm Ftop Ftree fsxp cs mscs ds sm ts srcpath file srcinum tinum dstfile (dstbase: list string) (dstname:string),
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts]]
    POST:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) (t, nil) ]]
    XCRASH:hm'
      (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs ts ds ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts ]])
       \/
      exists ts' ds' sm' mscs' dstfile',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' ts' ds' ]] *
      [[ treeseq_pred (tree_rep (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile') ts' ]] *
      [[ file_crash dstfile dstfile' ]]
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
    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
    eapply treeseq_in_ds_crash; eauto.

    (* other preconditions of lookup *)      
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_inum; eauto.
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_isdir; eauto.

    destruct a0.
    prestep. norm'l.

    eapply tree_pred_crash_find_subtree_root in H5 as Hroot; eauto.
    destruct Hroot.

    intuition; inv_option_eq; deex.
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name in Htc; eauto.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    unfold tree_with_tmp in Htc.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    eapply pimpl_apply in Htc.
    2: repeat rewrite flatmem_crash_xform_sep_star.
    2: repeat rewrite flatmem_crash_xform_file.
    2: reflexivity.
    destruct_lift Htc.

    2: distinct_names.

    safecancel.

    instantiate (pathname := []).
    simpl. reflexivity.

    simpl.
    pred_apply.
    cancel.

    prestep; norm'l.
    safecancel.

    eassumption.

    step.  (* return *)
    or_l. cancel. eapply pimpl_any.

    xcrash. or_r. cancel.
    xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.

    distinct_names.

    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.
(*     erewrite <- file_crash_data_length; eauto. *)
    eauto.
    eauto.

    step.
    or_r. repeat progress (xform_norm; safecancel).
    eassumption.

    rewrite latest_pushd. unfold treeseq_pred. constructor; [ | constructor ].
    unfold tree_rep_recover; simpl. intuition; eauto.
    distinct_names.
    left. unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.

    xcrash. or_r. cancel.
    xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    (* erewrite <- file_crash_data_length; eauto. *)

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    xcrash. or_r. cancel.
    xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    (* erewrite <- file_crash_data_length; eauto. *)
    eauto.

    or_r. cancel. xcrash.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    (* erewrite <- file_crash_data_length; eauto. *)

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    step.   (* lookup failed? *)
    right.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name_none in Htc; eauto.
    apply flatmem_crash_xform_or_dist in Htc; destruct Htc.

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_src in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      left. pred_apply.
      unfold tree_with_src. cancel.
    }

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_dst in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      right.
      unfold tree_with_dst. pred_apply.

      synced_file_eq. cancel.
    }

    distinct_names.

    (* crash condition *)
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.

    {
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        unfold tree_with_tmp in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.
        2: eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        left. pred_apply. unfold tree_with_tmp. synced_file_eq. cancel.
        (* erewrite <- file_crash_data_length; eauto. *)
      }

      denote flatmem_crash_xform as Htc.
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_src in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.
        2: eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. left. pred_apply. unfold tree_with_src. synced_file_eq. cancel.
      }

      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_dst in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        edestruct (dirfile_crash_exists dstfile).

        xcrash. or_r. cancel. xcrash.
        eassign ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts)), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. right. pred_apply. unfold tree_with_dst.
        synced_file_eq. synced_file_eq. cancel.
        eauto.
      }
    }

    cancel.
    xcrash. or_l.
    rewrite LOG.before_crash_idempred.
    cancel; auto.
    
  Grab Existential Variables.
    all: eauto.
    exact Mem.empty_mem.
  Qed.
  
  Lemma tree_pred_crash_find_name_root_single: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t t',
    tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
    tree_crash (TStree t) t' ->
    find_name [] t' = Some (the_dnum, true).
Proof.
  intros.
  eapply tree_crash_find_name_root; eauto.
  destruct H.
  destruct H1.
  destruct H2.
  destruct H2.
  unfold tree_with_tmp in *. 
  destruct H2.
  eapply tree_rep_find_name_root; eauto.
  pred_apply; cancel; eauto.
  
  destruct H2.
  unfold tree_with_src in *. 
  destruct H2.
  eapply tree_rep_find_name_root; eauto.
  pred_apply; cancel; eauto.
  
  destruct H2.
  unfold tree_with_dst in *. 
  eapply tree_rep_find_name_root; eauto.
  pred_apply; cancel; eauto.
Qed.

Lemma treeseq_in_ds_snd_length: forall Fm Ftop fsxp sm mscs t tl d dl, 
  treeseq_in_ds Fm Ftop fsxp sm mscs (t, tl) (d, dl) ->
  List.length tl = List.length dl.
Proof.
  unfold treeseq_in_ds; simpl; intros.
  destruct H.
  apply NEforall2_length in H; simpl in *; auto.
Qed.
  
Lemma tree_pred_crash_find_subtree_root_single: forall Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t t',
    tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
    tree_crash (TStree t) t' ->
    (exists elem, find_subtree [] t' = Some (TreeDir the_dnum elem)).
Proof.
  intros.
  eapply tree_crash_find_subtree_root; eauto.
  unfold tree_rep in H.
  intuition; eauto.

  destruct H2.
  unfold tree_with_tmp in *. 
  destruct H2.
  eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
  pred_apply; cancel.

  unfold tree_with_src in *. 
  destruct H3.
  eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
  pred_apply; cancel.

  unfold tree_with_dst in *. 
  destruct H3.
  eapply tree_rep_find_subtree_root with (Ftree := Ftree); eauto.
  pred_apply; cancel.
Qed.

  

Lemma treeseq_in_ds_crash_single: forall Fm Ftop fsxp d x t sm ms,
  BFILE.MSinitial ms ->
  (crash_xform Fm
    ✶ rep fsxp Ftop x (TSilist t)
        (TSfree t) (BFILE.ms_empty (MSLL ms)) sm)%pred (list2nmem d) ->
  treeseq_in_ds (crash_xform Fm) Ftop fsxp sm ms
      ({| TStree := x; TSilist := TSilist t; TSfree := TSfree t |}, []) 
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
    
Lemma treeseq_pred_tree_rep_dir2flatmem2_single : forall t Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile,
  tree_rep Ftree srcpath tmppath srcinum file tinum dstbase dstname dstfile t ->
    ((exists tfile', 
      tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile' dstbase dstname dstfile) \/
     (tree_with_src Ftree srcpath tmppath srcinum file dstbase dstname dstfile) \/
     (tree_with_dst Ftree srcpath tmppath srcinum file dstbase dstname))%pred
    (dir2flatmem2 (TStree t)).
Proof.
  unfold treeseq_pred, tree_rep; intros.
  intuition.
  - deex.
    pred_apply. cancel.
  - pred_apply; cancel.
  - pred_apply; cancel.
Qed.

Lemma add_to_list_not_in: forall d s t,
  ~In s (map fst d) -> add_to_list s t d = (d ++ [(s,t)])%list.
Proof.
  induction d; intros; simpl; auto.
  destruct a; simpl in *.
  destruct (string_dec s0 s).
  exfalso; auto.
  rewrite IHd; auto.
Qed.
  
Lemma tree_names_distinct_add_to_dir: forall ents tfn a df inum,
  ~In tfn (map fst ents) -> 
  tree_names_distinct (TreeDir inum ents) ->
  tree_names_distinct (add_to_dir tfn (TreeFile a df) (TreeDir inum ents)).
Proof.
  induction ents; intros; simpl; auto.
  apply TND_dir.
  simpl.
  apply Forall_forall; intros x Hf; destruct Hf; subst.
  apply TND_file.
  inversion H1.
  simpl.
  econstructor; auto.
  apply NoDup_nil.
  
  destruct a.
  destruct (string_dec s tfn); simpl in *; auto.
  exfalso; auto.
  inversion H0; subst; simpl in *.
  inversion H3; subst.
  inversion H4; subst.
  assert (A: tree_names_distinct (TreeDir inum ents)).
  apply TND_dir; eauto.
  assert (A0: ~In tfn (map fst ents)).
  auto.
  
  apply TND_dir; simpl.
  constructor; auto.
  specialize (IHents tfn a0 df inum).
  specialize (IHents A0 A).
  inversion IHents; subst; auto. 
  
  specialize (IHents tfn a0 df inum).
  specialize (IHents A0 A).
  inversion IHents; subst; auto. 
  constructor; auto.
  rewrite add_to_list_not_in.
  rewrite map_app; simpl.
  unfold not; intros .
  apply in_app_iff in H1.
  destruct H1; auto.
  inversion H1; subst; auto.
  auto.
Qed.

  Theorem atomic_cp_recover_ok_2 :
    {< Fm Ftop Ftree fsxp cs mscs ds sm srcpath file srcinum tinum tinum' dfile dstfile (dstbase: list string) (dstname:string) t ts',
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs (pushd t ts') ds ]] *
      [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]]
    POST:hm' RET:r
      [[ isError r ]] * any \/
      exists d sm' t mscs',
      [[ r = OK (mscs', fsxp) ]] *
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') sm' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' (t, nil) (d, nil) ]] *
      ([[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dstfile) (t, nil) ]] \/
       [[ treeseq_pred (tree_rep_recover (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file dstbase dstname dfile) (t, nil) ]])
    XCRASH:hm'
      (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' *
      [[ treeseq_in_ds Fm Ftop fsxp sm mscs (pushd t ts') ds ]] *
      [[ tree_rep Ftree srcpath [temp_fn] srcinum file tinum' dstbase dstname dfile t ]] *
      [[ treeseq_pred (tree_rep Ftree srcpath [temp_fn] srcinum file tinum dstbase dstname dstfile) ts' ]])
       \/
      exists ts' ds' sm' mscs' dstfile' tinum',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
      [[ treeseq_in_ds (crash_xform Fm) (BFileCrash.flist_crash_xform Ftop) fsxp sm' mscs' ts' ds' ]] *
      [[ treeseq_pred (tree_rep (flatmem_crash_xform Ftree) srcpath [temp_fn] srcinum file tinum' dstbase dstname dstfile') ts' ]] *
      ([[ file_crash dstfile dstfile' ]] \/ [[ file_crash dfile dstfile' ]])
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
    match goal with H: context [lift_empty] |- _ => destruct_lift H end.
    
    (* Split between last tree and rest *)
    unfold pushd in H6.
    apply treeseq_in_ds_snd_length in H7 as Hx.
    unfold LogReplay.diskstate in *; rewrite <- Hx in H12; simpl in H12.
    inversion H12.
    
    (* Last Tree *)
    rewrite nthd_pushd_latest' in *; auto.

    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)).
    eapply treeseq_in_ds_crash_single; eauto.
    eapply tree_pred_crash_find_name_root_single in H6 as Hroot; eauto.
    eapply find_name_dirtree_inum; simpl; eauto.
    eapply tree_pred_crash_find_name_root_single in H6 as Hroot; eauto.
    eapply find_name_dirtree_isdir; simpl; eauto.
    
    
    destruct a0.
    prestep. norm'l.
    
    eapply tree_pred_crash_find_name_root_single in H6 as Hroot; eauto.
    destruct Hroot.

    intuition; inv_option_eq; deex.
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.

    2: eapply treeseq_pred_tree_rep_dir2flatmem2_single; eassumption.
    eapply tree_with_tmp_find_name in Htc; eauto.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    unfold tree_with_tmp in Htc.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    eapply pimpl_apply in Htc.
    2: repeat rewrite flatmem_crash_xform_sep_star.
    2: repeat rewrite flatmem_crash_xform_file.
    2: reflexivity.
    destruct_lift Htc.

    2: distinct_names.
    
    repeat rewrite flatmem_crash_xform_dir in H4.
    repeat rewrite flatmem_crash_xform_lift_empty in H4.
    apply sep_star_assoc in H4.
    apply sep_star_comm in H4.
    apply sep_star_assoc in H4.
    apply sep_star_comm in H4.
    apply sep_star_assoc in H4.
    apply tree_rep_find_subtree_root in H4 as Hpath.
    destruct Hpath.
    simpl in H8. 
    
    safecancel.

    instantiate (pathname := []).
    simpl; eauto.

    simpl.
    pred_apply.
    cancel.

    prestep; norm'l.
    safecancel.

    eassumption.
    
    step.  (* return *)
    or_l. cancel. eapply pimpl_any.

    xcrash. or_r. cancel.
    xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor; simpl; eauto.
    2: apply Forall_nil.
    unfold tree_rep; simpl.
    intuition; eauto.

    distinct_names.

    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.
    eauto.
    eauto.
    

    step.
    or_r. repeat progress (xform_norm; safecancel).
    rewrite sep_star_or_distr; or_r; repeat progress (xform_norm; safecancel).
    all: eauto.

    rewrite pushd_latest; unfold treeseq_pred. constructor; [ | constructor ].
    unfold tree_rep_recover; simpl. intuition; eauto.
    distinct_names.
    left. unfold tree_with_src.
    pred_apply' H24.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    xcrash. or_r. cancel.
    xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply' H24.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    xcrash. or_r. cancel.
    xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    or_r. cancel. xcrash.
    or_r; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply' H8.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.
    eapply rep_tree_names_distinct; eauto.

    step.   (* lookup failed? *)
    right.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.

    2: eapply treeseq_pred_tree_rep_dir2flatmem2_single; eassumption.
    eapply tree_with_tmp_find_name_none in Htc; eauto.
    apply flatmem_crash_xform_or_dist in Htc; destruct Htc.

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_src in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_r; cancel.
      2:eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      left. pred_apply.
      unfold tree_with_src. cancel.
    }

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_dst in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_r; cancel.
      2:eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      right.
      unfold tree_with_dst. pred_apply.

      synced_file_eq. cancel.
    }

    distinct_names.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2_single; eassumption.

    {
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        unfold tree_with_tmp in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_r; cancel; eauto.
        eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash_single; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        left. pred_apply. unfold tree_with_tmp. synced_file_eq. cancel.
      }

      denote flatmem_crash_xform as Htc.
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_src in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_r; cancel; eauto.
        eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash_single; eauto.


        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. left. pred_apply. unfold tree_with_src. synced_file_eq. cancel.
      }

      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_dst in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        edestruct (dirfile_crash_exists dfile).

        xcrash. or_r. cancel. xcrash.
        or_r; cancel; eauto.
        eassign ((mk_tree x (TSilist t) (TSfree t), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash_single; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. right. pred_apply. unfold tree_with_dst.
        synced_file_eq. synced_file_eq. cancel.
      }
    }

    (* Other Trees *)      
    
    rewrite nthd_pushd' in *; auto.

    safecancel.
    eassign ((d, @nil (list valuset))).
    cancel.
    eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
    eapply treeseq_in_ds_crash; eauto.
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_inum; simpl; eauto.
    eapply tree_pred_crash_find_name_root in H5 as Hroot; eauto.
    eapply find_name_dirtree_isdir; simpl; eauto.

    destruct a0.
    prestep. norm'l.
    
    eapply tree_pred_crash_find_subtree_root in H5 as Hroot; eauto.
    destruct Hroot.

    intuition; inv_option_eq; deex.
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name in Htc; eauto.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    unfold tree_with_tmp in Htc.
    apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
    denote flatmem_crash_xform as Htc.
    eapply pimpl_apply in Htc.
    2: repeat rewrite flatmem_crash_xform_sep_star.
    2: repeat rewrite flatmem_crash_xform_file.
    2: reflexivity.
    destruct_lift Htc.

    2: distinct_names.

    safecancel.

    instantiate (pathname := []).
    simpl. reflexivity.

    simpl.
    pred_apply.
    cancel.

    prestep; norm'l.
    safecancel.

    eassumption.
    
    step.  (* return *)
    or_l. cancel. eapply pimpl_any.

    xcrash. or_r. cancel.
    xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.

    distinct_names.

    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.
    eauto.
    eauto.

    step.
    or_r. repeat progress (xform_norm; safecancel).
    rewrite sep_star_or_distr; or_l; cancel.
    all: eauto.

    rewrite latest_pushd. unfold treeseq_pred. constructor; [ | constructor ].
    unfold tree_rep_recover; simpl. intuition; eauto.
    distinct_names.
    left. unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.

    synced_file_eq. cancel.

    xcrash. or_r. cancel.
    xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    xcrash. or_r. cancel.
    xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    eexists.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    or_r. cancel. xcrash.
    or_l; cancel; eauto.
    eassumption.

    unfold treeseq_pred. constructor.
    2: constructor.
    3: constructor.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    left.
    unfold tree_with_tmp.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.

    unfold tree_rep; simpl.
    intuition; eauto.
    distinct_names.
    right. left.
    unfold tree_with_src.
    pred_apply.
    repeat rewrite flatmem_crash_xform_dir.
    repeat rewrite flatmem_crash_xform_lift_empty.
    synced_file_eq. cancel.
    eauto.

    step.   (* lookup failed? *)
    right.

    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.
    eapply tree_with_tmp_find_name_none in Htc; eauto.
    apply flatmem_crash_xform_or_dist in Htc; destruct Htc.

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_src in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_l; cancel.
      2: eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      left. pred_apply.
      unfold tree_with_src. cancel.
    }

    {
      denote flatmem_crash_xform as Htc.
      unfold tree_with_dst in Htc.
      apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
      denote flatmem_crash_xform as Htc.
      eapply pimpl_apply in Htc.
      2: repeat rewrite flatmem_crash_xform_sep_star.
      2: repeat rewrite flatmem_crash_xform_nothing.
      2: repeat rewrite flatmem_crash_xform_file.
      2: repeat rewrite flatmem_crash_xform_dir.
      2: repeat rewrite flatmem_crash_xform_lift_empty.
      2: reflexivity.
      destruct_lift Htc.

      pred_apply. synced_file_eq. cancel.
      rewrite sep_star_or_distr; or_l; cancel.
      2: eassumption.

      unfold treeseq_pred. constructor. 2: constructor.
      unfold tree_rep_recover. intuition; eauto.
      distinct_names.
      simpl.
      right.
      unfold tree_with_dst. pred_apply.

      synced_file_eq. cancel.
    }

    distinct_names.

    (* crash condition *)
    denote! (tree_crash _ _) as Htc.
    eapply tree_crash_flatmem_crash_xform in Htc.
    2: eapply treeseq_pred_nthd; eauto.
    2: eapply treeseq_pred_tree_rep_dir2flatmem2; eassumption.

    {
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        unfold tree_with_tmp in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_l; cancel; eauto.
        eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        left. pred_apply. unfold tree_with_tmp. synced_file_eq. cancel.
      }

      denote flatmem_crash_xform as Htc.
      apply flatmem_crash_xform_or_dist in Htc; destruct Htc.
      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_src in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        xcrash. or_r. cancel. xcrash.
        or_l; cancel; eauto.
        eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. left. pred_apply. unfold tree_with_src. synced_file_eq. cancel.
      }

      {
        denote flatmem_crash_xform as Htc.
        unfold tree_with_dst in Htc.
        apply flatmem_crash_xform_exists in Htc; destruct_lift Htc.
        denote flatmem_crash_xform as Htc.
        eapply pimpl_apply in Htc.
        2: repeat rewrite flatmem_crash_xform_sep_star.
        2: repeat rewrite flatmem_crash_xform_nothing.
        2: repeat rewrite flatmem_crash_xform_file.
        2: repeat rewrite flatmem_crash_xform_dir.
        2: repeat rewrite flatmem_crash_xform_lift_empty.
        2: reflexivity.
        destruct_lift Htc.

        edestruct (dirfile_crash_exists dstfile).

        xcrash. or_r. cancel. xcrash.
        or_l; cancel; eauto.
        eassign ((mk_tree x (TSilist (nthd n ts')) (TSfree (nthd n ts')), @nil treeseq_one)); simpl in *.
        eapply treeseq_in_ds_crash; eauto.

        unfold treeseq_pred, tree_rep; intuition.
        constructor. 2: constructor.
        intuition; eauto. distinct_names.

        right. right. pred_apply. unfold tree_with_dst.
        synced_file_eq. synced_file_eq. cancel.
      }
    }

    cancel.
    xcrash. or_l.
    rewrite LOG.before_crash_idempred.
    cancel; auto.
    
  Grab Existential Variables.
    all: eauto.
    exact Mem.empty_mem.
Qed.

End ATOMICCP.
