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
Require Import TreeCrash.
Require Import TreeSeq.
Require Import DirSep.

Import DIRTREE.
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
    If (bool_dec ok true) {
      let^ (mscs, ok) <- copydata fsxp src_inum tinum mscs;
      Ret ^(mscs, ok)
    } else {
      Ret ^(mscs, ok)
    }.

  Definition copy_and_rename fsxp src_inum tinum (dstbase:list string) (dstname:string) mscs :=
    let^ (mscs, ok) <- copy2temp fsxp src_inum tinum mscs;
    match ok with
      | false =>
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        (* Just for a simpler spec: the state is always (d, nil) after this function *)
        Ret ^(mscs, false)
      | true =>
        let^ (mscs, ok1) <- AFS.rename fsxp the_dnum [] temp_fn dstbase dstname mscs;
        let^ (mscs) <- AFS.tree_sync fsxp mscs;
        Ret ^(mscs, ok1)
    end.

  Definition atomic_cp fsxp src_inum dstbase dstname mscs :=
    let^ (mscs, maybe_tinum) <- AFS.create fsxp the_dnum temp_fn mscs;
    match maybe_tinum with
      | None => Ret ^(mscs, false)
      | Some tinum =>
        let^ (mscs, ok) <- copy_and_rename fsxp src_inum tinum dstbase dstname mscs;
        Ret ^(mscs, ok)
    end.

  (** recovery programs **)

  (* top-level recovery function: call AFS recover and then atomic_cp's recovery *)
  Definition atomic_cp_recover :=
    let^ (mscs, fsxp) <- AFS.recover cachesize;
    let^ (mscs, maybe_src_inum) <- AFS.lookup fsxp the_dnum [temp_fn] mscs;
    match maybe_src_inum with
    | None => Ret ^(mscs, fsxp)
    | Some (src_inum, isdir) =>
      let^ (mscs, ok) <- AFS.delete fsxp the_dnum temp_fn mscs;
      let^ (mscs) <- AFS.tree_sync fsxp mscs;
      Ret ^(mscs, fsxp)
    end.

  (** Specs and proofs **)

  Opaque LOG.idempred.
  Opaque crash_xform.

  Ltac xcrash_norm :=  repeat (xform_norm; cancel).
  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.


  Theorem copydata_ok : forall fsxp src_inum tmppath tinum mscs,
    {< ds ts Fm Ftop Ftree srcpath file tfile v0 t0,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_upd_safe tmppath Off0 (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, tfile))%pred
            (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ BFILE.BFData file ::: (Off0 |-> v0) ]]] *
      [[[ BFILE.BFData tfile ::: (Off0 |-> t0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
        (([[ r = false ]] *
          exists tfile',
            [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, tfile'))%pred (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = true ]] *
            [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, (BFILE.synced_file file)))%pred (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      exists newds ts',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushdlist newds ds) hm' *
      [[ newds <> nil -> treeseq_in_ds Fm Ftop fsxp mscs ts' (list2nelist ds newds) ]] *
      [[ newds <> nil -> NEforall (fun t => exists tfile', (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, tfile'))%pred (dir2flatmem2 (TStree t)))%type ts' ]]
     >} copydata fsxp src_inum tinum mscs.
  Proof.
    unfold copydata; intros.
    step.
    eapply pimpl_sep_star_split_l; eauto.
    step.
    erewrite treeseq_in_ds_eq; eauto.
    eapply pimpl_sep_star_split_l; eauto.
    pred_apply.
    cancel.
    step.
    erewrite treeseq_in_ds_eq; eauto.
    step.
    step.

    safestep.  (* step picks the wrong ts. *)
    2: erewrite treeseq_in_ds_eq; eauto.
    or_l.
    cancel.
    or_r.
    cancel.
    2: eassumption.
    pred_apply.
    cancel.
    unfold BFILE.synced_file.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (BFILE.BFData file)) by eauto.
    erewrite ptsto_0_list2nmem_mem_eq with (d := (BFILE.BFData f')) by eauto.
    simpl.
    cancel.

    (* crashed during setattr  *)
    xcrash.
    or_r.
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    pred_apply.
    cancel.

    (* crash during sync *)
    xcrash.
    or_r.
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    pred_apply.
    cancel.
  
    (* crash during upd *)
    xcrash.
    or_r.
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    admit. (* is x ts? [update_fblock_d_ok] promises too little? *)

    xcrash.
    xcrash.
  Admitted.

  Hint Extern 1 ({{_}} Bind (copydata _ _ _ _) _) => apply copydata_ok : prog.

  Theorem copy2temp_ok : forall fsxp src_inum tinum mscs,
    {< Fm Ftop Ftree ds ts tmppath srcpath file tfile v0,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_grow_safe tmppath Off0 (MSAlloc mscs) ts !!) ts ]] *
      [[ treeseq_pred (treeseq_upd_safe tmppath Off0 (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, tfile))%pred
            (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ BFILE.BFData file ::: (Off0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ MSAlloc mscs = MSAlloc mscs' ]] *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
        (([[ r = false ]] *
          exists tfile',
            [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, tfile'))%pred (dir2flatmem2 (TStree ts'!!)) ]])
         \/ ([[ r = true ]] *
            [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, (BFILE.synced_file file)))%pred (dir2flatmem2 (TStree ts'!!)) ]]))
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      (exists ds' ts' tfile',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
        [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, tfile'))%pred (dir2flatmem2 (TStree ts'!!)) ]])
    >} copy2temp fsxp src_inum tinum mscs.
  Proof.
    unfold copy2temp; intros.
    step.
    step.
    step.
    step.
    erewrite treeseq_in_ds_eq; eauto.
    step.

    instantiate (1 := ($ (0), [])).
    admit. (* XXX need list2nmem_setlen? *)

    step.
    xcrash.
    or_r.
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    pred_apply.
    cancel.

    xcrash.
    or_r.
    xcrash.
    erewrite treeseq_in_ds_eq; eauto.
    pred_apply.
    cancel.

    step.
    xcrash.
    or_l.
    eauto.
  Admitted.

  Hint Extern 1 ({{_}} Bind (copy2temp _ _ _ _) _) => apply copy2temp_ok : prog.

  Theorem copy_and_rename_ok : forall fsxp src_inum tinum (dstbase: list string) (dstname:string) mscs,
    {< Fm Ftop Ftree ds ts tmppath srcpath file tfile v0 dstinum dstfile,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ treeseq_pred (treeseq_grow_safe tmppath Off0 (MSAlloc mscs) ts !!) ts ]] *
      [[ treeseq_pred (treeseq_upd_safe tmppath Off0 (MSAlloc mscs) (ts !!)) ts ]] *
      [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some(tinum, tfile) *
          ((dstbase++[dstname])%list |-> Some (dstinum, dstfile)))%pred (dir2flatmem2 (TStree ts!!)) ]] *
      [[[ BFILE.BFData file ::: (Off0 |-> v0) ]]]
    POST:hm' RET:^(mscs', r)
      exists ds' ts',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ treeseq_in_ds Fm Ftop fsxp mscs' ts' ds' ]] *
      (([[r = false ]] *
        (exists f',
          [[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, f') *
              (dstbase ++ [dstname])%list |-> Some (dstinum, dstfile))%pred (dir2flatmem2 (TStree ts'!!)) ]])  \/
       ([[r = true ]] *
          [[ (Ftree * srcpath |-> Some (src_inum, file) * (dstbase++[dstname])%list |-> Some (tinum, (BFILE.synced_file file)) *
              tmppath |-> None)%pred (dir2flatmem2 (TStree ts'!!)) ]]
       )))
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      (exists ds' ts' f',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds' hm' *
        [[ treeseq_in_ds Fm Ftop fsxp mscs ts' ds' ]] *
        (([[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> None *
               (dstbase++[dstname])%list |-> Some (tinum, (BFILE.synced_file file)))%pred (dir2flatmem2 (TStree ts'!!)) ]]) \/
         ([[ (Ftree * srcpath |-> Some (src_inum, file) * tmppath |-> Some (tinum, f') *
              (dstbase ++ [dstname])%list |-> Some (dstinum, dstfile))%pred (dir2flatmem2 (TStree ts'!!)) ]]))
      )
    >} copy_and_rename fsxp src_inum tinum dstbase dstname mscs.
  Proof.
    unfold copy_and_rename; intros.
    step.
    instantiate (1 := srcpath).
    cancel.
    step.
    instantiate (2 := []).
    eapply sep_star_split_l in H11 as H11'.
    destruct H11'.
    admit.  (* implied by H6 *)
    admit.
    step.
    erewrite treeseq_in_ds_eq; eauto.
    step.

    xcrash.
    or_r.
    xcrash.
    2: erewrite treeseq_in_ds_eq; eauto.
    or_r.
    cancel.

    step.
    xcrash.
    or_r.
    xcrash.
    2: erewrite treeseq_in_ds_eq; eauto.
    or_l.
    cancel.

    xcrash.
    or_r.
    xcrash.
    or_r.
    cancel.
    2: erewrite treeseq_in_ds_eq; eauto.
    pred_apply.
    cancel.

    step.

    xcrash.
    or_r.
    xcrash.
    or_r.
    2: erewrite treeseq_in_ds_eq; eauto.
    cancel.

    xcrash.
    or_r.
    xcrash.
    2: erewrite treeseq_in_ds_eq; eauto.
    or_r.
    cancel.
  Admitted.

  Hint Extern 1 ({{_}} Bind (copy_and_rename _ _ _ _ _ _) _) => apply copy_and_rename_ok : prog.


  (* specs for copy_and_rename_cleanup and atomic_cp *)

Lemma rep_tree_crash: forall Fm fsxp Ftop d t ilist frees d',
  (Fm * rep fsxp Ftop t ilist frees)%pred (list2nmem d) ->
  crash_xform (diskIs (list2nmem d)) (list2nmem d') ->
  (exists t', [[ tree_crash t t' ]] * (crash_xform Fm) * rep fsxp Ftop t' ilist frees)%pred (list2nmem d').
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

Lemma treeseq_tree_crash_exists: forall Fm Ftop fsxp mscs ts ds n d,
  let t := (nthd n ts) in
  treeseq_in_ds Fm Ftop fsxp mscs ts ds ->
  crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
  (exists t', [[ tree_crash (TStree t) t' ]] *  (crash_xform Fm) * rep fsxp Ftop t' (TSilist t) (TSfree t))%pred (list2nmem d).
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
  tree_rep Fm Ftop fsxp t (list2nmem d) ->
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

  Definition tree_with_tmp Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum tfile dstbase dstname dstinum dstfile:  @pred _ (list_eq_dec string_dec) _ :=
   (Ftree * srcpath |-> Some (srcinum, file) * tmppath |-> Some (tinum, tfile) *
         (dstbase ++ [dstname])%list |-> Some (dstinum, dstfile))%pred.

  Definition tree_with_dst Ftree (srcpath: list string) tmppath (srcinum:addr) (file:BFILE.bfile) tinum  dstbase dstname :  @pred _ (list_eq_dec string_dec) _ :=
   (Ftree * srcpath |-> Some (srcinum, file) * tmppath |-> None *
         (dstbase ++ [dstname])%list |-> Some (tinum, (BFILE.synced_file file)))%pred.

  Theorem atomic_cp_recover_ok :
    {< Fm Ftop Ftree fsxp cs mscs ds ts tmppath srcpath file srcinum dstinum tinum dstfile (dstbase: list string) (dstname:string),
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]] *
      [[ NEforall (fun t => exists tfile,
        find_name [] (TStree t) = Some (the_dnum, true) /\
        ((tree_with_tmp Ftree srcpath tmppath srcinum file tinum tfile dstbase dstname dstinum dstfile (dir2flatmem2 (TStree t))) \/
        (tree_with_dst Ftree srcpath tmppath srcinum file tinum dstbase dstname (dir2flatmem2 (TStree t)))))%type ts ]]
    POST:hm' RET:^(mscs', fsxp')
      [[ fsxp' = fsxp ]] * exists n d t,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs' (t, nil) (d, nil) ]] *
      [[ forall Ftree f,
         (Ftree * tmppath |-> f)%pred (dir2flatmem2 (TStree (nthd n ts))) ->
         (Ftree * tmppath |-> None)%pred (dir2flatmem2 (TStree t)) ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists n d t,
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs (t, nil) (d, nil) ]] *
      [[ forall Ftree f,
         (Ftree * tmppath |-> f)%pred (dir2flatmem2 (TStree (nthd n ts))) ->
         (Ftree * tmppath |-> None)%pred (dir2flatmem2 (TStree t)) ]]
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
    instantiate (ts0 := ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts))), [])).

    eapply tree_rep_treeseq; eauto.



    eapply NEforall_d_in in Tpred as Tpred'.
    destruct Tpred'.
    2: eapply nthd_in_ds with (n := n).
    intuition.
 
    simpl.

Lemma tree_crash_the_dnum: forall t t',
  tree_crash t t' ->
  find_name [] t = Some (the_dnum, true) ->
  find_name [] t' = Some (the_dnum, true).
Proof.
  intros.
  destruct t.
  - unfold find_name in H0; subst; simpl.
    destruct (find_subtree [] (TreeFile n b)).
    destruct d.
    exfalso; congruence.
    inversion H0.
    subst; simpl.
    admit.
    exfalso; congruence.
  - destruct t'.
    unfold find_name in H0.
    destruct (find_subtree [] (TreeDir n l)).
    destruct d.
    inversion H0.
    inversion H0.
    subst; simpl.
    exfalso.
    inversion H.
    congruence.
    inversion H.
    subst; simpl; eauto.
Qed.

  destruct tree_crash in H.

    admit. (* follows from H6 *)
    admit. (* follows from H6 *)

    step.

    instantiate (ts0 := ((mk_tree x (TSilist (nthd n ts)) (TSfree (nthd n ts))), [])).
    eapply tree_rep_treeseq; eauto.
    instantiate (pathname := []).
    admit.  (* follows from H6 *)

    admit.  (* need new lemma *)

    step.


    eapply tree_rep_treeseq.



    (* XXX looks proming ....*)
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
Lemma possible_crash_flist_crash: forall F bxps ixp d d' ilist frees flist,
  (F * (BFILE.rep bxps ixp flist ilist frees))%pred (list2nmem d) ->
  possible_crash (list2nmem d) (list2nmem d') ->
  exists flist', BFILE.flist_crash flist flist'.
Proof.
  intros.
  eapply flist_crash_exists.
Qed.
