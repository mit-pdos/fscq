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

  Theorem atomic_cp_recover_ok :
    {< Fm Ftop fsxp cs mscs ds ts tmppath,
    PRE:hm
      LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm *
      [[ treeseq_in_ds Fm Ftop fsxp mscs ts ds ]]
    POST:hm' RET:^(mscs', fsxp')
      [[ fsxp' = fsxp ]] * exists n d t,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs') hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs' (t, nil) (d, nil) ]] *
      [[ forall Ftree f,
         (Ftree * tmppath |-> f)%pred (dir2flatmem2 (TStree (nthd n ts))) ->
         (Ftree * tmppath |-> None) (dir2flatmem2 (TStree t)) ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists n d t,
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) hm' *
      [[ treeseq_in_ds Fm Ftop fsxp mscs (t, nil) (d, nil) ]] *
      [[ forall Ftree f,
         (Ftree * tmppath |-> f)%pred (dir2flatmem2 (TStree (nthd n ts))) ->
         (Ftree * tmppath |-> None) (dir2flatmem2 (TStree t)) ]]
    >} atomic_cp_recover.
  Proof.
    unfold atomic_cp_recover; intros.
    prestep. norml.  (* XXX slow! *)
    safecancel.
    step.
    Focus 4.
    destruct a1.
    step.
    (* XXX looks proming ....*)
  Admitted.

End ATOMICCP.
