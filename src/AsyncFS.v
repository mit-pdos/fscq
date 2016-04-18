Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import Omega.
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
Require Import NEList.

Set Implicit Arguments.
Import ListNotations.


Module AFS.

  Parameter cachesize : nat.

  (* Programs *)

  Definition recover {T} rx : prog T :=
    cs <- BUFCACHE.init_recover 10;
    let^ (cs, fsxp) <- SB.load cs;
    mscs <- LOG.recover (FSXPLog fsxp) cs;
    rx ^(mscs, fsxp).

  Definition file_get_attr T fsxp inum mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
      mscs <- LOG.commit_ro (FSXPLog fsxp) mscs;
        rx ^(mscs, attr).

  Definition file_get_sz T fsxp inum mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
      mscs <- LOG.commit_ro (FSXPLog fsxp) mscs;
        rx ^(mscs, INODE.ABytes attr).

  Definition file_set_sz T fsxp inum sz mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    mscs <- DIRTREE.updattr fsxp inum (INODE.UBytes sz) mscs;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
      rx ^(mscs, ok).

  Definition read_fblock T fsxp inum off mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, b) <- DIRTREE.read fsxp inum off mscs;
      mscs <- LOG.commit_ro (FSXPLog fsxp) mscs;
        rx ^(mscs, b).

  Definition file_truncate T fsxp inum sz ms rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) ms;
    let^ (ms, ok) <- BFILE.truncate (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum sz ms;
    If (bool_dec ok false) {
      ms <- LOG.abort (FSXPLog fsxp) ms;
      rx ^(ms, false)
    } else {
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) ms;
      rx ^(ms, ok)
    }.

  (* update an existing block directly.  XXX dwrite happens to sync metadata. *)
  Definition update_fblock_d T fsxp inum off v ms rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) ms;
    ms <- BFILE.dwrite (FSXPLog fsxp) (FSXPInode fsxp) inum off v ms;
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;
    rx ms.

  (* sync only data blocks of a file. *)
  Definition file_sync T fsxp inum ms rx : prog T :=
    ms <- BFILE.datasync (FSXPLog fsxp) (FSXPInode fsxp) inum ms;
    rx ms.

  Definition readdir T fsxp dnum mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, files) <- SDIR.readdir (FSXPLog fsxp) (FSXPInode fsxp) dnum mscs;
      mscs <- LOG.commit_ro (FSXPLog fsxp) mscs;
        rx ^(mscs, files).

  Definition create T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
      match oi with
        | None =>
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
            rx ^(mscs, None)
        | Some inum =>
          let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
            match ok with
              | true => rx ^(mscs, Some inum)
              | false => rx ^(mscs, None)
            end
             end.

  Definition mksock T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
      match oi with
        | None =>
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
            rx ^(mscs, None)
        | Some inum =>
          mscs <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum
               (INODE.UType $1) mscs;
            let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
              match ok with
                | true => rx ^(mscs, Some inum)
                | false => rx ^(mscs, None)
              end
               end.

  Definition mkdir T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, oi) <- DIRTREE.mkdir fsxp dnum name mscs;
      match oi with
        | None =>
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
            rx ^(mscs, None)
        | Some inum =>
          let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
            match ok with
              | true => rx ^(mscs, Some inum)
              | false => rx ^(mscs, None)
            end
      end.

  Definition delete T fsxp dnum name mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, ok) <- DIRTREE.delete fsxp dnum name mscs;
      If (bool_dec ok true) {
           let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
              rx ^(mscs, ok)
         } else {
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      rx ^(mscs, false)
    }.

  Definition lookup T fsxp dnum names mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, r) <- DIRTREE.namei fsxp dnum names mscs;
      mscs <- LOG.commit_ro (FSXPLog fsxp) mscs;
        rx ^(mscs, r).

  Definition rename T fsxp dnum srcpath srcname dstpath dstname mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname mscs;
      If (bool_dec r true) {
           let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
              rx ^(mscs, ok)
         } else {
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      rx ^(mscs, false)
    }.

  (* sync directory tree; will flush all outstanding changes to tree (but not dupdates to files) *)
  Definition tree_sync T fsxp mscs rx : prog T :=
    mscs <- GLog.flushall fsxp mscs;
    rx mscs.

(*

  Definition statfs T fsxp mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
      let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
          rx ^(mscs, free_blocks, free_inodes).
*)

  (* Recover theorems *)

  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _) (LOG.rep_inner _ _ _)) => constructor : okToUnify.

  Theorem recover_ok :
    {< fsxp cs ds,
     PRE
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs
     POST RET:^(ms, fsxp')
       [[ fsxp' = fsxp ]] * exists d n, [[ n <= length (snd ds) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) ms *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     CRASH exists cs',
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs'
     >} recover.
  Proof.
    unfold recover, LOG.after_crash; intros.
    prestep. norm. cancel. intuition; eauto.
    prestep. norm. cancel. intuition; eauto.
    pred_apply; cancel.

    prestep.
    unfold LOG.after_crash; norm. cancel.
    intuition simpl.
    pred_apply; norm. cancel.
    intuition simpl; eauto.

    safestep; eauto.
    subst; pimpl_crash; eauto.

    subst; pimpl_crash. norm; try tauto. cancel.
    intuition; pred_apply. norm. cancel.
    intuition eauto.

    subst; pimpl_crash. norm; try tauto. cancel.
    intuition; pred_apply. norm. cancel.
    intuition eauto.
  Qed.

  Ltac recover_ro_ok := intros;
    repeat match goal with
      | [ |- forall_helper _ ] => idtac "forall"; unfold forall_helper; intros; eexists; intros
      | [ |- corr3 ?pre' _ _ ] => idtac "corr3 pre"; eapply corr3_from_corr2_rx; eauto with prog
      | [ |- corr3 _ _ _ ] => idtac "corr3"; eapply pimpl_ok3; intros
      | [ |- corr2 _ _ ] => idtac "corr2"; step
      | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
      | [ H: diskIs _ _ |- _ ] => idtac "unfold"; unfold diskIs in *
      | [ |- pimpl (crash_xform _) _ ] => idtac "crash_xform"; progress autorewrite with crash_xform
    end.

  Hint Extern 0 (okToUnify (LOG.idempred _ _ _) (LOG.idempred _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (LOG.after_crash _ _ _ _) (LOG.after_crash _ _ _ _)) => constructor : okToUnify.


(*
  Inductive tree_crash : tree -> tree -> Prop :=
    | TreeCrashFile : forall f1 f2,
      possible_crash (FData (list2nmem f1)) (FData (list2nmem f2)) ->
      tree_crash (TFile f1) (TFile f2)
    | TreeCrashDir : forall d1 d2,
      (forall name, tree_crash (Map.find name d1) (Map.find name d2)) ->
      tree_crash (TDir d1) (TDir d2).

  Lemma tree_crash_xform : forall t1 t2,
    tree_crash t1 t2 ->
    crash_xform (DIRTREE.rep t1) =p=> DIRTREE.rep t2.
*)
  


  (* Specs and proofs *)

  Theorem file_getattr_ok : forall fsxp inum mscs,
  {< ds pathname Fm Ftop tree f,
  PRE    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs  *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
         [[ r = BFILE.BFAttr f ]]
  CRASH LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds
  >} file_get_attr fsxp inum mscs.
  Proof.
    unfold file_get_attr; intros.
    step.
    step.
    eapply pimpl_ok2.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    subst; pimpl_crash; cancel.
    rewrite LOG.notxn_idempred; cancel.
    rewrite LOG.intact_idempred; cancel.
    rewrite LOG.notxn_idempred; cancel.
  Qed.

  Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {<< ds pathname Fm Ftop tree f,
  PRE    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs  *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
         [[ r = BFILE.BFAttr f ]]
  REC RET:^(mscs, fsxp)
        exists cs, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs
  >>} file_get_attr fsxp inum mscs >> recover.
  Proof.
    unfold forall_helper.
    intros; eexists; intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2_rx.
    eapply file_getattr_ok.
    eapply recover_ok.
    cancel.
    eauto.
    step.
    eapply pimpl_refl.
    xform_norm.
    rewrite LOG.idempred_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    eapply LOG.notxn_after_crash_diskIs; eauto.

    cancel.
    rewrite LOG.after_crash_idempred.
    destruct v; auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.


  Theorem file_getattr_ok_strict : forall fsxp inum mscs,
  {< ds pathname Fm Ftop tree f,
  PRE    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs  *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
         [[ r = BFILE.BFAttr f ]]
  CRASH  LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds
  >} file_get_attr fsxp inum mscs.
  Proof.
    unfold file_get_attr; intros.
    step.
    step.
    eapply pimpl_ok2.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    subst; pimpl_crash; cancel.
    apply LOG.notxn_intact.
    apply LOG.notxn_intact.
  Qed.


  Theorem file_getattr_recover_ok_strict : forall fsxp inum mscs,
  {<< ds pathname Fm Ftop tree f,
  PRE    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs  *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
         [[ r = BFILE.BFAttr f ]]
  REC RET:^(mscs, fsxp)
         exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs *
         [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
  >>} file_get_attr fsxp inum mscs >> recover.
  Proof.
    unfold forall_helper.
    intros; eexists; intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2_rx.
    eapply file_getattr_ok_strict.
    eapply recover_ok.
    cancel.
    eauto.
    step.
    eassign ( LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    cancel; cancel.

    xform_norm.
    recover_ro_ok.
    rewrite LOG.crash_xform_intact.
    xform_norm.
    rewrite SB.crash_xform_rep.

    cancel.
    rewrite LOG.notxn_after_crash_diskIs. cancel.
    rewrite nthd_0; eauto. omega.

    safestep; subst.
    eassign d0; eauto.
    pred_apply; instantiate (1 := nil).
    replace n with 0 in *.
    rewrite nthd_0; simpl; auto.
    simpl in *; omega.

    cancel; cancel.
    rewrite LOG.after_crash_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    cancel; cancel.
  Qed.

  Theorem read_fblock_ok : forall fsxp inum off mscs,
    {< ds Fm Ftop tree pathname f Fd vs,
    PRE    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
           [[ r = fst vs ]]
    CRASH  LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds
    >} read_fblock fsxp inum off mscs.
  Proof.
    unfold read_fblock; intros.
    step.
    step.
    eapply pimpl_ok2.
    apply LOG.commit_ro_ok.
    cancel.
    step.
    subst; pimpl_crash; cancel.
    apply LOG.notxn_intact.
    apply LOG.notxn_intact.
  Qed.


  Hint Extern 1 ({{_}} progseq (read_fblock _ _ _ _) _) => apply read_fblock_ok : prog.

  Theorem read_fblock_recover_ok : forall fsxp inum off mscs,
    {<< ds Fm Ftop tree pathname f Fd vs,
    PRE    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (SB.rep  fsxp) (LOG.NoTxn ds) mscs *
           [[ r = fst vs ]]
    REC RET:^(mscs,fsxp)
         exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs *
         [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} read_fblock fsxp inum off mscs >> recover.
  Proof.
    unfold forall_helper.
    intros; eexists; intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2_rx.
    eapply read_fblock_ok.
    eapply recover_ok.
    cancel.
    eauto.
    eauto.
    step.
    eassign ( LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    cancel; cancel.

    xform_norm.
    recover_ro_ok.
    rewrite LOG.crash_xform_intact.
    xform_norm.
    rewrite SB.crash_xform_rep.

    cancel.
    rewrite LOG.notxn_after_crash_diskIs. cancel.
    rewrite nthd_0; eauto. omega.

    safestep; subst.
    eassign d0; eauto.
    pred_apply; instantiate (1 := nil).
    replace n with 0 in *.
    rewrite nthd_0; simpl; auto.
    simpl in *; omega.

    cancel; cancel.
    rewrite LOG.after_crash_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    cancel; cancel.
  Qed.

  Theorem file_truncate_ok : forall fsxp inum sz mscs,
    {< ds Fm flist A f,
    PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
      [[[ ds!! ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist) ]]] *
      [[[ flist ::: (A * inum |-> f) ]]]
    POST RET:^(mscs, r)
      [[ r = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs \/
      [[ r = true  ]] * exists d flist' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs *
        [[[ d :::(Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
        [[[ flist' ::: (A * inum |-> f') ]]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]]
    CRASH
      LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds
     >} file_truncate fsxp inum sz mscs.
  Proof.
    unfold file_truncate; intros.
    step.
    step.
    destruct a0.
    step.
    step.
    step.  (* commit *)
    step.
    apply LOG.notxn_intact.
    step.
    step.  (* abort *)
    step.
    apply LOG.notxn_intact.
    step.
    apply LOG.notxn_intact.
  Qed.

  Hint Extern 1 ({{_}} progseq (file_truncate _ _ _ _) _) => apply file_truncate_ok : prog.

  Theorem c_reover_ok : forall fsxp inum sz mscs,
    {<< ds Fm flist A f,
    PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
      [[[ ds!! ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist) ]]] *
      [[[ flist ::: (A * inum |-> f) ]]]
    POST RET:^(mscs, r)
      [[ r = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs \/
      [[ r = true  ]] * exists d flist' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs *
        [[[ d :::(Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
        [[[ flist' ::: (A * inum |-> f') ]]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]]
    REC RET:^(mscs,fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs *
         [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
     >>} file_truncate fsxp inum sz mscs >> recover.
  Proof.
    unfold forall_helper.
    intros; eexists; intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2_rx.
    eapply file_truncate_ok.
    eapply recover_ok.
    cancel.
    step.
    eassign ( LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    xform_norm.
    recover_ro_ok.
    cancel.
    or_l.
    (* rewrite LOG.crash_xform_intact. *)
  Admitted.

  Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds Fm flist A f Fd v0,
    PRE     
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
      [[[ ds!! ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist) ]]] *
      [[[ flist ::: (A * inum |-> f) ]]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> v0) ]]]
    POST RET:mscs
      exists d flist' f',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs *
      [[[ d ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
      [[[ flist' ::: (A * inum |-> f') ]]] *
      [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge v0)) ]]]
    CRASH   
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds \/
      exists d flist' f',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) *
      [[[ d ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
      [[[ flist' ::: (A * inum |-> f') ]]] *
      [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge v0)) ]]]
   >} update_fblock_d fsxp inum off v mscs.
  Proof.
    unfold update_fblock_d; intros.
    step.
    step.
    eapply list2nmem_ptsto_bound; eauto.

    safestep.
    instantiate (1 := (m', nil)); simpl.
    rewrite singular_latest by auto; simpl; cancel.

    step.
    subst; pimpl_crash.
    cancel. or_r; cancel; eauto.
    rewrite LOG.notxn_idempred; eauto.

    or_l; rewrite LOG.recover_any_idempred; cancel.
    or_r; cancel; eauto.
    rewrite LOG.intact_idempred; cancel.
    or_l; rewrite LOG.notxn_idempred; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (update_fblock_d _ _ _ _ _) _) => apply update_fblock_d_ok : prog.

  Theorem update_fblock_d_recover_ok : forall fsxp inum off v mscs,
    {<< ds Fm flist A f Fd v0,
    PRE
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs *
      [[[ ds!! ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist) ]]] *
      [[[ flist ::: (A * inum |-> f) ]]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> v0) ]]]
    POST RET:mscs
      exists d flist' f',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs *
      [[[ d ::: (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
      [[[ flist' ::: (A * inum |-> f') ]]] *
      [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge v0)) ]]]
    REC RET:^(mscs,fsxp)
      exists d,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs *
      ((exists n, 
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] ) \/
       (exists flist' f' v',
        [[[ d ::: (crash_xform Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
        [[[ flist' ::: (arrayN_ex flist' inum * inum |-> f') ]]] *
        [[[ (BFILE.BFData f') ::: (crash_xform Fd * off |=> v') ]]] * [[ In v' (v :: vsmerge v0) ]]
      ))
   >>} update_fblock_d fsxp inum off v mscs >> recover.
  Proof.
    recover_ro_ok.
    apply update_fblock_d_ok.
    apply recover_ok.

    cancel.
    step.
    apply pimpl_refl.

    xform_norm;
    recover_ro_ok;
    rewrite LOG.idempred_idem; xform_deex_l;
    rewrite SB.crash_xform_rep.

    - cancel.
      step.
      or_l; cancel.
      destruct v0; cancel.
      rewrite LOG.after_crash_idempred; cancel.

    - cancel.
      step.
      denote crash_xform as Hx.
      replace n with 0 in Hx by omega; rewrite nthd_0 in Hx; simpl in Hx.
      apply (@crash_xform_diskIs_pred _ _ H0) in Hx.
      apply crash_xform_sep_star_dist in Hx.
      rewrite BFILE.xform_rep_off in Hx by eauto.
      destruct_lift Hx.
      or_r; safecancel; subst; intuition.

      cancel; or_r; cancel; eauto.
      apply LOG.after_crash_idempred.
  Qed.

(*
  Theorem create_ok : forall fsxp dnum name mscs,
    {< m pathname Fm Ftop tree tree_elem,
    PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
            [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
            [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
             (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
              exists inum tree', [[ r = Some inum ]] *
              [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (DIRTREE.TreeFile inum BFILE.bfile0) tree ]] *
              [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
    CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
              exists inum tree',
              (Fm * DIRTREE.rep fsxp Ftop tree') *
              [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (DIRTREE.TreeFile inum BFILE.bfile0) tree ]])
    >} create fsxp dnum name mscs.
  Proof.
    unfold create.
    hoare.
    erewrite DIRTREE.find_subtree_tree_graft by eauto; reflexivity.
    eapply pimpl_or_r; right; cancel.
    erewrite DIRTREE.update_subtree_tree_graft by eauto; reflexivity.
    all: try rewrite LOG.activetxn_would_recover_old.
    all: try rewrite LOG.notxn_would_recover_old.
    all: try apply LOG.would_recover_old_either_pred.
    rewrite <- LOG.would_recover_either_pred_pimpl.
    cancel.
    erewrite DIRTREE.update_subtree_tree_graft by eauto; reflexivity.
    Grab Existential Variables.
    all: eauto.
    exact BFILE.bfile0.
  Qed.

  Hint Extern 1 ({{_}} progseq (create _ _ _ _ ) _) => apply create_ok : prog.

  Theorem create_recover_ok : forall fsxp dnum name mscs,
    {<< m pathname Fm Ftop tree tree_elem,
    PRE     [[ cachesize <> 0 ]] *
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
            [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
            [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,r)
            [[ r = None ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
            (exists m', LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
              exists inum tree', [[ r = Some inum ]] *
              [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (DIRTREE.TreeFile inum BFILE.bfile0) tree  ]] *
              [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]])
    REC RET:^(mscs,fsxp)
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
             exists inum tree',
              [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (DIRTREE.TreeFile inum BFILE.bfile0) tree  ]] *
              [[ (Fm * DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]]
    >>} create fsxp dnum name mscs >> recover.
  Proof.
    recover_rw_ok.
  Qed.

  Theorem lookup_ok: forall fsxp dnum fnlist mscs,
    {< m Fm Ftop tree,
    PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
             [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
             [[ dnum = DIRTREE.dirtree_inum tree ]] *
             [[ DIRTREE.dirtree_isdir tree = true ]]
    POST RET:^(mscs,r)
             LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
             [[ r = DIRTREE.find_name fnlist tree ]]
    CRASH   LOG.would_recover_either (FSXPLog fsxp) (sb_rep fsxp) m m
    >} lookup fsxp dnum fnlist mscs.
  Proof.
    unfold lookup.
    hoare.
    apply LOG.would_recover_old_either.
    rewrite LOG.notxn_would_recover_old. apply LOG.would_recover_old_either.
    rewrite LOG.activetxn_would_recover_old. apply LOG.would_recover_old_either.
  Qed.

  Hint Extern 1 ({{_}} progseq (lookup _ _ _ _) _) => apply lookup_ok : prog.


  Theorem lookup_recover_ok : forall fsxp dnum fnlist mscs,
    {<< m Fm Ftop tree,
    PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
             [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
             [[ dnum = DIRTREE.dirtree_inum tree ]] *
             [[ DIRTREE.dirtree_isdir tree = true ]]
    POST RET:^(mscs,r)
             LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
             [[ r = DIRTREE.find_name fnlist tree ]]
    REC RET:^(mscs, fsxp)
             LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
    >>} lookup fsxp dnum fnlist mscs >> recover.
  Proof.
    recover_ro_ok.
  Qed.

  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< m Ftop tree cwd tree_elem,
    PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
            [[ (DIRTREE.rep fsxp Ftop tree) (list2mem m) ]] *
            [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,ok)
            [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
            [[ ok = true ]] * exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
            [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
            [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
            [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
            [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
    CRASH   LOG.would_recover_either_pred (FSXPLog fsxp) (sb_rep fsxp) m (
            exists srcnum srcents dstnum dstents subtree pruned renamed tree',
            (DIRTREE.rep fsxp Ftop tree')%pred *
            [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
            [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
            [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
            [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = DIRTREE.update_subtree cwd renamed tree ]])
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename.
    hoare.
    all: try rewrite LOG.activetxn_would_recover_old.
    all: try rewrite LOG.notxn_would_recover_old.
    all: try apply LOG.would_recover_old_either_pred.
    rewrite <- LOG.would_recover_either_pred_pimpl.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.

  (* XXX Use rep_return spec in App.v? *)
  Theorem rename_recover_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {<< m Ftop tree cwd tree_elem,
    PRE     LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
            [[ (DIRTREE.rep fsxp Ftop tree) (list2mem m) ]] *
            [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST RET:^(mscs,ok)
            [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
            [[ ok = true ]] * exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
            [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
            [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
            [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
            [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
    REC RET:^(mscs,fsxp)
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
            exists m' srcnum srcents dstnum dstents subtree pruned renamed tree',
            LOG.rep (FSXPLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
            [[ (DIRTREE.rep fsxp Ftop tree')%pred (list2mem m') ]] *
            [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
            [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
            [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
            [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
            [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
            [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]
    >>} rename fsxp dnum srcpath srcname dstpath dstname mscs >> recover.
  Proof.
    recover_rw_ok.
  Qed.

  *)

End AFS.


