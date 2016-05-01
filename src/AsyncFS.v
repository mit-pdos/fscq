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
Require Import DiskLogHash.
Require Import SuperBlock.
Require Import NEList.

Set Implicit Arguments.
Import ListNotations.


Module AFS.

  Parameter cachesize : nat.

  (* Programs *)

  Definition compute_xparams (data_bitmaps inode_bitmaps log_descr_blocks : addr) :=
    (**
     * Block 0 stores the superblock (layout information).
     * The other block numbers, except for Log, are relative to
     * the Log data area, which starts at $1.
     * To account for this, we bump [log_base] by $1, to ensure that
     * the data area does not run into the logging structures.
     *)

    (**
     * File system layout:
     * +--------+--------+--------+-------+-------+--------+-------+------+
     * | Super- |  Data  | Inode  | Inode | Data  |  Log   | Log   | Log  |
     * | block  | blocks | blocks | alloc | alloc | header | descr | data |
     * +--------+--------+--------+-------+-------+--------+-------+------+
     **)

    let data_blocks := data_bitmaps * BALLOC.items_per_val in
    let inode_blocks := inode_bitmaps * BALLOC.items_per_val / INODE.IRecSig.items_per_val in
    let inode_base := data_blocks in
    let balloc_base := inode_base + inode_blocks + inode_bitmaps in
    let log_hdr := 1 + balloc_base + data_bitmaps in
    let log_descr := log_hdr + 1 in
    let log_data := log_descr + log_descr_blocks in
    let log_data_size := log_descr_blocks * PaddedLog.DescSig.items_per_val in
    let max_addr := log_data + log_data_size in
    (Build_fs_xparams
     (Build_log_xparams 1 log_hdr log_descr log_descr_blocks log_data log_data_size)
     (Build_inode_xparams inode_base inode_blocks)
     (Build_balloc_xparams (inode_base + inode_blocks) inode_bitmaps)
     (Build_balloc_xparams balloc_base data_bitmaps)
     1
     max_addr).

  Definition mkfs {T} data_bitmaps inode_bitmaps log_descr_blocks rx : prog T :=
    let fsxp := compute_xparams data_bitmaps inode_bitmaps log_descr_blocks in
    cs <- BUFCACHE.init_recover cachesize;
    cs <- SB.init fsxp cs;
    mscs <- LOG.init (FSXPLog fsxp) cs;
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    mscs <- BALLOC.init (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
    mscs <- BALLOC.init (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
    mscs <- INODE.init (FSXPLog fsxp) (FSXPInode fsxp) mscs;
    let^ (mscs, r) <- BALLOC.alloc (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
    match r with
    | None =>
      mscs <- LOG.abort (FSXPLog fsxp) mscs;
      rx None
    | Some inum =>
      (**
       * We should write a new fsxp back to the superblock with the new root
       * inode number.
       * In practice, the root inode is always the same, so it doesn't matter.
       *)
      If (eq_nat_dec inum (FSXPRootInum fsxp)) {
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
        If (bool_dec ok true) {
          mscs <- LOG.sync (FSXPLog fsxp) mscs;
          rx (Some (mscs, fsxp))
        } else {
          rx None
        }
      } else {
        rx None
      }
    end.

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

  Definition file_set_attr T fsxp inum attr mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    mscs <- DIRTREE.setattr fsxp inum attr mscs;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
      rx ^(mscs, ok).

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
    let^ (ms, ok) <- DIRTREE.truncate fsxp inum sz ms;
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
    ms <- DIRTREE.dwrite fsxp inum off v ms;
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;
    rx ^(ms).

  Definition update_fblock T fsxp inum off v ms rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) ms;
    ms <- DIRTREE.write fsxp inum off v ms;
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) ms;
    rx ^(ms, ok).

  (* sync only data blocks of a file. XXX does a global flush too *)
  Definition file_sync T fsxp inum ms rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) ms;
    ms <- DIRTREE.datasync fsxp inum ms;
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;
    rx ^(ms).

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
    mscs <- LOG.sync (FSXPLog fsxp) mscs;
    rx ^(mscs).

  Definition statfs T fsxp mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    (*
    let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
    let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
     *)
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    (* rx ^(mscs, free_blocks, free_inodes).  *)
    rx ^(mscs, 0, 0).

  (* Recover theorems *)

  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _) (LOG.rep_inner _ _ _ _)) => constructor : okToUnify.

  Theorem recover_ok :
    {< fsxp cs ds,
     PRE:hm
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm
     POST:hm' RET:^(ms, fsxp')
       [[ fsxp' = fsxp ]] * exists d n, [[ n <= length (snd ds) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) ms hm' *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     CRASH:hm' exists cs',
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs' hm'
     >} recover.
  Proof.
    unfold recover, LOG.after_crash; intros.
    eapply pimpl_ok2.
    eapply BUFCACHE.init_recover_ok.
    cancel.
    unfold BUFCACHE.rep; cancel.
    eauto.
    prestep. norm. cancel. intuition; eauto.
    unfold BUFCACHE.rep; cancel.
    intuition.
    pred_apply; cancel.
    prestep. norm. cancel. 
    unfold LOG.after_crash; norm. cancel.
    intuition simpl.
    pred_apply; norml. 
    unfold stars; simpl.

    norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    instantiate (4 := hm1).
    cancel.
    eauto.
    eauto.
    intuition.
    prestep. norm. cancel.
    intuition.
    pred_apply; norm; eauto. cancel.
    rewrite min_l.
    cancel.
    auto.
    unfold LOG.after_crash. norm; eauto.
    unfold stars; simpl.
    pimpl_crash. norm. cancel.
    intuition; pred_apply. norm. cancel.
    intuition eauto.

    unfold LOG.after_crash. norm; eauto.
    unfold stars; simpl.
    pimpl_crash. norm. cancel.
    intuition; pred_apply. norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    instantiate (3 := hm_crash).
    cancel; eauto.
    eauto.
    intuition eauto.

    unfold LOG.after_crash. norm; eauto.
    unfold stars; simpl.
    pimpl_crash. norm. cancel.
    intuition; pred_apply. norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    instantiate (3 := hm_crash).
    cancel; eauto.
    eauto.
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

  Hint Extern 0 (okToUnify (LOG.idempred _ _ _ _) (LOG.idempred _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (LOG.after_crash _ _ _ _ _) (LOG.after_crash _ _ _ _ _)) => constructor : okToUnify.
 

  (* Specs and proofs *)

  Theorem file_getattr_ok : forall fsxp inum mscs,
  {< ds pathname Fm Ftop tree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST:hm' RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' *
         [[ r = BFILE.BFAttr f ]]
  CRASH:hm'
         LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
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

  Hint Extern 1 ({{_}} progseq (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.

  Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {<< ds pathname Fm Ftop tree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST:hm' RET:^(mscs,r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' *
         [[ r = BFILE.BFAttr f ]]
  REC:hm' RET:^(mscs, fsxp)
         exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
         [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
  >>} file_get_attr fsxp inum mscs >> recover.
  Proof.
    recover_ro_ok.
    eapply recover_ok.
    cancel.
    eauto.
    step.

    instantiate (1 := (fun hm => LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v hm\/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs hm))%pred).
    instantiate (1 := (fun hm => F_ * (LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v hm\/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs hm)))%pred).
    reflexivity.
    cancel. cancel.
    xform_norm.
    recover_ro_ok.
    rewrite LOG.crash_xform_intact.
    xform_norm.
    rewrite SB.crash_xform_rep.

    cancel.
    rewrite LOG.notxn_after_crash_diskIs. cancel.
    rewrite nthd_0; eauto. omega.

    safestep; subst.
    instantiate (1 := nil).
    replace n with 0 in *.
    rewrite nthd_0; simpl; auto.
    simpl in *; omega.

    cancel; cancel. cancel.
    cancel.
    rewrite LOG.after_crash_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    cancel; cancel.
    cancel; cancel.
    cancel; cancel.
  Qed.

  Theorem read_fblock_ok : forall fsxp inum off mscs,
    {< ds Fm Ftop tree pathname f Fd vs,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' *
           [[ r = fst vs ]]
    CRASH:hm'
           LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
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
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs,r)
           LOG.rep (FSXPLog fsxp) (SB.rep  fsxp) (LOG.NoTxn ds) mscs hm' *
           [[ r = fst vs ]]
    REC:hm' RET:^(mscs,fsxp)
         exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
         [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} read_fblock fsxp inum off mscs >> recover.
  Proof.
    recover_ro_ok.
    eapply recover_ok.
    cancel.
    eauto.
    eauto.
    step.

   instantiate (1 := (fun hm => LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v hm\/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs hm))%pred).
    instantiate (1 := (fun hm => F_ * (LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v hm\/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs hm)))%pred).
    reflexivity.
    cancel. cancel.
    xform_norm.
    recover_ro_ok.
    rewrite LOG.crash_xform_intact.
    xform_norm.
    rewrite SB.crash_xform_rep.

    cancel.
    rewrite LOG.notxn_after_crash_diskIs. cancel.
    rewrite nthd_0; eauto. omega.

    safestep; subst.
    instantiate (1 := nil).
    replace n with 0 in *.
    rewrite nthd_0; simpl; auto.
    simpl in *; omega.

    cancel; cancel. cancel.
    cancel.
    rewrite LOG.after_crash_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.

    step.
    cancel; cancel.
    cancel; cancel.
    cancel; cancel.
  Qed.

  Ltac xcrash_solve := 
    repeat match goal with 
      | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => idtac H; eapply pimpl_trans; try apply H; cancel
      | [ |- crash_xform (LOG.rep _ _ _ _ _) =p=> _ ] => idtac "crash_xform"; rewrite LOG.notxn_intact; cancel
      | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => idtac H; rewrite H; xform_norm
    end.

  Theorem file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds pathname Fm Ftop tree f,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST:hm' RET:^(mscs, ok)
      [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      [[ ok = true  ]] * exists d tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]]
  XCRASH:hm'
         LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} file_set_attr fsxp inum attr mscs.
  Proof.
    unfold file_set_attr; intros.
    step.
    step.
    step.
    step.
    xcrash_solve.
    xcrash_solve.
    xcrash_solve.
  Qed.

  Hint Extern 1 ({{_}} progseq (file_set_attr _ _ _ _) _) => apply file_set_attr_ok : prog.

  Theorem file_truncate_ok : forall fsxp inum sz mscs,
    {< ds Fm Ftop tree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
    POST:hm' RET:^(mscs, r)
      [[ r = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      [[ r = true  ]] * exists d tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]]
    XCRASH:hm'
      (* interesting: no need to add d to ds, because when we crash we always recover with the first disk of ds *)
      LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} file_truncate fsxp inum sz mscs.
  Proof.
    unfold file_truncate; intros.
    step.
    step.
    step.
    step.
    step.
    xcrash_solve.
    step.
    step.
    step.
    step.
    xcrash_solve.
    xcrash_solve.
    xcrash_solve.
  Qed.

  Hint Extern 1 ({{_}} progseq (file_truncate _ _ _ _) _) => apply file_truncate_ok : prog.

  Theorem file_truncate_recover_ok : forall fsxp inum sz mscs,
    {<< ds Fm Ftop tree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
     POST:hm' RET:^(mscs, r)
      [[ r = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      [[ r = true  ]] * exists d tree' f',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]]
     REC:hm' RET:^(mscs,fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
         [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
     >>} file_truncate fsxp inum sz mscs >> recover.
  Proof.
    recover_ro_ok.
    eapply recover_ok.
    cancel.
    instantiate (pathname := v3); eauto.
    safestep.  (* crucial to use safe version *)
    or_l.
    cancel. cancel.

   instantiate (1 :=  (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform
       (LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v hm \/
         (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs hm)) ]]))%pred).
   instantiate (1 :=  (fun hm => F_ * (exists p, p * [[ crash_xform p =p=> crash_xform
       (LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v hm \/
         (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs hm)) ]]))%pred).
    reflexivity.
    cancel; cancel.
    cancel.
    cancel.
    xcrash.
    or_l.
    eauto.

    xform_dist.
    repeat xform_dist.
    apply sep_star_lift_l.
    intros.
    rewrite crash_xform_exists_comm.
    rewrite sep_star_comm.
    rewrite pimpl_exists_r_star_r.
    apply pimpl_exists_l; intro.
    xform_dist.
    rewrite crash_xform_lift_empty.
    norml; unfold stars; simpl; clear_norm_goal.
    denote (crash_xform _ =p=> crash_xform _) as Hc; rewrite Hc.
    xform_norm.

    rewrite LOG.crash_xform_intact.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    cancel.
    rewrite LOG.notxn_after_crash_diskIs. cancel.

    pred_apply; instantiate (1 := nil).
    rewrite nthd_0; simpl; auto.
    cancel; cancel.
    omega.

    safestep; subst.
    cancel.
    cancel.
    cancel.
    xform_normr.
    or_r.
    xform_normr.
    cancel.

    rewrite LOG.after_crash_idem.
    xform_norm.
    rewrite SB.crash_xform_rep.
    recover_ro_ok.
    
    cancel.

    safestep; subst.
    cancel; cancel.
    cancel; cancel.
   xform_normr.
    or_r.
    xform_normr.
    cancel.
   Unshelve. all: eauto.
  Qed.

  Ltac latest_rewrite := unfold latest, pushd; simpl.

  Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds Fm Ftop tree pathname f Fd v0,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> v0) ]]]
    POST:hm' RET:^(mscs)
      exists d tree' f',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
      [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
      [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge v0)) ]]] *
      [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' f',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
      [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
      [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge v0)) ]]] *
      [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
   >} update_fblock_d fsxp inum off v mscs.
  Proof.
    unfold update_fblock_d; intros.
    step.
    prestep. norm. cancel.
    xcrash_solve.
    intuition.
    latest_rewrite.
    pred_apply; cancel.
    eauto.
    eauto.
    safestep.

    instantiate (1 := (d, nil)); simpl.
    rewrite singular_latest by auto; simpl; cancel.
    step.
    cancel.
    xcrash_solve.

    - xform_norm. or_r. cancel.
      xform_norm. cancel.
      xform_norm. cancel.
      xform_norm. safecancel.
      instantiate (1 := d); simpl.
      rewrite LOG.intact_idempred; cancel.
      pred_apply.
      eauto.
      f_equal.
      pred_apply.
      cancel.
      simpl; reflexivity.

    - eapply pimpl_trans.
      2: eapply H1.
      cancel.
      eapply pimpl_trans.
      eapply H0.
      xform_norm. cancel.
      or_l. rewrite LOG.recover_any_idempred; cancel.
      or_r.
      xform_norm. cancel.
      xform_norm. cancel.
      xform_norm. cancel.
      xform_norm. safecancel.
      instantiate (1 := x); simpl.
      rewrite LOG.intact_idempred; cancel.
      pred_apply.
      cancel.
      f_equal.
      pred_apply.
      cancel.
      simpl; reflexivity.

    - xcrash_solve.
      xform_norm.
      or_l. rewrite LOG.intact_idempred.
     eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (update_fblock_d _ _ _ _ _) _) => apply update_fblock_d_ok : prog.

  Theorem update_fblock_d_recover_ok : forall fsxp inum off v mscs,
    {<< ds Fm Ftop tree pathname f Fd v0,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> v0) ]]]
    POST:hm' RET:^(mscs)
      exists d tree' f',
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
      [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
      [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge v0)) ]]] *
      [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    REC:hm' RET:^(mscs,fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
      ((exists n, 
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] ) \/
       (exists tree' f' v',
        [[[ d ::: (crash_xform Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[[ (BFILE.BFData f') ::: (crash_xform Fd * off |=> v') ]]] *
        [[ BFILE.BFAttr f' = BFILE.BFAttr f ]] *
        [[ In v' (v :: vsmerge v0) ]]))
   >>} update_fblock_d fsxp inum off v mscs >> recover.
  Proof.
    recover_ro_ok.
    apply recover_ok.
    cancel.
    instantiate (pathname := v4); eauto.
    eauto.
    step.
    apply pimpl_refl.
    (* follows one of the earlier recover proofs but isn't used by atomiccp. *)
  Admitted.

  Theorem file_sync_ok: forall fsxp inum mscs,
    {< ds Fm Ftop tree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
    POST:hm' RET:^(mscs)
      exists d tree',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum  (BFILE.synced_file f)) tree ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum  (BFILE.synced_file f)) tree ]]
   >} file_sync fsxp inum mscs.
  Proof.
    unfold file_sync; intros.
    step.
    prestep. norm. cancel.
    intuition.
    latest_rewrite.
    pred_apply; cancel.
    eauto.
    step.
    instantiate (1 := (d, nil)); simpl.
    rewrite singular_latest by auto; simpl; cancel.
    step.

    - xcrash_solve.
      xform_norm.
      or_r.
      cancel.
      xform_norm. cancel.
      xform_norm. safecancel.
      instantiate (1 := d); simpl.
      admit.  (*  rewrite LOG.notxn_intact *)
      pred_apply.
      cancel.

    - eapply pimpl_trans; [ | eapply H1 ]; cancel.
      xform_norm.
      or_l.
      rewrite H3.
      rewrite LOG.recover_any_idempred.
      cancel.

    - xcrash_solve.
      xform_norm.
      or_l.
      rewrite LOG.intact_idempred.
      cancel.
    Qed.

  Hint Extern 1 ({{_}} progseq (file_sync _ _ _) _) => apply file_sync_ok : prog.


  Theorem file_sync_recover_ok : forall fsxp inum mscs,
    {<< ds Fm Ftop tree pathname f,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
    POST:hm' RET:^(mscs)
      exists d tree',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum  (BFILE.synced_file f)) tree ]]
    REC:hm' RET:^(mscs,fsxp)
      exists d,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
       ((exists n,  [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]) \/
         exists flist',
         [[[ d ::: (crash_xform Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist') ]]] *
         [[[ flist' ::: (arrayN_ex flist' inum * inum |-> BFILE.synced_file f) ]]]
       )
   >>} file_sync fsxp inum mscs >> recover.
  Proof.
    intros.
    recover_ro_ok.
    apply recover_ok.
    cancel.
    step.
    (* build a new idemcrash predicate that carries the XCRASH facts *)
    match goal with
    | [ H : crash_xform ?rc =p=> crash_xform ?crash
         |-  ?F * ?rc =p=> ?F * ?idem ] => is_evar idem;
        instantiate (1 := (exists p, p * [[ crash_xform p =p=> crash_xform crash ]])%pred);
        cancel
    end.

    (* tough work to pull out the "exists p" inside crash_form *)
    xform_dist.
    rewrite crash_xform_exists_comm.
    rewrite sep_star_comm.
    rewrite pimpl_exists_r_star_r.
    apply pimpl_exists_l; intro.
    xform_dist.
    rewrite crash_xform_lift_empty.
    norml; unfold stars; simpl; clear_norm_goal.
    denote (crash_xform _ =p=> crash_xform _) as Hc; rewrite Hc.

    xform_norm;
    recover_ro_ok;
    rewrite LOG.idempred_idem; xform_deex_l;
    rewrite SB.crash_xform_rep.

    - cancel.
      step.
      cancel.
      cancel.
      destruct v.
      xform_norm.
      or_l; cancel.
      rewrite LOG.after_crash_idempred; cancel.

    - cancel.
      step.
      denote crash_xform as Hx.
      replace n with 0 in Hx by omega; rewrite nthd_0 in Hx; simpl in Hx.
      apply (crash_xform_diskIs_pred _ H) in Hx.
      apply crash_xform_sep_star_dist in Hx.
      rewrite BFILE.xform_rep_file in Hx by eauto.
      destruct_lift Hx.
      or_r; safecancel.
      erewrite BFILE.file_crash_synced with (f := BFILE.synced_file v3); eauto.
      apply BFILE.fsynced_synced_file.

      cancel.
      apply crash_xform_pimpl.
      rewrite LOG.after_crash_idempred.
      or_r; safecancel.

    Unshelve. all: eauto.
  Qed.


  Theorem lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds Fm Ftop tree,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.dirtree_inum tree = dnum]] *
      [[ DIRTREE.dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs,r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' *
      [[ r = DIRTREE.find_name fnlist tree ]]
    CRASH:hm'  LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} lookup fsxp dnum fnlist mscs.
  Proof.
    unfold lookup; intros.
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

  Hint Extern 1 ({{_}} progseq (lookup _ _ _ _) _) => apply lookup_ok : prog.

  Theorem lookup_recover_ok : forall fsxp dnum fnlist mscs,
    {<< ds Fm Ftop tree,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.dirtree_inum tree = dnum]] *
      [[ DIRTREE.dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs,r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' *
      [[ r = DIRTREE.find_name fnlist tree ]]
    REC:hm' RET:^(mscs, fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
       [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} lookup fsxp dnum fnlist mscs >> recover.
  Proof.
    recover_ro_ok.
    eapply recover_ok.
    cancel.
    eauto.
    step.
    instantiate (1 := (LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred).
    cancel; cancel.
    cancel.
    or_l.
    cancel.
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

  Theorem create_ok : forall fsxp dnum name mscs,
    {< ds pathname Fm Ftop tree tree_elem,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,r)
      [[ r = None ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      (exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm' *
       exists inum tree', [[ r = Some inum ]] *
        [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                            (DIRTREE.TreeFile inum BFILE.bfile0) tree ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]])
    CRASH:hm'
      LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} create fsxp dnum name mscs.
  Proof.
    unfold create; intros.
    step.
    step.
    step.
    step.
    apply LOG.notxn_intact.
    step.
    apply LOG.notxn_intact.
    apply LOG.notxn_intact.
  Qed.

  Hint Extern 1 ({{_}} progseq (create _ _ _ _ ) _) => apply create_ok : prog.

  Theorem create_recover_ok : forall fsxp dnum name mscs,
    {<< ds pathname Fm Ftop tree tree_elem,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,r)
      [[ r = None ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      (exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm' *
       exists inum tree', [[ r = Some inum ]] *
        [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                            (DIRTREE.TreeFile inum BFILE.bfile0) tree ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]])
    REC:hm' RET:^(mscs,fsxp)
      exists d,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} create fsxp dnum name mscs >> recover.
  Proof.
    recover_ro_ok.
    apply recover_ok.
    cancel.
    eauto.
    safestep.
    or_l.
    cancel.
    subst.
    apply pimpl_refl.
    or_r.
    cancel.
    subst.
    apply pimpl_refl.

    (* if CRASH is LOG.intact, we must manually instantiate idemcrash to include
       the after_crash case *)
    eassign ( LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    cancel; cancel.
    xform_norm; recover_ro_ok.

    - rewrite LOG.crash_xform_intact.
      xform_norm.
      rewrite SB.crash_xform_rep.
      rewrite LOG.notxn_after_crash_diskIs with (n := 0) (ds := (fst v, nil)); auto.
      cancel.
      safestep.
      cancel.
      pred_apply; subst.
      replace n with 0 by omega.
      rewrite nthd_0; eauto.
      cancel; cancel.

    - rewrite LOG.after_crash_idem.
      xform_norm.
      rewrite SB.crash_xform_rep.
      cancel.
      step.
      cancel; cancel.
  Qed.


  Definition rename_rep ds mscs Fm fsxp Ftop tree cwd dnum srcpath srcname dstpath dstname hm :=
    (exists d tree' tree_elem srcnum srcents dstnum dstents subtree pruned renamed,
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm *
    [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]] *
    [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
    [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
    [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
    [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
    [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
    [[ tree' = DIRTREE.update_subtree cwd renamed tree ]]) %pred.

  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< ds Fm Ftop tree cwd tree_elem,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs, ok)
      [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      [[ ok = true ]] * 
        rename_rep ds mscs Fm fsxp Ftop tree cwd dnum srcpath srcname dstpath dstname hm'
    CRASH:hm'
      LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rename_rep; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    apply LOG.notxn_intact.
    step.
    step.
    apply LOG.notxn_intact.
    step.
    apply LOG.notxn_intact.
  Qed.

  Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.

  Theorem rename_recover_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {<< ds Fm Ftop tree cwd tree_elem,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs,ok)
      [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm' \/
      [[ ok = true ]] * 
        rename_rep ds mscs Fm fsxp Ftop tree cwd dnum srcpath srcname dstpath dstname hm'
    REC:hm' RET:^(mscs,fsxp)
      exists d,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
        [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} rename fsxp dnum srcpath srcname dstpath dstname mscs >> recover.
  Proof.
    recover_ro_ok.
    apply recover_ok.
    cancel.
    eauto.
    safestep.
    or_l.
    cancel.
    subst.
    apply pimpl_refl.
    or_r.
    cancel.
    subst.
    apply pimpl_refl.

    (* if CRASH is LOG.intact, we must manually instantiate idemcrash to include
       the after_crash case *)
    eassign ( LOG.intact (FSXPLog fsxp) (SB.rep fsxp) v \/
      (exists cs : cachestate, LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) (fst v, []) cs))%pred.
    cancel; cancel.
    xform_norm; recover_ro_ok.

    - rewrite LOG.crash_xform_intact.
      xform_norm.
      rewrite SB.crash_xform_rep.
      rewrite LOG.notxn_after_crash_diskIs with (n := 0) (ds := (fst v, nil)); auto.
      cancel.
      safestep.
      cancel.
      pred_apply; subst.
      replace n with 0 by omega.
      rewrite nthd_0; eauto.
      cancel; cancel.

    - rewrite LOG.after_crash_idem.
      xform_norm.
      rewrite SB.crash_xform_rep.
      cancel.
      step.
      cancel; cancel.
  Qed.



  Theorem delete_ok : forall fsxp dnum name mscs,
    {< ds pathname Fm Ftop tree tree_elem,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree) ]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm RET:^(mscs, ok)
      [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) mscs hm \/
      (exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) mscs hm *
       exists tree', [[ ok = true ]] *
        [[ tree' = DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) tree ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree') ]]])
    CRASH:hm
      LOG.intact (FSXPLog fsxp) (SB.rep fsxp) ds hm
    >} delete fsxp dnum name mscs.
  Proof.
  Admitted.



End AFS.


