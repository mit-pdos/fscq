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
Require Import DiskSet.

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
     * +--------+--------+--------+-------+-------+-------+--------+-------+------+
     * | Super- |  Data  | Inode  | Inode | Data1 | Data2 |  Log   | Log   | Log  |
     * | block  | blocks | blocks | alloc | alloc | alloc | header | descr | data |
     * +--------+--------+--------+-------+-------+-------+--------+-------+------+
     **)

    (* XXX: not quite right, fix later *)
    let data_blocks := data_bitmaps * BALLOC.items_per_val in
    let inode_blocks := inode_bitmaps * BALLOC.items_per_val / INODE.IRecSig.items_per_val in
    let inode_base := data_blocks in
    let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
    let balloc_base2 := balloc_base1 + data_bitmaps in
    let log_hdr := 1 + balloc_base2 + data_bitmaps in
    let log_descr := log_hdr + 1 in
    let log_data := log_descr + log_descr_blocks in
    let log_data_size := log_descr_blocks * PaddedLog.DescSig.items_per_val in
    let max_addr := log_data + log_data_size in
    (Build_fs_xparams
     (Build_log_xparams 1 log_hdr log_descr log_descr_blocks log_data log_data_size)
     (Build_inode_xparams inode_base inode_blocks)
     (Build_balloc_xparams balloc_base1 data_bitmaps)
     (Build_balloc_xparams balloc_base2 data_bitmaps)
     (Build_balloc_xparams (inode_base + inode_blocks) inode_bitmaps)
     1
     max_addr).

  Definition mkfs {T} data_bitmaps inode_bitmaps log_descr_blocks rx : prog T :=
    let fsxp := compute_xparams data_bitmaps inode_bitmaps log_descr_blocks in
    cs <- BUFCACHE.init_recover cachesize;
    cs <- SB.init fsxp cs;
    mscs <- LOG.init (FSXPLog fsxp) cs;
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    mscs <- BALLOC.init (FSXPLog fsxp) (FSXPBlockAlloc1 fsxp) mscs;
    mscs <- BALLOC.init (FSXPLog fsxp) (FSXPBlockAlloc2 fsxp) mscs;
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
          rx (Some ((BFILE.mk_memstate true mscs), fsxp))
        } else {
          rx None
        }
      } else {
        rx None
      }
    end.

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.
  Import DIRTREE.


  Definition recover {T} rx : prog T :=
    cs <- BUFCACHE.init_recover 10;
    let^ (cs, fsxp) <- SB.load cs;
    mscs <- LOG.recover (FSXPLog fsxp) cs;
    rx ^(BFILE.mk_memstate true mscs, fsxp).

  Definition file_get_attr T fsxp inum ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, attr) <- DIRTREE.getattr fsxp inum (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), attr).

  Definition file_get_sz T fsxp inum ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, attr) <- DIRTREE.getattr fsxp inum (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), INODE.ABytes attr).

  Definition file_set_attr T fsxp inum attr ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.setattr fsxp inum attr (MSAlloc ams, ms);
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), ok).

  Definition file_set_sz T fsxp inum sz ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.updattr fsxp inum (INODE.UBytes sz) (MSAlloc ams, ms);
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), ok).

  Definition read_fblock T fsxp inum off ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, b) <- DIRTREE.read fsxp inum off (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), b).

  Definition file_truncate T fsxp inum sz ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, ok) <- DIRTREE.truncate fsxp inum sz (MSAlloc ams, ms);
    If (bool_dec ok false) {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
      rx ^((MSAlloc ams, ms), false)
    } else {
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
      rx ^((MSAlloc ams, ms), ok)
    }.

  (* update an existing block directly.  XXX dwrite happens to sync metadata. *)
  Definition update_fblock_d T fsxp inum off v ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.dwrite fsxp inum off v (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms)).

  Definition update_fblock T fsxp inum off v ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.write fsxp inum off v (MSAlloc ams, ms);
    let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), ok).

  (* sync only data blocks of a file. XXX does a global flush too *)
  Definition file_sync T fsxp inum ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    ams <- DIRTREE.datasync fsxp inum (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms)).

  Definition readdir T fsxp dnum ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, files) <- SDIR.readdir (FSXPLog fsxp) (FSXPInode fsxp) dnum (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), files).

  Definition create T fsxp dnum name ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkfile fsxp dnum name (MSAlloc ams, ms);
    match oi with
      | None =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
          rx ^((MSAlloc ams, ms), None)
      | Some inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => rx ^((MSAlloc ams, ms), Some inum)
          | false => rx ^((MSAlloc ams, ms), None)
        end
    end.

  Definition mksock T fsxp dnum name ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkfile fsxp dnum name (MSAlloc ams, ms);
    match oi with
      | None =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
        rx ^((MSAlloc ams, ms), None)
      | Some inum =>
        ams <- BFILE.updattr (FSXPLog fsxp) (FSXPInode fsxp) inum (INODE.UType $1) ams;
        let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => rx ^((MSAlloc ams, ms), Some inum)
          | false => rx ^((MSAlloc ams, ms), None)
        end
    end.

  Definition mkdir T fsxp dnum name ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, oi) <- DIRTREE.mkdir fsxp dnum name (MSAlloc ams, ms);
    match oi with
      | None =>
        ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
          rx ^((MSAlloc ams, ms), None)
      | Some inum =>
        let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
        match ok with
          | true => rx ^((MSAlloc ams, ms), Some inum)
          | false => rx ^((MSAlloc ams, ms), None)
        end
    end.

  Definition delete T fsxp dnum name ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, ok) <- DIRTREE.delete fsxp dnum name (MSAlloc ams, ms);
    If (bool_dec ok true) {
       let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
       rx ^((MSAlloc ams, ms), ok)
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
      rx ^((MSAlloc ams, ms), false)
    }.

  Definition lookup T fsxp dnum names ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, r) <- DIRTREE.namei fsxp dnum names (MSAlloc ams, ms);
    ms <- LOG.commit_ro (FSXPLog fsxp) (MSLL ams);
    rx ^((MSAlloc ams, ms), r).

  Definition rename T fsxp dnum srcpath srcname dstpath dstname ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    let^ (ams, r) <- DIRTREE.rename fsxp dnum srcpath srcname dstpath dstname (MSAlloc ams, ms);
    If (bool_dec r true) {
      let^ (ms, ok) <- LOG.commit (FSXPLog fsxp) (MSLL ams);
      rx ^((MSAlloc ams, ms), ok)
    } else {
      ms <- LOG.abort (FSXPLog fsxp) (MSLL ams);
      rx ^((MSAlloc ams, ms), false)
    }.

  (* sync directory tree; will flush all outstanding changes to tree (but not dupdates to files) *)
  Definition tree_sync T fsxp ams rx : prog T :=
    ams <- DIRTREE.sync fsxp ams;
    rx ^(ams).

  Definition statfs T fsxp ams rx : prog T :=
    ms <- LOG.begin (FSXPLog fsxp) (MSLL ams);
    (*
    let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPLog fsxp) (FSXPBlockAlloc fsxp) mscs;
    let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPLog fsxp) (FSXPInodeAlloc fsxp) mscs;
     *)
    ms <- LOG.commit_ro (FSXPLog fsxp) ms;
    (* rx ^(mscs, free_blocks, free_inodes).  *)
    rx ^((MSAlloc ams, ms), 0, 0).

  (* Recover theorems *)

  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _) (LOG.rep_inner _ _ _ _)) => constructor : okToUnify.

  Theorem recover_ok :
    {< fsxp cs ds,
     PRE:hm
       LOG.after_crash (FSXPLog fsxp) (SB.rep fsxp) ds cs hm
     POST:hm' RET:^(ms, fsxp')
       [[ fsxp' = fsxp ]] * exists d n, [[ n <= length (snd ds) ]] *
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL ms) hm' *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     XCRASH:hm'
       LOG.before_crash (FSXPLog fsxp) (SB.rep fsxp) ds hm'
     >} recover.
  Proof.
    unfold recover, LOG.after_crash; intros.
    eapply pimpl_ok2.
    eapply BUFCACHE.init_recover_ok.
    cancel.
    unfold BUFCACHE.rep; cancel.
    eauto.

    prestep. norm. cancel.
    unfold BUFCACHE.rep; cancel.
    intuition.
    pred_apply.
    rewrite sep_star_comm.
    eauto.

    prestep. norm. cancel.
    unfold LOG.after_crash; norm. cancel.
    intuition simpl.
    pred_apply; norml.
    unfold stars; simpl.

    norm. cancel.
    rewrite LOG.rep_inner_hashmap_subset.
    eassign (SB.rep fsxp).
    cancel.
    or_l; cancel.
    auto.
    intuition simpl; eauto.
    safecancel.
    rewrite LOG.rep_inner_hashmap_subset.
    or_r; cancel.
    auto.
    eauto.
    auto.
    intuition.

    prestep. norm. cancel.
    intuition simpl; eauto.

    xcrash.
    xcrash.
    unfold LOG.before_crash.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor as [ Hor | Hor ];
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.

    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite LOG.rep_inner_rollbacktxn_pimpl in Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    xcrash.
    unfold LOG.before_crash.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor as [ Hor | Hor ];
    rewrite LOG.rep_inner_hashmap_subset in Hor; eauto.

    rewrite LOG.rep_inner_notxn_pimpl in Hor.
    destruct_lift Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.

    rewrite LOG.rep_inner_rollbacktxn_pimpl in Hor.
    norm. cancel.
    intuition.
    pred_apply.
    safecancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (recover) _) => apply recover_ok : prog.

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
  {< ds pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
         [[ r = BFILE.BFAttr f /\ MSAlloc mscs' = MSAlloc mscs ]]
  CRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
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
    rewrite LOG.notxn_intact. rewrite LOG.intact_idempred. reflexivity.
    rewrite LOG.intact_idempred. reflexivity.
    rewrite LOG.notxn_intact. rewrite LOG.intact_idempred. reflexivity.
  Qed.

  Hint Extern 1 ({{_}} progseq (file_get_attr _ _ _) _) => apply file_getattr_ok : prog.

  Ltac xcrash_solve :=
    repeat match goal with
      | [ H: forall _ _ _,  _ =p=> (?crash _) |- _ =p=> (?crash _) ] => idtac H; eapply pimpl_trans; try apply H; cancel
      | [ |- crash_xform (LOG.rep _ _ _ _ _) =p=> _ ] => idtac "crash_xform"; rewrite LOG.notxn_intact; cancel
      | [ H: crash_xform ?rc =p=> _ |- crash_xform ?rc =p=> _ ] => idtac H; rewrite H; xform_norm
    end.


  Ltac eassign_idempred :=
    match goal with
    | [ H : crash_xform ?realcrash =p=> crash_xform ?body |- ?realcrash =p=> (_ ?hm') ] =>
      let t := eval pattern hm' in body in
      match eval pattern hm' in body with
      | ?bodyf hm' =>
        instantiate (1 := (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform (bodyf hm) ]])%pred))
      end
    | [ |- ?body =p=> (_ ?hm) ] =>
      let t := eval pattern hm in body in
      match eval pattern hm in body with
      | ?bodyf hm =>
        instantiate (1 := (fun hm' => (exists p, p * [[ crash_xform p =p=> crash_xform (bodyf hm') ]])%pred));
        try (cancel; xform_norm; cancel)
      end
    end.

  (* Dumb and fast version of intuition *)
  Ltac intuition' :=
    match goal with
    | [|- _ /\ _]  => split; intuition'
    | [|- True] => auto
    | _ => idtac
  end.

  (* Try to simplify a pimpl with idempred on the left side. *)
  Ltac simpl_idempred_l :=
    simpl;
    repeat xform_dist;
    repeat xform_deex_l;
    xform_dist;
    rewrite crash_xform_lift_empty;
    norml; unfold stars; simpl;
    match goal with
    | [ H: crash_xform ?x =p=> crash_xform _ |- context[crash_xform ?x] ] => rewrite H
    end;
    repeat xform_dist;
    try rewrite sep_star_or_distr;
    rewrite LOG.crash_xform_idempred.

  (* Try to simplify a pimpl with idempred on the right side. *)
  Ltac simpl_idempred_r :=
      recover_ro_ok;
      (norml; unfold stars; simpl);
      (norm'r; unfold stars; simpl);
      try (cancel);
      intuition';
      repeat xform_dist;
      repeat rewrite crash_xform_idem.

  Theorem file_getattr_recover_ok : forall fsxp inum mscs,
  {X<< ds pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST:hm' RET:^(mscs',r)
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
         [[ r = BFILE.BFAttr f ]]
  REC:hm' RET:^(mscs, fsxp)
         exists d n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
  >>X} file_get_attr fsxp inum mscs >> recover.
  Proof.
    unfold forall_helper.
    recover_ro_ok.
    destruct v.
    cancel.
    eauto.
    step.

    norm'l. unfold stars; simpl.
    cancel.
    eassign_idempred.

    simpl_idempred_l.
    xform_norml;
      rewrite SB.crash_xform_rep;
      (rewrite LOG.notxn_after_crash_diskIs || rewrite LOG.rollbacktxn_after_crash_diskIs);
      try eassumption.
    cancel.
    safestep; subst.
    simpl_idempred_r.
    rewrite <- LOG.before_crash_idempred.
    cancel. auto.

    cancel.
    safestep; subst.
    simpl_idempred_r.
    rewrite <- LOG.before_crash_idempred.
    cancel. auto.
  Qed.

  Theorem read_fblock_ok : forall fsxp inum off mscs,
    {< ds Fm Ftop tree pathname f Fd vs ilist frees,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
           [[ r = fst vs /\ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
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
    rewrite LOG.notxn_intact.
    apply LOG.intact_idempred.
    apply LOG.intact_idempred.
    apply LOG.notxn_idempred.
  Qed.


  Hint Extern 1 ({{_}} progseq (read_fblock _ _ _ _) _) => apply read_fblock_ok : prog.

  Theorem read_fblock_recover_ok : forall fsxp inum off mscs,
    {X<< ds Fm Ftop tree pathname f Fd vs ilist frees,
    PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
           [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
           [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
           [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs', r)
           LOG.rep (FSXPLog fsxp) (SB.rep  fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
           [[ r = fst vs ]]
    REC:hm' RET:^(mscs,fsxp)
         exists d n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    >>X} read_fblock fsxp inum off mscs >> recover.
  Proof.
    unfold forall_helper.
    recover_ro_ok.
    destruct v.
    cancel.
    eauto.
    eauto.
    step.

    eassign_idempred.

    simpl_idempred_l.
    xform_norml;
      rewrite SB.crash_xform_rep;
      (rewrite LOG.notxn_after_crash_diskIs || rewrite LOG.rollbacktxn_after_crash_diskIs);
      try eassumption.
    cancel.
    safestep; subst.
    simpl_idempred_r.
    rewrite <- LOG.before_crash_idempred.

    cancel. auto.

    cancel.
    safestep; subst.
    simpl_idempred_r.
    rewrite <- LOG.before_crash_idempred.
    cancel. auto.
  Qed.

  Theorem file_set_attr_ok : forall fsxp inum attr mscs,
  {< ds pathname Fm Ftop tree f ilist frees,
  PRE:hm LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
         [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
  POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = true  ]] * exists d tree' f' ilist',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees)]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[ f' = BFILE.mk_bfile (BFILE.BFData f) attr ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]])
  XCRASH:hm'
         LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
  >} file_set_attr fsxp inum attr mscs.
  Proof.
    unfold file_set_attr; intros.
    step.
    step.
    step.
    step.
    xcrash_solve.
    rewrite LOG.intact_idempred; cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred; cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (file_set_attr _ _ _ _) _) => apply file_set_attr_ok : prog.

  Theorem file_truncate_ok : forall fsxp inum sz mscs,
    {< ds Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
    POST:hm' RET:^(mscs', r)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ r = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ r = true  ]] * exists d tree' f' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees  (MSAlloc mscs')) tree' ]])
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree' f' ilist' frees',
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (pushd d ds) hm' *
      [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
      [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
      [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]]
     >} file_truncate fsxp inum sz mscs.
  Proof.
    unfold file_truncate; intros.
    step.
    step.
    step.
    step.
    step.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    step.
    step.
    step.
    step.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
    xcrash_solve.
    rewrite LOG.intact_idempred. xform_norm. cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (file_truncate _ _ _ _) _) => apply file_truncate_ok : prog.

  Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
    (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.
  Proof.
    reflexivity.
  Qed.

  Theorem file_truncate_recover_ok : forall fsxp inum sz mscs,
    {<< ds Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
    POST:hm' RET:^(mscs', r)
      [[ r = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ r = true  ]] * exists d tree' f' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]]
    REC:hm' RET:^(mscs,fsxp)
      (exists d n, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm' *
         [[ n <= length (snd ds) ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]) \/
      (exists d dnew n ds' tree' f' ilist' frees',
         LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm' *
         [[ n <= length (snd ds') ]] *
         [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds'))) ]]] *
         [[ ds' = pushd dnew ds ]] *
         [[[ dnew ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
         [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
         [[ f' = BFILE.mk_bfile (setlen (BFILE.BFData f) sz ($0, nil)) (BFILE.BFAttr f) ]])
     >>} file_truncate fsxp inum sz mscs >> recover.
  Proof.
    recover_ro_ok.
    destruct v.
    cancel.
    eauto.
    safestep.  (* crucial to use safe version *)
    or_l.
    cancel. cancel.

    apply instantiate_crash.
    cancel.
    cancel.

    cancel.

    eassign_idempred.
    cancel.

    simpl.
    repeat xform_dist.
    repeat xform_deex_l.
    xform_dist.
    rewrite crash_xform_lift_empty.
    norml. unfold stars; simpl. rewrite H8.
    xform_dist. xform_deex_l.

    - rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

      prestep. norm. cancel.
      recover_ro_ok.
      cancel.
      or_l.
      safecancel; eauto.

      intuition.
      simpl_idempred_r.
      rewrite crash_xform_or_dist in *.
      auto.

      simpl_idempred_r.
      or_l; cancel.
      rewrite <- LOG.before_crash_idempred.
      auto.

    - norml; unfold stars; simpl.
      xform_deex_l. norml; unfold stars; simpl.
      xform_deex_l. norml; unfold stars; simpl.
      repeat xform_dist.
      rewrite LOG.idempred_idem.
      norml; unfold stars; simpl.
      rewrite SB.crash_xform_rep.
      cancel.

      prestep. norm. cancel.
      recover_ro_ok.
      cancel.
      or_r.
      safecancel; eauto.
      reflexivity.

      intuition.
      simpl_idempred_r.
      rewrite crash_xform_or_dist in *.
      auto.

      simpl_idempred_r.
      or_r; cancel.
      do 4 (xform_norm; cancel).
      rewrite <- LOG.before_crash_idempred.
      safecancel; eauto.
      auto.
      (* XXX: Goals proven, but getting
       * "Error: No such section variable or assumption: d." *)
  Admitted.

  Ltac latest_rewrite := unfold latest, pushd; simpl.

  Theorem update_fblock_d_ok : forall fsxp inum off v mscs,
    {< ds Fm Ftop tree pathname f Fd vs frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists tree' f' ds0 ds' bn,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[ ds' = dsupd ds0 bn (v, vsmerge vs) /\ BFILE.diskset_was ds0 ds ]] *
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
       [[ MSAlloc mscs' = MSAlloc mscs ]] *
       (* spec about files on the latest diskset *)
       [[[ ds'!! ::: (Fm  * DIRTREE.rep fsxp Ftop tree' ilist frees) ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    XCRASH:hm' exists bn,
       [[ BFILE.block_belong_to_file ilist bn inum off ]] *
      (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (updN (ds !!) bn (v, vsmerge vs), nil) hm' \/
       LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (updN (fst ds) bn (v, vsmerge vs), nil) hm')
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
    {<< ds Fm Ftop tree pathname f Fd vs frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
      [[[ (BFILE.BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(mscs')
      exists tree' f' ds',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
       [[[ ds'!! ::: (Fm  * DIRTREE.rep fsxp Ftop tree' ilist frees) ]]] *
       [[ tree' = update_subtree pathname (TreeFile inum f') tree ]] *
       [[[ (BFILE.BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
       [[ BFILE.BFAttr f' = BFILE.BFAttr f ]]
    REC:hm' RET:^(mscs,fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm' *
      ((exists n, 
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] ) \/
       (exists tree' f' v' ilist' frees',
        [[[ d ::: (crash_xform Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees')]]] *
        [[ tree' = DIRTREE.update_subtree pathname (DIRTREE.TreeFile inum f') tree ]] *
        [[[ (BFILE.BFData f') ::: (crash_xform Fd * off |=> v') ]]] *
        [[ BFILE.BFAttr f' = BFILE.BFAttr f ]] *
        [[ In v' (v :: vsmerge vs) ]]))
   >>} update_fblock_d fsxp inum off v mscs >> recover.
  Proof.
    recover_ro_ok.
    cancel.
    instantiate (pathname := v4); eauto.
    eauto.
    step.
    apply pimpl_refl.
    (* follows one of the earlier recover proofs but isn't used by atomiccp. *)
  Admitted.

  Theorem file_sync_ok: forall fsxp inum mscs,
    {< ds Fm Ftop tree pathname f ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ find_subtree pathname tree = Some (TreeFile inum f) ]]
    POST:hm' RET:^(mscs')
      exists ds' tree' ds0 al,
        [[ MSAlloc mscs' = MSAlloc mscs ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ ds' = dssync_vecs ds0 al /\ BFILE.diskset_was ds0 ds ]] *
        [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist frees)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum  (BFILE.synced_file f)) tree ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm' \/
      exists d tree',
        LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, nil) hm' *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist frees)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum  (BFILE.synced_file f)) tree ]]
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
      or_l.
      rewrite LOG.intact_idempred.
      or_r.
      cancel.
      xform_norm. cancel.
      xform_norm. safecancel.
      rewrite LOG.intact_idempred. cancel.
      eauto. auto.

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
    {<< ds Fm Ftop tree pathname f frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]]
    POST:hm' RET:^(mscs')
      exists ds' tree' ds0 al,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds') (MSLL mscs') hm' *
        [[ ds' = dssync_vecs ds0 al /\ BFILE.diskset_was ds0 ds ]] *
        [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist frees)]]] *
        [[ tree' = update_subtree pathname (TreeFile inum  (BFILE.synced_file f)) tree ]]
    REC:hm' RET:^(mscs,fsxp)
      exists d,
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) (MSLL mscs) hm' *
       ((exists n,  [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]) \/
         exists flist' F',
         [[[ d ::: (F' * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' ilist frees) ]]] *
         [[[ flist' ::: (arrayN_ex flist' inum * inum |-> BFILE.synced_file f) ]]]
       )
   >>} file_sync fsxp inum mscs >> recover.
  Proof.
    intros.
    recover_ro_ok.
    cancel. eauto.
    step.

    (* build a new idemcrash predicate that carries the XCRASH facts *)
    instantiate (1 :=  (fun hm => (exists p, p * [[ crash_xform p =p=> crash_xform
         (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v hm
      \/ (exists d tree',
           LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) (d, []) hm *
           [[[ d ::: v0 ✶ DIRTREE.rep fsxp v1 tree' ]]] *
           [[ tree' = DIRTREE.update_subtree v3 (DIRTREE.TreeFile inum (BFILE.synced_file v4)) v2 ]])) ]]))%pred).
    apply pimpl_refl.
    cancel.
    simpl.
    repeat xform_dist.
    repeat xform_deex_l.
    xform_dist.
    rewrite crash_xform_lift_empty.
    norml. unfold stars; simpl. rewrite H8.
    xform_dist. xform_deex_l.

    - rewrite LOG.idempred_idem; xform_deex_l;
      rewrite SB.crash_xform_rep.
      cancel.

      prestep. norm. cancel.
      recover_ro_ok.
      cancel.
      destruct v.
      or_l; cancel.

      intuition.
      cancel.

      simpl_idempred_r.
      or_l; cancel.
      rewrite <- LOG.before_crash_idempred.
      auto.

    - repeat xform_deex_l.
      repeat xform_dist.
      rewrite LOG.idempred_idem; xform_deex_l;
      rewrite SB.crash_xform_rep.
      cancel.

      step.
      denote crash_xform as Hx.
      replace n with 0 in Hx by omega; rewrite nthd_0 in Hx; simpl in Hx.
      denote! (_ (list2nmem x1)) as Hy.
      apply (crash_xform_diskIs_pred _ Hy) in Hx.
      apply crash_xform_sep_star_dist in Hx.

      (* unfold DIRTREE.rep in Hx to extract the file list *)
      unfold DIRTREE.rep in Hx; apply sep_star_comm in Hx.
      repeat (rewrite crash_xform_exists_comm in Hx;
        apply pimpl_exists_r_star_r in Hx;
        destruct Hx as [ ? Hx ]).
      repeat rewrite crash_xform_sep_star_dist in Hx.
      repeat rewrite crash_xform_lift_empty in Hx.
      rewrite BFILE.xform_rep, IAlloc.xform_rep in Hx.
      destruct_lift Hx.
      recover_ro_ok. cancel.
      or_r; cancel.

      (* XXX: should be able to tell from H8 and H7, though not very interesting.
         Need to prove (BFILE.synced_file v4) = selN dummy inum _ *)
      admit.

      simpl_idempred_r.
      or_r; cancel.
      do 3 (xform_norm; cancel).
      rewrite <- LOG.before_crash_idempred.
      eauto.
      auto.

    Unshelve. all: eauto.
  Admitted.

 Theorem tree_sync_ok: forall fsxp  mscs,
    {< ds Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees)]]] 
    POST:hm' RET:^(mscs')
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (ds!!, nil)) (MSLL mscs') hm' *
      [[ MSAlloc mscs' = negb (MSAlloc mscs) ]]
    XCRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
   >} tree_sync fsxp mscs.
  Proof.
    unfold tree_sync; intros.
    step.
    step.
    xcrash_solve.
    rewrite LOG.recover_any_idempred.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (tree_sync _ _) _) => apply tree_sync_ok : prog.

  Theorem lookup_ok: forall fsxp dnum fnlist mscs,
    {< ds Fm Ftop tree ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.dirtree_inum tree = dnum]] *
      [[ DIRTREE.dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs', r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
      [[ r = DIRTREE.find_name fnlist tree ]] *
      [[ MSAlloc mscs' = MSAlloc mscs ]]
    CRASH:hm'  LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
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
    apply LOG.notxn_idempred.
    apply LOG.intact_idempred.
    apply LOG.notxn_idempred.
  Qed.

  Hint Extern 1 ({{_}} progseq (lookup _ _ _ _) _) => apply lookup_ok : prog.

(*
  Theorem lookup_recover_ok : forall fsxp dnum fnlist mscs,
    {<< ds Fm Ftop tree ilist frees,
    PRE:hm
     LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.dirtree_inum tree = dnum]] *
      [[ DIRTREE.dirtree_isdir tree = true ]]
    POST:hm' RET:^(mscs',r)
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' *
      [[ r = DIRTREE.find_name fnlist tree ]]
    REC:hm' RET:^(mscs, fsxp)
      exists d, LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
       [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} lookup fsxp dnum fnlist mscs >> recover.
  Proof.
    recover_ro_ok.
    cancel.
    eauto.
    step.
    instantiate (1 := (LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v \/
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
*)

  Theorem create_ok : forall fsxp dnum name mscs,
    {< ds pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ find_subtree pathname tree = Some (TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
      ([[ r = None ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm'
      \/ exists inum,
       [[ r = Some inum ]] * exists d tree' ilist' frees',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
       [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (DIRTREE.TreeFile inum BFILE.bfile0) tree ]] *
       [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
       [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                       ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    CRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} create fsxp dnum name mscs.
  Proof.
    unfold create; intros.
    step.
    step.
    step.
    step.
    apply LOG.notxn_idempred.
    step.
    apply LOG.notxn_idempred.
    apply LOG.intact_idempred.
    apply LOG.notxn_idempred.
  Qed.

  Hint Extern 1 ({{_}} progseq (create _ _ _ _ ) _) => apply create_ok : prog.

(*
  Theorem create_recover_ok : forall fsxp dnum name mscs,
    {<< ds pathname Fm Ftop tree tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',r)
       [[ r = None ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm'
      \/ exists inum,
       [[ r = Some inum ]] * exists d tree' ilist' frees',
       LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm' *
       [[ tree' = DIRTREE.tree_graft dnum tree_elem pathname name 
                           (DIRTREE.TreeFile inum BFILE.bfile0) tree ]] *
       [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]]
    REC:hm' RET:^(mscs,fsxp)
      exists d,
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} create fsxp dnum name mscs >> recover.
  Proof.
    recover_ro_ok.
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

    (* if CRASH is LOG.idempred, we must manually instantiate idemcrash to include
       the after_crash case *)
    eassign ( LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v \/
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
*)

  Definition rename_rep ds mscs' Fm fsxp Ftop tree ilist frees cwd dnum srcpath srcname dstpath dstname hm :=
    (exists d tree' tree_elem srcnum srcents dstnum dstents subtree pruned renamed ilist' frees',
    LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm *
    [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
    [[ DIRTREE.find_subtree srcpath (DIRTREE.TreeDir dnum tree_elem) = Some (DIRTREE.TreeDir srcnum srcents) ]] *
    [[ DIRTREE.find_dirlist srcname srcents = Some subtree ]] *
    [[ pruned = DIRTREE.tree_prune srcnum srcents srcpath srcname (DIRTREE.TreeDir dnum tree_elem) ]] *
    [[ DIRTREE.find_subtree dstpath pruned = Some (DIRTREE.TreeDir dstnum dstents) ]] *
    [[ renamed = DIRTREE.tree_graft dstnum dstents dstpath dstname subtree pruned ]] *
    [[ tree' = DIRTREE.update_subtree cwd renamed tree ]] *
    [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                    ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]]
    ) %pred.

  Theorem rename_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {< ds Fm Ftop tree cwd tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = true ]] * 
        rename_rep ds mscs' Fm fsxp Ftop tree ilist frees cwd dnum srcpath srcname dstpath dstname hm')
    CRASH:hm'
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm'
    >} rename fsxp dnum srcpath srcname dstpath dstname mscs.
  Proof.
    unfold rename, rename_rep; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    apply LOG.notxn_idempred.
    step.
    step.
    apply LOG.notxn_idempred.
    step.
    apply LOG.intact_idempred.
    apply LOG.notxn_idempred.
  Qed.

  Hint Extern 1 ({{_}} progseq (rename _ _ _ _ _ _ _) _) => apply rename_ok : prog.

(*
  Theorem rename_recover_ok : forall fsxp dnum srcpath srcname dstpath dstname mscs,
    {<< ds Fm Ftop tree cwd tree_elem ilist frees,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.find_subtree cwd tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm' RET:^(mscs',ok)
      [[ ok = false ]] * LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm' \/
      [[ ok = true ]] * 
        rename_rep ds mscs' Fm fsxp Ftop tree ilist frees cwd dnum srcpath srcname dstpath dstname hm'
    REC:hm' RET:^(mscs,fsxp)
      exists d,
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (d, nil)) mscs hm' *
        [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]]
    >>} rename fsxp dnum srcpath srcname dstpath dstname mscs >> recover.
  Proof.
    recover_ro_ok.
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

    (* if CRASH is LOG.idempred, we must manually instantiate idemcrash to include
       the after_crash case *)
    eassign ( LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) v \/
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
*)


  Theorem delete_ok : forall fsxp dnum name mscs,
    {< ds pathname Fm Ftop tree tree_elem frees ilist,
    PRE:hm
      LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) hm *
      [[[ ds!! ::: (Fm * DIRTREE.rep fsxp Ftop tree ilist frees) ]]] *
      [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeDir dnum tree_elem) ]]
    POST:hm RET:^(mscs', ok)
      [[ MSAlloc mscs' = MSAlloc mscs ]] *
     ([[ ok = false ]] *
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs') hm   \/
      [[ ok = true ]] * exists d tree' ilist' frees',
        LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn (pushd d ds)) (MSLL mscs') hm *
        [[ tree' = DIRTREE.update_subtree pathname
                      (DIRTREE.delete_from_dir name (DIRTREE.TreeDir dnum tree_elem)) tree ]] *
        [[[ d ::: (Fm * DIRTREE.rep fsxp Ftop tree' ilist' frees') ]]] *
        [[ dirtree_safe ilist  (BFILE.pick_balloc frees  (MSAlloc mscs')) tree
                        ilist' (BFILE.pick_balloc frees' (MSAlloc mscs')) tree' ]])
    CRASH:hm
      LOG.idempred (FSXPLog fsxp) (SB.rep fsxp) ds hm
    >} delete fsxp dnum name mscs.
  Proof.
    unfold delete; intros.
    step.
    step.
    step.
    step.
    step.
    step.
    apply LOG.notxn_idempred.
    step.
    step.
    apply LOG.notxn_idempred.
    step.
    apply LOG.intact_idempred.
    apply LOG.notxn_idempred.
  Qed.

  Hint Extern 1 ({{_}} progseq (delete _ _ _ _) _) => apply delete_ok : prog.

End AFS.


