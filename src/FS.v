Require Import Prog.
Require Import MemLog.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred.
Require Import DirName.
Require Import Hoare.
Require Import GenSep.
Require Import GenSepN.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
Require Import DirTree.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.

Set Implicit Arguments.
Import ListNotations.

Parameter cachesize : nat.
Axiom cachesize_nonzero : cachesize <> 0.

Definition compute_xparams (data_bitmaps inode_bitmaps : addr) :=
  (* Block $0 stores the superblock (layout information).
   * The other block numbers, except for MemLog, are relative to
   * the MemLog data area, which starts at $1.
   * To account for this, we bump [log_base] by $1, to ensure that
   * the data area does not run into the logging structures.
   *)
  let data_blocks := data_bitmaps ^* BALLOC.items_per_valu in
  let inode_blocks := inode_bitmaps ^* BALLOC.items_per_valu ^/ INODE.items_per_valu in
  let inode_base := data_blocks in
  let balloc_base := inode_base ^+ inode_blocks ^+ inode_bitmaps in
  let log_base := $1 ^+ balloc_base ^+ data_bitmaps in
  let log_size := $ MEMLOG.addr_per_block in
  let max_addr := log_base ^+ $3 ^+ log_size in
  (Build_fs_xparams
   (Build_memlog_xparams $1 log_base (log_base ^+ $1) (log_base ^+ $2) log_size)
   (Build_inode_xparams inode_base inode_blocks)
   (Build_balloc_xparams (inode_base ^+ inode_blocks) inode_bitmaps)
   (Build_balloc_xparams balloc_base data_bitmaps)
   $0
   max_addr).

Definition set_root_inode fsxp rootinum :=
  Build_fs_xparams
    fsxp.(FSXPMemLog)
    fsxp.(FSXPInode)
    fsxp.(FSXPInodeAlloc)
    fsxp.(FSXPBlockAlloc)
    rootinum
    fsxp.(FSXPMaxBlock).

Definition mkfs T data_bitmaps inode_bitmaps rx : prog T :=
  let fsxp := compute_xparams data_bitmaps inode_bitmaps in
  cs <- BUFCACHE.init cachesize;
  cs <- sb_init fsxp cs;
  mscs <- MEMLOG.init (FSXPMemLog fsxp) cs;
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  mscs <- BALLOC.init' (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) mscs;
  mscs <- INODE.init (FSXPMemLog fsxp) (FSXPInodeAlloc fsxp) (FSXPInode fsxp) mscs;
  let^ (mscs, r) <- BALLOC.alloc_gen (FSXPMemLog fsxp) (FSXPInodeAlloc fsxp) mscs;
  match r with
  | None =>
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, fsxp, false)
  | Some inum =>
    let fsxp' := set_root_inode fsxp inum in
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    rx ^(mscs, fsxp, ok)
  end.

Definition recover {T} rx : prog T :=
  cs <- BUFCACHE.init_recover cachesize;
  let^ (cs, fsxp) <- sb_load cs;
  mscs <- MEMLOG.recover (FSXPMemLog fsxp) cs;
  rx ^(mscs, fsxp).

Local Opaque BUFCACHE.rep.

Theorem recover_ok :
  {< fsxp old new,
  PRE
    crash_xform (MEMLOG.would_recover_either (FSXPMemLog fsxp) (sb_rep fsxp) old new)
  POST RET:^(mscs, fsxp')
    [[ fsxp' = fsxp ]] *
    (MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction old) mscs \/
     MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction new) mscs)
  CRASH
    MEMLOG.would_recover_either (FSXPMemLog fsxp) (sb_rep fsxp) old new
  >} recover.
Proof.
  unfold recover, MEMLOG.would_recover_either; intros.
  pose proof cachesize_nonzero.

  eapply pimpl_ok2; eauto with prog.
  intros. norm'l. unfold stars; simpl.
  repeat ( setoid_rewrite crash_xform_exists_comm ||
           setoid_rewrite crash_xform_sep_star_dist ||
           setoid_rewrite crash_xform_lift_empty ).
  cancel.

  step.
  autorewrite with crash_xform. cancel.

  eapply pimpl_ok2; eauto with prog.
  unfold MEMLOG.would_recover_either.
  cancel.

  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_sep_star_dist.
  cancel.

  step.
  unfold MEMLOG.rep. setoid_rewrite crash_xform_sb_rep. cancel.
  unfold MEMLOG.rep. setoid_rewrite crash_xform_sb_rep. cancel.
  subst. pimpl_crash. cancel. autorewrite with crash_xform. cancel.

  autorewrite with crash_xform. cancel.

  pimpl_crash. norm'l; unfold stars; simpl. autorewrite with crash_xform.
  norm. cancel. intuition.
  eapply pred_apply_crash_xform_pimpl; eauto.
  autorewrite with crash_xform. cancel.
Qed.

Hint Extern 1 ({{_}} progseq (recover) _) => apply recover_ok : prog.

Definition file_nblocks T fsxp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, len) <- DIRTREE.getlen fsxp inum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, len).

Definition file_get_attr T fsxp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, attr).

Definition file_get_sz T fsxp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, INODE.ISize attr).

Definition file_set_sz T fsxp inum sz mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, attr) <- DIRTREE.getattr fsxp inum mscs;
  mscs <- BFILE.bfsetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum
                          (INODE.Build_iattr sz
                                             (INODE.IMTime attr)
                                             (INODE.IType attr))
                          mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, ok).

Definition read_block T fsxp inum off mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, b) <- DIRTREE.read fsxp inum off mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, b).

Theorem read_block_ok : forall fsxp inum off mscs,
  {< m F Fm Ftop tree pathname f B v,
  PRE    MEMLOG.rep (FSXPMemLog fsxp) F (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
         [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,r)
         MEMLOG.rep (FSXPMemLog fsxp) F (NoTransaction m) mscs *
         [[ r = v ]]
  CRASH  MEMLOG.would_recover_either (FSXPMemLog fsxp) F m m
  >} read_block fsxp inum off mscs.
Proof.
  unfold read_block.
  hoare.
  apply MEMLOG.would_recover_old_either.
  unfold MEMLOG.rep, MEMLOG.would_recover_either, MEMLOG.would_recover_either'. cancel. cancel.
  unfold MEMLOG.rep, MEMLOG.would_recover_either, MEMLOG.would_recover_either'. cancel. cancel.
Qed.

Hint Extern 1 ({{_}} progseq (read_block _ _ _ _) _) => apply read_block_ok : prog.

Theorem read_block_recover_ok : forall fsxp inum off mscs,
  {<< m Fm Ftop tree pathname f B v,
  PRE    MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ (Fm * DIRTREE.rep fsxp Ftop tree)%pred (list2mem m) ]] *
         [[ DIRTREE.find_subtree pathname tree = Some (DIRTREE.TreeFile inum f) ]] *
         [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,r)
         MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
         [[ r = v ]]
  REC RET:^(mscs,fsxp)
         MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs
  >>} read_block fsxp inum off mscs >> recover.
Proof.
  intros.
  unfold forall_helper; intros m Fm Ftop tree pathname f B v.
  exists (MEMLOG.would_recover_either (FSXPMemLog fsxp) (sb_rep fsxp) m m).

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.

  cancel.
  cancel.
  eauto.
  eauto.
  step.
  eauto.
  autorewrite with crash_xform.
  cancel.
  step.
  rewrite H3. cancel.
Qed.

Definition write_block_inbounds T fsxp inum off v mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) inum off v mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, ok).

Theorem write_block_inbounds_ok : forall fsxp inum off v mscs,
  {< m Fm flist A f B v0,
  PRE     MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' flist' f',
          MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]]
  CRASH   MEMLOG.would_recover_either_pred (FSXPMemLog fsxp) (sb_rep fsxp) m (
          exists flist' f',
          (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred
  >} write_block_inbounds fsxp inum off v mscs.
Proof.
  unfold write_block_inbounds.
  hoare.
  rewrite <- MEMLOG.would_recover_either_pred_pimpl. cancel.
  admit.
  admit.
  admit.
Qed.

Hint Extern 1 ({{_}} progseq (write_block_inbounds _ _ _ _ _) _) => apply write_block_inbounds_ok : prog.

Theorem write_block_inbounds_recover_ok : forall fsxp inum off v mscs cachesize,
  {<< flist A f B v0 Fm m,
  PRE     [[ cachesize <> 0 ]] *
          MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist *
            [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
            [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]])%pred (list2mem m) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m',
          MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (exists flist' f', Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred (list2mem m') ]]
  REC RET:^(mscs,fsxp)
          MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m) mscs \/ exists m',
          MEMLOG.rep (FSXPMemLog fsxp) (sb_rep fsxp) (NoTransaction m') mscs *
          [[ (exists flist' f', Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred (list2mem m') ]]
  >>} write_block_inbounds fsxp inum off v mscs >> recover.
Proof.
  intros.
  unfold forall_helper; intros flist A f B v0 Fm m.
  exists (exists m' flist' f',
          MEMLOG.would_recover_either (FSXPMemLog fsxp) (sb_rep fsxp) m m' *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred.

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.

  cancel.
  eapply pimpl_ok2; eauto with prog.
  cancel.
  cancel.
  subst. apply pimpl_refl.
  cancel.
  subst. apply pimpl_refl.
  apply pimpl_refl.

  autorewrite with crash_xform.
  norm'l. unfold stars; simpl.
  autorewrite with crash_xform.
  norm'l. unfold stars; simpl.
  autorewrite with crash_xform.
  norm'l. unfold stars; simpl.
  autorewrite with crash_xform.
  cancel.

  step.
  rewrite H3. cancel. cancel.
  rewrite H3. cancel. cancel.
  rewrite H3. cancel.
Qed.


Definition set_size T fsxp inum size mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, ok) <- BFILE.bftrunc (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum size mscs;
  rx ^(mscs, ok).


Definition write_block T fsxp inum off v newsz mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, oldattr) <- BFILE.bfgetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  let^ (mscs, curlen) <- BFILE.bflen (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  mscs <- IfRx irx (wlt_dec off curlen) {
    irx mscs
  } else {
    let^ (mscs, ok) <- BFILE.bftrunc (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum (off ^+ $1) mscs;
    If (bool_dec ok true) {
      irx mscs
    } else {
      mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
      rx ^(mscs, false)
    }
  };
  mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) inum off v mscs;
  mscs <- IfRx irx (wlt_dec (INODE.ISize oldattr) newsz) {
    mscs <- BFILE.bfsetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum
                            (INODE.Build_iattr newsz
                                               (INODE.IMTime oldattr)
                                               (INODE.IType oldattr))
                            mscs;
    irx mscs
  } else {
    irx mscs
  };
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, ok).

Definition readdir T fsxp dnum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, files) <- SDIR.dslist (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) dnum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, files).

Definition create T fsxp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
  match oi with
  | None =>
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, None)
  | Some inum =>
    mscs <- BFILE.bfsetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum
                            (INODE.Build_iattr $0 $0 $0) mscs;
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    match ok with
    | true => rx ^(mscs, Some inum)
    | false => rx ^(mscs, None)
    end
  end.

Definition mksock T fsxp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, oi) <- DIRTREE.mkfile fsxp dnum name mscs;
  match oi with
  | None =>
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, None)
  | Some inum =>
    mscs <- BFILE.bfsetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum
                            (INODE.Build_iattr $0 $0 $1) mscs;
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    match ok with
    | true => rx ^(mscs, Some inum)
    | false => rx ^(mscs, None)
    end
  end.

Definition mkdir T fsxp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, oi) <- DIRTREE.mkdir fsxp dnum name mscs;
  match oi with
  | None =>
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, None)
  | Some inum =>
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    match ok with
    | true => rx ^(mscs, Some inum)
    | false => rx ^(mscs, None)
    end
  end.

Definition delete T fsxp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, ok) <- DIRTREE.delete fsxp dnum name mscs;
  If (bool_dec ok true) {
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, false)
  }.

Definition lookup T fsxp dnum names mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, r) <- DIRTREE.namei fsxp dnum names mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, r).

Definition rename T fsxp dsrc srcname ddst dstname mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, r) <- DIRTREE.rename fsxp dsrc srcname ddst dstname mscs;
  If (bool_dec r true) {
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, false)
  }.

Definition statfs T fsxp mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, free_blocks) <- BALLOC.numfree (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) mscs;
  let^ (mscs, free_inodes) <- BALLOC.numfree (FSXPMemLog fsxp) (FSXPInodeAlloc fsxp) mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, free_blocks, free_inodes).
