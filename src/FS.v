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

Definition mkfs T data_bitmaps inode_bitmaps cachesize rx : prog T :=
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

Definition file_nblocks T fsxp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, len) <- BFILE.bflen (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, len).

Definition file_get_attr T fsxp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, attr) <- BFILE.bfgetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, attr).

Definition file_get_sz T fsxp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, attr) <- BFILE.bfgetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, INODE.ISize attr).

Definition file_set_sz T fsxp inum sz mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, attr) <- BFILE.bfgetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  mscs <- BFILE.bfsetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum
                          (INODE.Build_iattr sz
                                             (INODE.IMTime attr)
                                             (INODE.IType attr))
                          mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, ok).

Definition read_block T fsxp inum off mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, b) <- BFILE.bfread (FSXPMemLog fsxp) (FSXPInode fsxp) inum off mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, b).

Theorem read_block_ok : forall fsxp inum off mscs,
  {< m F flist A f B v,
  PRE    MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs *
         [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
         [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
         [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,r)
         MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs *
         [[ r = v ]]
  CRASH  MEMLOG.log_intact (FSXPMemLog fsxp) m m
  >} read_block fsxp inum off mscs.
Proof.
  unfold read_block.
  hoare_unfold MEMLOG.log_intact_unfold.
Qed.


Theorem read_block_recover_ok : forall fsxp inum off mscs cachesize,
  {<< m F flist A f B v,
  PRE     [[ cachesize <> 0 ]] *
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs *
          [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,r)
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs *
          [[ r = v ]]
  REC RET:^(mscs,fsxp)
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs
  >>} read_block fsxp inum off mscs >> MEMLOG.recover cachesize.
Proof.
  intros.
  unfold forall_helper; intros m F flist A f B v.
  exists (MEMLOG.log_intact (FSXPMemLog fsxp) m m).

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply read_block_ok.
  eapply MEMLOG.recover_ok.

  cancel.
  step.
  cancel.
  cancel.
  unfold MEMLOG.log_intact.
  autorewrite with crash_xform.
  rewrite sep_star_or_distr.
  apply pimpl_or_l.
  cancel.
  autorewrite with crash_xform.
  rewrite sep_star_comm.
  apply pimpl_or_r; left; cancel.

  unfold MEMLOG.log_intact in *.
  step.
  rewrite H3; cancel.
  cancel.

  unfold MEMLOG.log_intact in *.
  apply pimpl_or_r; right; cancel.
  step.
  rewrite H3; cancel.
  cancel.
Qed.

Definition write_block_inbounds T fsxp inum off v mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) inum off v mscs;
  let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx ^(mscs, ok).

Theorem write_block_inbounds_ok : forall fsxp inum off v mscs,
  {< m F flist A f B v0,
  PRE     MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs *
          [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m' flist' f',
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m') mscs *
          [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]]
  CRASH   MEMLOG.would_recover_old (FSXPMemLog fsxp) m \/ exists m' flist' f',
          MEMLOG.would_recover_either (FSXPMemLog fsxp) m m' *
          [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]]
  >} write_block_inbounds fsxp inum off v mscs.
Proof.
  unfold write_block_inbounds.
  hoare_unfold MEMLOG.log_intact_unfold.
Qed.

Definition write_block_inbounds' fsxp inum off v T := @write_block_inbounds T fsxp inum off v.

Theorem write_block_inbounds_recover_ok : forall fsxp inum off v mscs cachesize,
  {<< flist A f B v0 F m,
  PRE     [[ cachesize <> 0 ]] *
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs *
          [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist *
            [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
            [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]])%pred (list2mem m) ]]
  POST RET:^(mscs,ok)
          [[ ok = false ]] * MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs \/
          [[ ok = true ]] * exists m',
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m') mscs *
          [[ (exists flist' f', F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred (list2mem m') ]]
  REC RET:^(mscs,fsxp)
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m) mscs \/ exists m',
          MEMLOG.rep (FSXPMemLog fsxp) (NoTransaction m') mscs *
          [[ (exists flist' f', F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred (list2mem m') ]]
  >>} write_block_inbounds fsxp inum off v mscs >> MEMLOG.recover cachesize.
Proof.
  intros.
  (*unfold forall_helper at 1 2 3 4 5; intros flist A f B v0 F.
  Check (MEMLOG.recover_corr2_to_corr3 (write_block_inbounds' fsxp inum off v)
    (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist *
            [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
            [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]] )
    (exists flist' f', F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist' *
            [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
            [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred).*)

  unfold forall_helper; intros flist A f B v0 F m.
  exists (MEMLOG.would_recover_old (FSXPMemLog fsxp) m \/ exists m' flist' f',
          MEMLOG.would_recover_either (FSXPMemLog fsxp) m m' *
          [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]])%pred.

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply write_block_inbounds_ok.
  eapply MEMLOG.recover_ok.

  cancel.
  step.
  cancel.
  cancel.
  auto.
  unfold MEMLOG.log_intact.
  autorewrite with crash_xform.
  rewrite sep_star_or_distr.
  apply pimpl_or_l.
  cancel.
  autorewrite with crash_xform.
  apply pimpl_or_r; left; cancel.

  step.
  rewrite sep_star_or_distr.
  apply pimpl_or_r; left; cancel.
  rewrite H3; auto.
  rewrite H3; cancel.
  apply pimpl_or_r; left; cancel.

  rewrite H3.
  autorewrite with crash_xform.
  norm'l; unfold stars; simpl.
  autorewrite with crash_xform.
  norm'l; unfold stars; simpl.
  autorewrite with crash_xform.
  norm'l; unfold stars; simpl.
  autorewrite with crash_xform.
  cancel.
  apply pimpl_or_r; right.
  norm.
  (* XXX do this without the instantiate *)
  instantiate (p := (p * [[(F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) l)%pred (list2mem d)]] *
    [[(A * # (inum) |-> b)%pred (list2nmem l)]] * [[(B * # (off) |-> v)%pred (list2nmem (BFILE.BFData b))]])%pred).
  cancel.
  intuition.

  eapply pimpl_ok2; [ eauto |].
  intros; norm.
  unfold stars; simpl.
  cancel.
  cancel.
  intuition.
  subst.
  auto.
  unfold stars; simpl.
  cancel.
  apply pimpl_or_r; right.
  (* XXX don't know that fsxp = b0 *)
  admit.
  admit.
  admit.
Qed.

Definition set_size_helper T fsxp inum size mscs rx : prog T :=
  let^ (mscs, curlen) <- BFILE.bflen (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  If (wlt_dec curlen size) {
    let^ (mscs) <- For n < (size ^- curlen)
      Ghost [ (_:unit) ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        let^ (mscs, ok) <- BFILE.bfgrow (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum mscs;
        If (bool_dec ok false) {
          rx ^(mscs, false)
        } else {
          lrx ^(mscs)
        }
    Rof ^(mscs);

    rx ^(mscs, true)
  } else {
    let^ (mscs) <- For n < (curlen ^- size)
      Ghost [ (_:unit) ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        mscs <- BFILE.bfshrink (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum mscs;
        lrx ^(mscs)
    Rof ^(mscs);

    rx ^(mscs, true)
  }.

Theorem set_size_helper_ok : forall fsxp inum size mscs,
    {< F A mbase m flist f,
    PRE      MEMLOG.rep (FSXPMemLog fsxp) (ActiveTxn mbase m) mscs *
             [[ # size <= INODE.blocks_per_inode ]] *
             [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:^(mscs,r)
             [[ r = false ]] * MEMLOG.would_recover_old (FSXPMemLog fsxp) mbase \/
             [[ r = true ]] * exists m' flist' f',
             MEMLOG.rep (FSXPMemLog fsxp) (ActiveTxn mbase m') mscs *
             [[ (F * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ BFILE.BFData f' = (firstn #size (BFILE.BFData f)) ++
                                  (repeat $0 (#size - length (BFILE.BFData f))) ]]
    CRASH    MEMLOG.would_recover_old (FSXPMemLog fsxp) mbase
    >} set_size_helper fsxp inum size mscs.
Proof.
  admit.
Qed.

Definition set_size T fsxp inum size mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, ok) <- set_size_helper fsxp inum size mscs;
  If (bool_dec ok true) {
    let^ (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
    rx ^(mscs, ok)
  } else {
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs;
    rx ^(mscs, false)
  }.

Definition write_block T fsxp inum off v newsz mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  let^ (mscs, oldattr) <- BFILE.bfgetattr (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  let^ (mscs, curlen) <- BFILE.bflen (FSXPMemLog fsxp) (FSXPInode fsxp) inum mscs;
  mscs <- IfRx irx (wlt_dec off curlen) {
    irx mscs
  } else {
    let^ (mscs, ok) <- set_size_helper fsxp inum (off ^+ $1) mscs;
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
