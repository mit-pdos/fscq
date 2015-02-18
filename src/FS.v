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
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
Require Import DirAlloc.

Set Implicit Arguments.
Import ListNotations.

Definition compute_xparams (cache_blocks data_bitmaps inode_bitmaps : addr) cache_blocks_ok :
  (MemLog.xparams * Inode.xparams * Balloc.xparams * Balloc.xparams * addr) :=
  let data_blocks := data_bitmaps ^* BALLOC.items_per_valu in
  let inode_blocks := inode_bitmaps ^* BALLOC.items_per_valu ^/ INODE.items_per_valu in
  let inode_base := data_blocks in
  let balloc_base := inode_base ^+ inode_blocks ^+ inode_bitmaps in
  let log_base := balloc_base ^+ data_bitmaps in
  let log_size := $ MEMLOG.addr_per_block in
  let max_addr := log_base ^+ $4 ^+ log_size in
  (MemLog.Build_xparams (@Cache.Build_xparams cache_blocks cache_blocks_ok)
                        log_base (log_base ^+ $1) (log_base ^+ $2) (log_base ^+ $3) log_size,
   Inode.Build_xparams inode_base inode_blocks,
   Balloc.Build_xparams (inode_base ^+ inode_blocks) inode_bitmaps,
   Balloc.Build_xparams balloc_base data_bitmaps,
   max_addr).

Definition file_len T lxp ixp inum mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, len) <- BFILE.bflen lxp ixp inum mscs;
  let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
  rx (mscs, len ^* $512).

Definition read_block T lxp ixp inum off mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, b) <- BFILE.bfread lxp ixp inum off mscs;
  let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
  rx (mscs, b).

Theorem read_block_ok : forall lxp bxp ixp inum off mscs,
  {< m F flist A f B v,
  PRE    MEMLOG.rep lxp (NoTransaction m) mscs *
         [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
         [[ (A * inum |-> f)%pred (list2mem flist) ]] *
         [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f)) ]]
  POST:(mscs',r)
         MEMLOG.rep lxp (NoTransaction m) mscs' *
         [[ r = v ]]
  CRASH  MEMLOG.log_intact lxp m
  >} read_block lxp ixp inum off mscs.
Proof.
(* XXX why doesn't this proof, which unfolds MEM.log_intact first, go through?
  unfold read_block, MEMLOG.log_intact.
  hoare.
  admit.
  unfold MEMLOG.log_intact; cancel.
*)

  unfold read_block.
  hoare.
  admit.
  unfold MEMLOG.log_intact; cancel.
  unfold MEMLOG.log_intact; cancel.
Qed.

Theorem read_block_recover_ok : forall lxp bxp ixp inum off mscs,
  {< m F flist A f B v,
  PRE     MEMLOG.rep lxp (NoTransaction m) mscs *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * inum |-> f)%pred (list2mem flist) ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f)) ]]
  POST:(mscs',r)
          MEMLOG.rep lxp (NoTransaction m) mscs' *
          [[ r = v ]]
  CRASH:mscs' MEMLOG.rep lxp (NoTransaction m) mscs'
  >} read_block lxp ixp inum off mscs >> MEMLOG.recover lxp.
Proof.
  intros.
  unfold forall_helper; intros m F flist A f B v.
  exists (MEMLOG.log_intact lxp m).

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply read_block_ok.
  eapply MEMLOG.recover_ok.

  cancel.
  step.
  cancel.
  cancel.
  rewrite crash_xform_sep_star_dist.
  instantiate (a:=m). instantiate (a0:=m).
  admit.

  step.
  admit.
Qed.

Definition write_block_inbounds T lxp ixp inum off v mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  mscs <- BFILE.bfwrite lxp ixp inum off v mscs;
  let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
  rx (mscs, ok).

Theorem write_block_inbounds_ok : forall lxp bxp ixp inum off v mscs,
  {< m F flist A f B v0,
  PRE     MEMLOG.rep lxp (NoTransaction m) mscs *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * inum |-> f)%pred (list2mem flist) ]] *
          [[ (B * off |-> v0)%pred (list2mem (BFILE.BFData f)) ]]
  POST:(mscs',ok)
          [[ ok = false ]] * MEMLOG.rep lxp (NoTransaction m) mscs' \/
          [[ ok = true ]] * exists m' flist' f',
          MEMLOG.rep lxp (NoTransaction m') mscs' *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  CRASH   MEMLOG.log_intact lxp m \/ exists m' flist' f',
          MEMLOG.log_intact lxp m' *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  >} write_block_inbounds lxp ixp inum off v mscs.
Proof.
  unfold write_block_inbounds.
  hoare.
  admit.
  unfold MEMLOG.log_intact; cancel.
  unfold MEMLOG.log_intact; cancel.
Qed.

Theorem write_block_inbounds_recover_ok : forall lxp bxp ixp inum off v mscs,
  {< m F flist A f B v0,
  PRE     MEMLOG.rep lxp (NoTransaction m) mscs *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * inum |-> f)%pred (list2mem flist) ]] *
          [[ (B * off |-> v0)%pred (list2mem (BFILE.BFData f)) ]]
  POST:(mscs',ok)
          [[ ok = false ]] * MEMLOG.rep lxp (NoTransaction m) mscs' \/
          [[ ok = true ]] * exists m' flist' f',
          MEMLOG.rep lxp (NoTransaction m') mscs' *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  CRASH:mscs'
          MEMLOG.rep lxp (NoTransaction m) mscs' \/ exists m' flist' f',
          MEMLOG.rep lxp (NoTransaction m') mscs' *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  >} write_block_inbounds lxp ixp inum off v mscs >> MEMLOG.recover lxp.
Proof.
  intros.
  unfold forall_helper; intros m F flist A f B v0.
  exists (MEMLOG.log_intact lxp m \/ exists m' flist' f',
          MEMLOG.log_intact lxp m' *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]])%pred.

  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply write_block_inbounds_ok.
  eapply MEMLOG.recover_ok.

  cancel.
  step.
  cancel.
  cancel.

  cancel.
  cancel.
  cancel.

  rewrite crash_xform_sep_star_dist.
  rewrite crash_xform_or_dist.
  cancel.
  admit.
  step.

  instantiate (p:=p). instantiate (a:=m). cancel.
  apply pimpl_or_r; left. cancel.

  instantiate (a0:=m). cancel.
  apply pimpl_or_r; left. cancel.

  cancel. apply pimpl_or_r; left.
  admit.

  admit.

  step.

  instantiate (p:=p).
  instantiate (a2:=m). cancel.
  apply pimpl_or_r; left. cancel.

  instantiate (a3:=m). cancel.
  apply pimpl_or_r; left. cancel.

  cancel.
  admit.
Qed.

Definition set_size_helper T lxp bxp ixp inum size mscs rx : prog T :=
  let2 (mscs, curlen) <- BFILE.bflen lxp ixp inum mscs;
  If (wlt_dec curlen size) {
    mscs <- For n < (size ^- curlen)
      Loopvar mscs <- mscs
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        let2 (mscs, ok) <- BFILE.bfgrow lxp bxp ixp inum mscs;
        If (bool_dec ok false) {
          rx (mscs, false)
        } else {
          lrx mscs
        }
    Rof;

    rx (mscs, true)
  } else {
    mscs <- For n < (curlen ^- size)
      Loopvar mscs <- mscs
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        mscs <- BFILE.bfshrink lxp bxp ixp inum mscs;
        lrx mscs
    Rof;

    rx (mscs, true)
  }.

Theorem set_size_helper_ok : forall lxp bxp ixp inum size mscs,
    {< F A mbase m flist f,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ # size <= INODE.blocks_per_inode ]] *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:(mscs',r)
             [[ r = false ]] * MEMLOG.log_intact lxp mbase \/
             [[ r = true ]] * exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * inum |-> f')%pred (list2mem flist') ]] *
             [[ BFILE.BFData f' = (firstn #size (BFILE.BFData f)) ++
                                  (MEMLOG.repeat (#size - length (BFILE.BFData f)) $0) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} set_size_helper lxp bxp ixp inum size mscs.
Proof.
  admit.
Qed.

Definition set_size T lxp bxp ixp inum size mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, ok) <- set_size_helper lxp bxp ixp inum size mscs;
  If (bool_dec ok true) {
    let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
    rx (mscs, ok)
  } else {
    mscs <- MEMLOG.abort lxp mscs;
    rx (mscs, false)
  }.

Definition write_block T lxp bxp ixp inum off v mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, curlen) <- BFILE.bflen lxp ixp inum mscs;
  If (wlt_dec off curlen) {
    mscs <- BFILE.bfwrite lxp ixp inum off v mscs;
    let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
    rx (mscs, ok)
  } else {
    let2 (mscs, ok) <- set_size_helper lxp bxp ixp inum (off ^+ $1) mscs;
    If (bool_dec ok false) {
      mscs <- MEMLOG.abort lxp mscs;
      rx (mscs, false)
    } else {
      mscs <- BFILE.bfwrite lxp ixp inum off v mscs;
      let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
      rx (mscs, ok)
    }
  }.

Definition readdir T lxp ixp dnum mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, files) <- SDIR.dslist lxp ixp dnum mscs;
  let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
  rx (mscs, files).

Definition create T lxp ibxp dbxp ixp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, oi) <- DIRALLOC.dacreate lxp ibxp dbxp ixp dnum name mscs;
  match oi with
  | None =>
    mscs <- MEMLOG.abort lxp mscs;
    rx (mscs, None)
  | Some inum =>
    let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
    match ok with
    | true => rx (mscs, Some inum)
    | false => rx (mscs, None)
    end
  end.

Definition delete T lxp ibxp dbxp ixp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, ok) <- DIRALLOC.dadelete lxp ibxp dbxp ixp dnum name mscs;
  If (bool_dec ok true) {
    let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
    rx (mscs, ok)
  } else {
    mscs <- MEMLOG.abort lxp mscs;
    rx (mscs, false)
  }.

Definition lookup T lxp bxp ixp dnum name mscs rx : prog T :=
  mscs <- MEMLOG.begin lxp mscs;
  let2 (mscs, r) <- SDIR.dslookup lxp bxp ixp dnum name mscs;
  let2 (mscs, ok) <- MEMLOG.commit lxp mscs;
  rx (mscs, r).
