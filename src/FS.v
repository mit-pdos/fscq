Require Import Prog.
Require Import MemLog.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred.
Require Import Dir.
Require Import Hoare.
Require Import GenSep.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.

Set Implicit Arguments.
Import ListNotations.

Definition file_len T lxp ixp inum rx : prog T :=
  ms <- MEMLOG.begin lxp;
  len <- BFILE.bflen lxp ixp inum ms;
  _ <- MEMLOG.commit lxp ms;
  rx (len ^* $512).

Definition read_block T lxp ixp inum off rx : prog T :=
  ms <- MEMLOG.begin lxp;
  b <- BFILE.bfread lxp ixp inum off ms;
  _ <- MEMLOG.commit lxp ms;
  rx b.

Theorem read_block_ok : forall lxp bxp ixp inum off,
  {< m F flist A f B v,
  PRE    MEMLOG.rep lxp (NoTransaction m) ms_empty *
         [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
         [[ (A * inum |-> f)%pred (list2mem flist) ]] *
         [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f)) ]]
  POST:r MEMLOG.rep lxp (NoTransaction m) ms_empty *
         [[ r = v ]]
  CRASH  MEMLOG.log_intact lxp m
  >} read_block lxp ixp inum off.
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

Theorem read_block_recover_ok : forall lxp bxp ixp inum off,
  {< m F flist A f B v,
  PRE     MEMLOG.rep lxp (NoTransaction m) ms_empty *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * inum |-> f)%pred (list2mem flist) ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f)) ]]
  POST:r  MEMLOG.rep lxp (NoTransaction m) ms_empty *
          [[ r = v ]]
  CRASH:_ MEMLOG.rep lxp (NoTransaction m) ms_empty
  >} read_block lxp ixp inum off >> MEMLOG.recover lxp.
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

Definition write_block_inbounds T lxp ixp inum off v rx : prog T :=
  ms <- MEMLOG.begin lxp;
  ms <- BFILE.bfwrite lxp ixp inum off v ms;
  ok <- MEMLOG.commit lxp ms;
  rx ok.

Theorem write_block_inbounds_ok : forall lxp bxp ixp inum off v,
  {< m F flist A f B v0,
  PRE     MEMLOG.rep lxp (NoTransaction m) ms_empty *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * inum |-> f)%pred (list2mem flist) ]] *
          [[ (B * off |-> v0)%pred (list2mem (BFILE.BFData f)) ]]
  POST:ok [[ ok = false ]] * MEMLOG.rep lxp (NoTransaction m) ms_empty \/
          [[ ok = true ]] * exists m' flist' f',
          MEMLOG.rep lxp (NoTransaction m') ms_empty *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  CRASH   MEMLOG.log_intact lxp m \/ exists m' flist' f',
          MEMLOG.log_intact lxp m' *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  >} write_block_inbounds lxp ixp inum off v.
Proof.
  unfold write_block_inbounds.
  hoare.
  admit.
  unfold MEMLOG.log_intact; cancel.
  unfold MEMLOG.log_intact; cancel.
Qed.

Theorem write_block_inbounds_recover_ok : forall lxp bxp ixp inum off v,
  {< m F flist A f B v0,
  PRE     MEMLOG.rep lxp (NoTransaction m) ms_empty *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * inum |-> f)%pred (list2mem flist) ]] *
          [[ (B * off |-> v0)%pred (list2mem (BFILE.BFData f)) ]]
  POST:ok [[ ok = false ]] * MEMLOG.rep lxp (NoTransaction m) ms_empty \/
          [[ ok = true ]] * exists m' flist' f',
          MEMLOG.rep lxp (NoTransaction m') ms_empty *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  CRASH:_ MEMLOG.rep lxp (NoTransaction m) ms_empty \/ exists m' flist' f',
          MEMLOG.rep lxp (NoTransaction m') ms_empty *
          [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
          [[ (A * inum |-> f')%pred (list2mem flist') ]] *
          [[ (B * off |-> v)%pred (list2mem (BFILE.BFData f')) ]]
  >} write_block_inbounds lxp ixp inum off v >> MEMLOG.recover lxp.
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

Definition set_size_helper T lxp bxp ixp inum size ms rx : prog T :=
  curlen <- BFILE.bflen lxp ixp inum ms;
  If (wlt_dec curlen size) {
    ms <- For n < (size ^- curlen)
      Loopvar ms <- ms
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        r <- BFILE.bfgrow lxp bxp ixp inum ms;
        let (ok, ms) := r in
        If (bool_dec ok false) {
          MEMLOG.abort lxp ms;;
          rx (false, ms)
        } else {
          lrx ms
        }
    Rof;

    rx (true, ms)
  } else {
    ms <- For n < (curlen ^- size)
      Loopvar ms <- ms
      Continuation lrx
      Invariant emp
      OnCrash emp
      Begin
        ms <- BFILE.bfshrink lxp bxp ixp inum ms;
        lrx ms
    Rof;

    rx (true, ms)
  }.

Theorem set_size_helper_ok : forall lxp bxp ixp inum size ms,
    {< F A mbase m flist f,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ # size <= INODE.blocks_per_inode ]] *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:rms [[ fst rms = false ]] * MEMLOG.log_intact lxp mbase \/
             [[ fst rms = true ]] * exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') (snd rms) *
             [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * inum |-> f')%pred (list2mem flist') ]] *
             [[ BFILE.BFData f' = (firstn #size (BFILE.BFData f)) ++
                                  (MEMLOG.repeat (#size - length (BFILE.BFData f)) $0) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} set_size_helper lxp bxp ixp inum size ms.
Proof.
  admit.
Qed.

Definition set_size T lxp bxp ixp inum size rx : prog T :=
  ms <- MEMLOG.begin lxp;
  r <- set_size_helper lxp bxp ixp inum size ms;
  let (ok, ms) := r in
  If (bool_dec ok true) {
    ok <- MEMLOG.commit lxp ms;
    rx ok
  } else {
    MEMLOG.abort lxp ms;;
    rx false
  }.

Definition write_block T lxp bxp ixp inum off v rx : prog T :=
  ms <- MEMLOG.begin lxp;
  curlen <- BFILE.bflen lxp ixp inum ms;
  If (wlt_dec off curlen) {
    ms <- BFILE.bfwrite lxp ixp inum off v ms;
    ok <- MEMLOG.commit lxp ms;
    rx ok
  } else {
    r <- set_size_helper lxp bxp ixp inum (off ^+ $1) ms;
    let (ok, ms) := r in
    If (bool_dec ok false) {
      MEMLOG.abort lxp ms;;
      rx false
    } else {
      ms <- BFILE.bfwrite lxp ixp inum off v ms;
      ok <- MEMLOG.commit lxp ms;
      rx ok
    }
  }.

Definition readdir T lxp ixp dnum rx : prog T :=
  ms <- MEMLOG.begin lxp;
  files <- DIR.dlist lxp ixp dnum ms;
  _ <- MEMLOG.commit lxp ms;
  rx files.
