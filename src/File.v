Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import Pack.
Require Import Inode.
Require Import Balloc.

Import ListNotations.

Set Implicit Arguments.

Module FILE.

  Definition fread' T lxp xp inum (off:addr) rx : prog T :=
    i <-INODE.iget lxp xp inum;     (* XXX check off < len? *)
    let blocknum := sel (i :-> "blocks") $0 $0 in
    fblock <- LOG.read lxp blocknum;
    rx fblock.

  Definition iget_blocknum ilist inum: addr := 
    let i := (sel ilist inum INODE.inode_zero) in
    let bn := sel (i :-> "blocks") $0 $0 in
    bn.

  Theorem fread'_ok : forall lxp xp inum off,
    {< F mbase m ilist bn v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilist * bn |-> v)% pred m ]] *
           [[ (inum < IXLen xp ^* INODE.items_per_valu)%word ]] *
           [[ bn = (iget_blocknum ilist inum) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v]]
    CRASH  LOG.log_intact lxp mbase
    >} fread' lxp xp inum off.
  Proof.
    unfold fread'.
    hoare.
    unfold iget_blocknum.
    instantiate (a2 := l). cancel.   
    unfold iget_blocknum in H3.
    cancel.
    LOG.unfold_intact.
    cancel.
  Qed.

  Definition fwrite' T lxp xp inum (off:addr) v rx : prog T :=
    i <-INODE.iget lxp xp inum;
    let blocknum := sel (i :-> "blocks") $0 $0 in
    ok <- LOG.write lxp blocknum v;
    rx ok.

  Theorem fwrite'_ok : forall lxp xp inum off v,
    {< F mbase m ilist bn v0,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilist * bn |-> v0)%pred m ]] *
           [[ (inum < $ (length ilist))%word ]] *
           [[ bn = iget_blocknum ilist inum ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = false ]] \/
           exists m', LOG.rep lxp (ActiveTxn mbase m') * [[ r = true ]] *
           [[ (F * INODE.rep xp ilist * bn |-> v)%pred m' ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite' lxp xp inum off v.
  Proof.
    unfold fwrite'.
    hoare.
    cancel.
    admit.
    cancel.
    LOG.unfold_intact.
    cancel.
  Qed.

  Record file := {
     FileLen : nat;   (* Just a representation invariant, not used in computation *)
    FileData : mem
  }.

  Definition empty_file := Build_file 0 (fun _ => None).

  Fixpoint blocks_ptto (fl : nat) (f : file) (i : INODE.inode) : pred :=
    match fl with
    | 0 => [[ emp (FileData f) ]]
    | S fl' => exists v, (sel (i :-> "blocks") ($ fl') $0) |-> v * blocks_ptto fl' f i
    end%pred.

  Fixpoint file_rep (l : list (INODE.inode * file)) : pred :=
    match l with
    | nil => emp
    | (i, f) :: rest =>
      (file_rep rest *
       [[ (i :-> "len") = $ (FileLen f) ]] *
       blocks_ptto (FileLen f) f i)%pred
    end.

  Definition rep xp (filelist : list file) :=
    (exists inodelist, INODE.rep xp inodelist *
     [[ length inodelist = length filelist ]] *
     file_rep (combine inodelist filelist))%pred.

  Definition fread T lxp xp inum (off:addr) rx : prog T :=
    fblock <- fread' lxp xp inum off;
    rx fblock.

  Theorem fread_ok : forall lxp xp inum off,
    {< F F' mbase m flist v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ (F' * off |-> v)%pred (FileData (sel flist inum empty_file)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp xp inum off.
  Proof.
    admit.
  Qed.

  Definition fwrite T lxp xp inum (off:addr) v rx : prog T :=
    ok <- fwrite' lxp xp inum off v;
    rx ok.

  Theorem fwrite_ok : forall lxp xp inum off v,
    {< F F' mbase m flist v0,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]] *
           [[ (F' * off |-> v0)%pred (FileData (sel flist inum empty_file)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = false ]] \/
           exists m' flist', LOG.rep lxp (ActiveTxn mbase m') * [[ r = true ]] *
           [[ (F * rep xp flist')%pred m ]] *
           [[ (F' * off |-> v)%pred (FileData (sel flist' inum empty_file)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite lxp xp inum off v.
  Proof.
    admit.
  Qed.

  Definition flen T lxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    rx (i :-> "len").

  Theorem flen_ok : forall lxp xp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = $ (FileLen (sel flist inum empty_file)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} flen lxp xp inum.
  Proof.
    admit.
  Qed.

  Definition fgrow T lxp bxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    bnum <- BALLOC.alloc lxp bxp;
    match bnum with
    | None => rx false
    | Some b =>
      let l' := i :-> "len" ^+ $1 in
      let i' := (i :=> "blocks" := (upd (i :-> "blocks") l' b) :=> "len" := l') in
      ok <- INODE.iput lxp xp inum i';
      If (bool_dec ok true) {
        rx true
      } else {
        (* This is pretty unfortunate: we allocated a block, but we couldn't
         * write it into the inode (presumably because the log ran out of space.
         * The theorem/spec of fgrow says that returning false leaves an active
         * transaction with some unspecified state, effectively requiring the
         * caller to abort.  But this isn't always true: one could also get a
         * false return from BALLOC.alloc returning false above, which leaves
         * the transaction in a clean state.  Maybe we could add a three-way
         * return value, with an "abort" value indicating such dead-end cases?
         *)
        rx false
      }
    end.

  Definition fshrink T lxp bxp xp inum rx : prog T :=
    i <- INODE.iget lxp xp inum;
    let l := i :-> "len" in
    ok <- BALLOC.free lxp bxp (sel (i :-> "blocks") $0 l);
    If (bool_dec ok true) {
      let i' := (i :=> "len" := l ^- $1) in
      ok <- INODE.iput lxp xp inum i';
      rx ok
    } else {
      rx false
    }.

  (* Note that for [fgrow_ok] and [fshrink_ok], a [false] return value
   * indicates that the transaction could be in any active state, so
   * the caller is effectively forced to abort.
   *)
  Theorem fgrow_ok : forall lxp bxp xp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r [[ r = false]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep xp flist')%pred m ]] *
           [[ FileLen (sel flist' inum empty_file) = FileLen (sel flist inum empty_file) + 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fgrow lxp bxp xp inum.
  Proof.
    admit.
  Qed.

  Theorem fshrink_ok : forall lxp bxp xp inum,
    {< F mbase m flist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp flist)%pred m ]] *
           [[ (inum < $ (length flist))%word ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist', LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep xp flist')%pred m ]] *
           [[ FileLen (sel flist' inum empty_file) = FileLen (sel flist inum empty_file) - 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink lxp bxp xp inum.
  Proof.
    admit.
  Qed.

End FILE.
