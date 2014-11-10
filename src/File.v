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

Import ListNotations.

Set Implicit Arguments.

Module FILE.

  Definition fread' T lxp xp inum (off:addr) rx : prog T :=
    i <-INODE.iget lxp xp inum;     (* XXX check off < len? *)
    let blocknum := i :-> "block0" in
    fblock <- LOG.read lxp blocknum;
    rx fblock.

  (* XXX part of Inode.v? *) 
  Definition iget_blocknum ilist inum: addr := 
    let i := (sel ilist inum INODE.inode_zero) in
    let bn := i :-> "block0" in
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
     admit.
  Qed.

  Definition fwrite' T lxp xp inum (off:addr) v rx : prog T :=
    i <-INODE.iget lxp xp inum;
    let blocknum := i :-> "block0" in
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
           [[ (F * INODE.rep xp ilist * bn |-> v)%pred m ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite' lxp xp inum off v.
  Proof.
    admit.
  Qed.

  Record file := {
     FileLen : nat;   (* Just a representation invariant, not used in computation *)
    FileData : mem
  }.

  Definition empty_file := Build_file 0 (fun _ => None).

  Fixpoint file_rep (l : list (INODE.inode * file)) : pred :=
    match l with
    | nil => emp
    | (i, f) :: rest =>
      (file_rep rest *
       [[ (i :-> "len") = $ (FileLen f) ]] *
       exists v0 v1 v2,
       (i :-> "block0") |-> v0 * (i :-> "block1") |-> v1 * (i :-> "block2") |-> v2 *
       [[ ($0 |-> v0 * $1 |-> v1 * $2 |-> v2)%pred (FileData f) ]] * [[ FileLen f = 3 ]] \/
       (i :-> "block0") |-> v0 * (i :-> "block1") |-> v1 *
       [[ ($0 |-> v0 * $1 |-> v1)%pred (FileData f) ]] * [[ FileLen f = 2 ]] \/
       (i :-> "block0") |-> v0 *
       [[ ($0 |-> v0)%pred (FileData f) ]] * [[ FileLen f = 1 ]] \/
       [[ emp (FileData f) ]] * [[ FileLen f = 0 ]])%pred
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

End FILE.
