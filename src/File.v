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

  Definition fread T lxp xp inum (off:addr) rx : prog T :=
    (* XXX should computing iblock and ipos be foldable into iget? *)
    let bn := off ^/ $ valulen in
    let boff := off ^% $ valulen in
    i <-INODE.iget lxp xp inum;     (* XXX check off < len? *)
    let blocknum := i :-> "block0" in
    fblock <- LOG.read lxp blocknum;
    rx fblock.

  (* XXX part of Inode.v? *) 
  Definition iget_blocknum ilistlist iblock ipos : addr := 
    let i := (sel ilist inum INODE.inode_zero) in
    let bn := i :-> "block0" in
    bn.                             

  Theorem fread_ok : forall lxp xp inum off,
    {< F mbase m ilist bn v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilistlist)% pred m ]] *
           [[ bn = (iget_blocknum ilist inum) ]] *
           [[ exists F', (bn |-> v * F') m]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp xp inum off.
    

End FILE.


