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

  (* XXX part of Inode.v?  XXX I want to reason about an addr that could be the value
  * for "block0".  I think i want 
  *
  * word (Rec.field_type p) 
  *
  * but i get: : 
  *    match  Rec.fieldp inodetype "block0" with 
  *      | Some p => word (Rec.field_type p) '
  *      | None  => True end 
  *) 
  Definition iget_blocknum ilist inum : addr :=
    (sel ilist inum INODE.inode_zero) :-> "block0".

  Theorem fread_ok : forall lxp xp inum off,
    {< F F' mbase m ilist bn v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * INODE.rep xp ilist)%pred m ]] *
           [[ bn = iget_blocknum ilist inum ]] *
           [[ exists F', (bn |-> v * F') m]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp xp inum off.
    

End FILE.


