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

  Definition fileblock := (valu)%type.
  Definition file := list fileblock.   (* XXX list of bytes? *)

  Definition fread T lxp xp inum (off:addr) rx : prog T :=
    (* XXX should computing iblock and ipos be foldable into iget? *)
    let iblock :=  inum ^/ INODE.items_per_valu in
    let ipos := inum ^% INODE.items_per_valu in
    let bn := off ^/ $ valulen in
    let boff := off ^% $ valulen in
    i <-INODE.iget lxp xp iblock ipos;     (* XXX check off < len? *)
    let blocknum := i :-> "block0" in
    fblock <- LOG.read lxp blocknum;
    rx fblock.


  (* XXX need a rep for file and use rep in PRE/POST/CRASH *)
  Theorem fread_ok : forall lxp xp inum off,
    {< F mbase m (f: file),
    PRE    LOG.rep lxp (ActiveTxn mbase m)
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[r = sel f $0]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp xp inum off.
    


End FILE.


