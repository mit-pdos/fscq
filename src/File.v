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
Require Import Inode.
Require Import Balloc.
Require Import WordAuto.
Require Import GenSep.
Import ListNotations.

Set Implicit Arguments.

Module FILE.

  (* interface implementation *)

  Definition fread T lxp ixp inum off rx : prog T :=
    b <-INODE.iget lxp ixp inum off;
    fblock <- LOG.read lxp b;
    rx fblock.

  Definition fwrite T lxp ixp inum off v rx : prog T :=
    b <-INODE.iget lxp ixp inum off;
    ok <- LOG.write lxp b v;
    rx ok.

  Definition flen T lxp ixp inum rx : prog T :=
    n <- INODE.igetlen lxp ixp inum;
    rx n.

  Definition fgrow T lxp bxp ixp inum rx : prog T :=
    bnum <- BALLOC.alloc lxp bxp;
    match bnum with
    | None => rx false
    | Some b =>
        ok <- INODE.igrow lxp ixp inum b;
        rx ok
    end.

  Definition fshrink T lxp bxp ixp inum rx : prog T :=
    n <- INODE.igetlen lxp ixp inum;
    b <- INODE.iget lxp ixp inum n;
    ok <- BALLOC.free lxp bxp b;
    If (bool_dec ok true) {
      ok <- INODE.ishrink lxp ixp inum;
      rx ok
    } else {
      rx false
    }.



  (* representation invariants *)

  Record file := {
    FData : list valu
  }.

  Definition file0 := Build_file nil.

  Definition data_match (x : addr * valu) : @pred valu :=
    fst x |-> snd x.

  Definition file_match (x : INODE.inode * file) : @pred valu := (
    [[ length (INODE.IBlocks (fst x)) = length (FData (snd x)) ]] *
    listpred data_match (combine (INODE.IBlocks (fst x)) (FData (snd x)))
    )%pred.

  Definition rep bxp ixp (flist : list file) :=
    (exists freeblocks ilist,
     BALLOC.rep bxp freeblocks * INODE.rep ixp ilist *
     [[ length ilist = length flist ]] *
     listpred file_match (combine ilist flist))%pred.



  (* correctness theorems *)

  Theorem fread_ok : forall lxp bxp ixp inum off,
    {<F A B mbase m flist f v,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ wordToNat inum < length flist /\ wordToNat off < length (FData f) ]] *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]] *
           [[ (B * off |-> v)%pred (list2mem (FData f)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = v ]]
    CRASH  LOG.log_intact lxp mbase
    >} fread lxp ixp inum off.
  Proof.
    admit.
  Qed.

  Lemma fwrite_ok : forall lxp bxp ixp inum off v,
    {<F A B mbase m flist f v0,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ wordToNat inum < length flist /\ wordToNat off < length (FData f) ]] *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]] *
           [[ (B * off |-> v0)%pred (list2mem (FData f)) ]]
    POST:r [[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m) \/
           [[ r = true  ]] * exists m' flist' f',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f')%pred (list2mem flist') ]] *
           [[ (B * off |-> v)%pred (list2mem (FData f')) ]]
    CRASH  LOG.log_intact lxp mbase
    >} fwrite lxp ixp inum off v.
  Proof.
    admit.
  Qed.


  Theorem flen_ok : forall lxp bxp ixp inum,
    {< F A mbase m flist f,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ wordToNat inum < length flist ]] *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = $ (length (FData f)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} flen lxp ixp inum.
  Proof.
    admit.
  Qed.


  Theorem fgrow_ok : forall lxp bxp ixp inum,
    {< F A mbase m flist f,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ wordToNat inum < length flist ]] *
           [[ length (FData f) < INODE.blocks_per_inode ]] *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:r [[ r = false]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true ]] * exists m' flist' f',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep bxp ixp flist')%pred m' ]] *
           [[ (A * inum |-> f')%pred (list2mem flist') ]] *
           [[ length (FData f') = length (FData f) + 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fgrow lxp bxp ixp inum.
  Proof.
    admit.
  Qed.


  Theorem fshrink_ok : forall lxp bxp ixp inum,
    {< F A mbase m flist f,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ wordToNat inum < length flist /\ length (FData f) > 0 ]] *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true  ]] * exists m' flist' f',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep bxp ixp flist')%pred m' ]] *
           [[ (A * inum |-> f')%pred (list2mem flist') ]] *
           [[ length (FData f') = length (FData f) - 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink lxp bxp ixp inum.
  Proof.
    admit.
  Qed.

End FILE.
