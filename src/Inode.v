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
Require Import AddrMap.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
    IXLen : addr
}.

Module INODE.
  Definition inodetype : Rec.rectype := [("len", addrlen); ("block0", addrlen)].
  Definition inode := Rec.recdata inodetype.

  Definition inode2valu (i : inode) : valu.
    (* XXX how to convert a recdata to a word? *)
  Admitted.

  Definition valu2inode (v : valu) : inode.
    (* XXX how to truncate the 4096-bit valu down to an inode? *)
  Admitted.

  Theorem inode2valu2inode: forall i,
    valu2inode (inode2valu i) = i.
  Admitted.

  Definition rep xp (imap : addr -> inode) :=
    array (IXStart xp)
          (map (fun i => inode2valu (imap $ i)) (seq 0 (wordToNat (IXLen xp)))) $1.

  Definition fupd T (m : addr -> T) a v :=
    fun a' => if addr_eq_dec a a' then v else m a'.

  Definition iget T lxp xp inum rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) inum $1 ;
    rx (valu2inode v).

  Definition iput T lxp xp inum i rx : prog T :=
    ok <- LOG.write_array lxp (IXStart xp) inum $1 (inode2valu i) ;
    rx ok.

  Theorem iget_ok : forall lxp xp inum,
    {< F mbase m imap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp imap)%pred m ]] *
           [[ (inum < IXLen xp)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = imap inum ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp inum.
  Proof.
    admit.
  Qed.

  Theorem iput_ok : forall lxp xp inum i,
    {< F mbase m imap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp imap)%pred m ]] *
           [[ (inum < IXLen xp)%word ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp (fupd imap inum i))%pred m ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp inum i.
  Proof.
    admit.
  Qed.

End INODE.
