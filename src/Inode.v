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
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArray.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
  IXLen : addr
}.

Module INODE.
  Definition blocks_per_inode := 3.
  Definition inodetype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) blocks_per_inode)]).

  Definition inode := Rec.data inodetype.
  Definition inode_zero := @Rec.of_word inodetype $0.

  Definition itemsz := Rec.len inodetype.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition blocktype : Rec.type := Rec.ArrayF inodetype (wordToNat items_per_valu).
  Definition block := Rec.data blocktype.
  Definition block_zero := @Rec.of_word blocktype $0.

  Theorem blocksz : Rec.len blocktype = valulen.
    rewrite valulen_is; auto.
  Qed.

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (IXStart xp) (IXLen xp).

  Definition rep xp (ilist : list inode) :=
    RecArray.array_item inodetype items_per_valu itemsz_ok (xp_to_raxp xp) ilist.

  Definition iget T lxp xp inum rx : prog T :=
    RecArray.get inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum rx.

  Definition iput T lxp xp inum i rx : prog T :=
    RecArray.put inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum i rx.

  Theorem iget_ok : forall lxp xp inum,
    {< F F' mbase m ilist idata,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (F' * inum |-> idata)%pred (list2mem ilist) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = idata ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp inum.
  Proof.
    unfold iget, rep.
    intros. eapply pimpl_ok2. eapply RecArray.get_ok; word_neq.
    step.
  Qed.

  Theorem iput_ok : forall lxp xp inum i,
    {< F F' mbase m ilist oldidata,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (F' * inum |-> oldidata)%pred (list2mem ilist) ]] *
           [[ Rec.well_formed i ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m' ilist', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp ilist')%pred m' ]] *
            [[ (F' * inum |-> i)%pred (list2mem ilist) ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp inum i.
  Proof.
    unfold iput, rep.
    intros. eapply pimpl_ok2. eapply RecArray.put_ok; word_neq.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _) _) => apply iput_ok : prog.

End INODE.
