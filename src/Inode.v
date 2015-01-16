
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
Require Import GenSep.

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

  Definition inode' := Rec.data inodetype.
  Definition inode0' := @Rec.of_word inodetype $0.

  Definition itemsz := Rec.len inodetype.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (IXStart xp) (IXLen xp).

  Definition rep' xp (ilist : list inode') :=
    RecArray.array_item inodetype items_per_valu itemsz_ok (xp_to_raxp xp) ilist.

  Definition iget' T lxp xp inum rx : prog T :=
    RecArray.get inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum rx.

  Definition iput' T lxp xp inum i rx : prog T :=
    RecArray.put inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum i rx.

  Theorem iget_ok' : forall lxp xp inum,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep' xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel ilist inum inode0' ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget' lxp xp inum.
  Proof.
    unfold iget', rep'.
    intros. eapply pimpl_ok2. eapply RecArray.get_ok; word_neq.
    step.
  Qed.

  Theorem iput_ok' : forall lxp xp inum i,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep' xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]] *
           [[ Rec.well_formed i ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep' xp (upd ilist inum i))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput' lxp xp inum i.
  Proof.
    unfold iput', rep'.
    intros. eapply pimpl_ok2. eapply RecArray.put_ok; word_neq.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget' _ _ _) _) => apply iget_ok' : prog.
  Hint Extern 1 ({{_}} progseq (iput' _ _ _ _) _) => apply iput_ok' : prog.


  (* separation logic based theorems *)

  Record inode := {
    IBlocks : list addr
    (* add indirect link later *)
  }.

  Definition inode0 := Build_inode nil.

  Definition igetlen T lxp xp inum rx : prog T :=
    i <- iget' lxp xp inum;
    rx (i :-> "len").

  Definition iget T lxp xp inum off rx : prog T :=
    i <- iget' lxp xp inum ;
    rx (sel (i :-> "blocks") off $0).

  Definition iput T lxp xp inum off a rx : prog T :=
    i <- iget' lxp xp inum ;
    let i' := i :=> "blocks" := (upd (i :-> "blocks") off a) in
    iput' lxp xp inum i' rx.

  Definition igrow T lxp xp inum a rx : prog T :=
    i <- iget' lxp xp inum ;
    let i' := i :=> "blocks" := (upd (i :-> "blocks") (i :-> "len") a) in
    let i'' := i' :=> "len" := (i' :-> "len" ^+ $1) in
    iput' lxp xp inum i'' rx.

  Definition ishrink T lxp xp inum rx : prog T :=
    i <- iget' lxp xp inum ;
    let i' := i :=> "len" := (i :-> "len" ^- $1) in
    iput' lxp xp inum i' rx.

  Definition blocks_match i (i' : inode') :=
    forall off, off < length (IBlocks i)
    -> selN (IBlocks i) off $0 = selN (i' :-> "blocks") off $0.

  Definition inode_match i (i' : inode') :=
    (exists (b : addr), length (IBlocks i) <= wordToNat b) /\
    length (IBlocks i) = wordToNat (i' :-> "len") /\
    blocks_match i i'.

  Definition rep xp (ilist : list inode) :=
    (exists ilist', rep' xp ilist' *
     [[ length ilist = length ilist' ]] * 
     [[ forall i, inode_match (selN ilist i inode0) (selN ilist' i inode0') ]])%pred.

  Definition inum_valid inum xp (ilist : list inode) :=
      (inum < IXLen xp ^* items_per_valu)%word /\
      wordToNat inum < length ilist.

  Definition off_valid (off : addr) ino :=
    wordToNat off < length (IBlocks ino).

  Hint Unfold inum_valid.
  Hint Unfold off_valid.


  Ltac destruct_hyp H := match type of H with
    | _ /\ _ => let X := fresh in
              destruct H as [H X]; destruct_hyp H; destruct_hyp X
    | ex _ => destruct H
    | _ => idtac
  end.

  Ltac specialize_inode_match inum := match goal with
    | [ H: forall _, inode_match _ _ |- _ ] =>
      let X := fresh in 
          pose proof (H (wordToNat inum)) as X;
          unfold inode_match in X;
          destruct_hyp X; clear H
  end.

  Ltac specialize_inode_match_off inum off := match goal with
    | [ H: forall _, inode_match _ _ |- _ ] =>
         specialize_inode_match inum; 
         match goal with
           | [ H: blocks_match _ _ |- _ ] =>
             let X := fresh in
                unfold blocks_match in H;
                pose proof (H (wordToNat off)) as X; clear H
          end
  end.

  Ltac inode_simpl' := match goal with
    | [ H: (_ * ?inum |-> ?i)%pred (list2mem ?il) |- context [?i] ] =>
      match type of i with
      | inode => replace i with (sel il inum inode0) by (erewrite list2mem_sel; eauto)
      | addr => replace i with (sel il inum $0) by (erewrite list2mem_sel; eauto)
      end
    | [ H: (_ * ?inum |-> ?i)%pred (list2mem ?il), H2: context [?i] |- _ ] =>
      match type of i with
      | inode => replace i with (sel il inum inode0) in H2 by (erewrite list2mem_sel; eauto)
      | addr => replace i with (sel il inum $0) in H2 by (erewrite list2mem_sel; eauto)
      end
  end.

  Ltac inode_simpl := repeat inode_simpl'; subst.

  Theorem igetlen_ok : forall lxp xp inum,
    {< F A mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ inum_valid inum xp ilist ]] *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = $ (length (IBlocks ino)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} igetlen lxp xp inum.
  Proof.
    unfold igetlen, rep, inum_valid.
    hoare.

    specialize_inode_match inum.
    inode_simpl.
    apply wordToNat_inj; erewrite wordToNat_natToWord_bound; eauto.
  Qed.

  Theorem iget_ok : forall lxp xp inum off,
    {< F A B mbase m ilist ino a,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ inum_valid inum xp ilist /\ off_valid off ino ]] *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ (B * off |-> a)%pred (list2mem (IBlocks ino)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = a ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp inum off.
  Proof.
    unfold iget, rep, inum_valid, off_valid.
    hoare.
    specialize_inode_match_off inum off.
    inode_simpl.
    intuition.
  Qed.

  Theorem iput_ok : forall lxp xp inum off a,
    {< F A B mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ inum_valid inum xp ilist /\ off_valid off ino ]] *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ (B * off |->?)%pred (list2mem (IBlocks ino)) ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m' ilist' ino',
            LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp ilist')%pred m' ]] *
            [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
            [[ (B * off |-> a)%pred (list2mem (IBlocks ino')) ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp inum off a.
  Proof.
    unfold iput, rep, inum_valid, off_valid.
    hoare.
    admit.
  Qed.


End INODE.
