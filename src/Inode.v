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

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
    IXLen : addr
}.

Module INODE.
  Inductive alloc_state :=
  | Avail
  | InUse.

  Record inode := mkinode {
    IFree: alloc_state;
    ILen: addr;
    IBlocks: addr -> addr
  }.

  Definition alloc_state_to_bits a : addr :=
    match a with
    | Avail => $0
    | InUse => $1
    end.

  Definition bits_to_alloc_state (a : addr) : alloc_state :=
    if (weq a $0) then Avail else InUse.

  Notation "a ^++ b" := (@Word.combine _ a _ b) (at level 55, left associativity).

  Definition inodelen := (addrlen + addrlen + addrlen + addrlen).

  Definition inode_pack (i : inode) : word inodelen :=
    let (f, l, b) := i in
    (alloc_state_to_bits f) ^++ l ^++ (b $0) ^++ (b $1).

  Notation "a ^-- sz" := ((@Word.split1 sz _ a), (@Word.split2 sz _ a)) (at level 55).

  Definition inode_unpack (w : word inodelen) : inode :=
    let (f, w) := w ^-- addrlen in
    let (l, w) := w ^-- addrlen in
    let (b0, w) := w ^-- addrlen in
    let (b1, w) := w ^-- addrlen in
    mkinode (bits_to_alloc_state f) l
            (fun x => if weq x $0 then b0 else b1).

  Theorem inode_pack_unpack : forall i,
    inode_unpack (inode_pack i) = i.
  Proof.
    destruct i.
    unfold inode_unpack, inode_pack.
    f_equal.
    (* XXX rewrite split2_combine, split1_combine? *)
    (* XXX not quite correct because of addrs other than $0 and $1 in IBlocks;
     * should IBlocks be a fixed-length list instead?  or a list with an extra
     * Prop field in inode about the length of that list?
     *)
  Abort.

  Lemma inodelen_valulen : inodelen + (valulen - inodelen) = valulen.
  Proof.
    rewrite valulen_is.
    auto.
  Qed.

  Definition inodew2valu (w : word inodelen) : valu.
    set (zext w (valulen-inodelen)) as r.
    rewrite inodelen_valulen in r.
    apply r.
  Defined.

  Definition valu2inodew (v : valu) : word inodelen.
    rewrite <- inodelen_valulen in v.
    apply (split1 inodelen (valulen-inodelen) v).
  Defined.

  Theorem inodew2valu2inodew : forall i,
    valu2inodew (inodew2valu i) = i.
  Proof.
    unfold valu2inodew, inodew2valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- inodelen_valulen.
    do 2 (rewrite <- eq_rect_eq_dec; try apply eq_nat_dec).
    apply split1_combine.
  Qed.

  Definition rep xp (imap : addr -> inode) :=
    array (IXStart xp)
          (map (fun i => inode_to_valu (imap $ i)) (seq 0 (wordToNat (IXLen xp)))).



End INODE.
