Require Import Prog.
Require Import Word.
Require Import Rec.
Require Import List.
Require Import Pred.
Require Import Eqdep_dec.
Require Import Arith.
Require Import Hoare.
Require Import SepAuto.

Import ListNotations.
Set Implicit Arguments.

Record cache_xparams := {
  MaxCacheBlocks : addr;
  MaxCacheBlocksOK : MaxCacheBlocks <> $0
}.

Record memlog_xparams := {
  LogCache : cache_xparams;

  (* The actual data region is everything that's not described here *)
  LogHeader : addr; (* Store the header here *)
  LogCommit : addr; (* Store true to apply after crash. *)

  LogDescriptor : addr; (* Start of descriptor region in log *)
  LogData : addr; (* Start of data region in log *)
  LogLen : addr  (* Maximum number of entries in log; length but still use addr type *)
}.

Record balloc_xparams := {
  BmapStart : addr;
  BmapNBlocks : addr
}.

Record inode_xparams := {
  IXStart : addr;
  IXLen : addr
}.

Record fs_xparams := {
  FSXPMemLog : memlog_xparams;
  FSXPInode : inode_xparams;
  FSXPInodeAlloc : balloc_xparams;
  FSXPBlockAlloc : balloc_xparams;
  FSXPMaxBlock : addr
}.

Definition superblock_type : Rec.type := Rec.RecF ([
    ("log_header",  Rec.WordF addrlen);
    ("log_commit",  Rec.WordF addrlen);
    ("log_descr",   Rec.WordF addrlen);
    ("log_data",    Rec.WordF addrlen);
    ("log_len",     Rec.WordF addrlen);

    ("ixstart",     Rec.WordF addrlen);
    ("ixlen",       Rec.WordF addrlen);

    ("bastart",     Rec.WordF addrlen);
    ("banblocks",   Rec.WordF addrlen);

    ("iastart",     Rec.WordF addrlen);
    ("ianblocks",   Rec.WordF addrlen);

    ("maxblock",    Rec.WordF addrlen)
  ]).

Definition superblock_padded : Rec.type := Rec.RecF ([
    ("sb", superblock_type);
    ("pad", Rec.WordF (valulen - (Rec.len superblock_type)))
  ]).

Theorem superblock_padded_len :
  Rec.len superblock_padded = valulen.
Proof.
  simpl. rewrite valulen_is. compute. reflexivity.
Qed.

Definition superblock0 := @Rec.of_word superblock_type (wzero _).
Definition superblock_pad0 := @Rec.of_word superblock_padded (wzero _).

Definition pickle_superblock (fsxp : fs_xparams) : word (Rec.len superblock_padded) :=
  let (lxp, ixp, ibxp, dbxp, maxblock) := fsxp in
  let sb := superblock0
    :=> "log_header"  := (LogHeader lxp)
    :=> "log_commit"  := (LogCommit lxp)
    :=> "log_descr"   := (LogDescriptor lxp)
    :=> "log_data"    := (LogData lxp)
    :=> "log_len"     := (LogLen lxp)
    :=> "ixstart"     := (IXStart ixp)
    :=> "ixlen"       := (IXLen ixp)
    :=> "bastart"     := (BmapStart dbxp)
    :=> "banblocks"   := (BmapNBlocks dbxp)
    :=> "iastart"     := (BmapStart ibxp)
    :=> "ianblocks"   := (BmapNBlocks ibxp)
    :=> "maxblock"    := maxblock
  in Rec.to_word (superblock_pad0 :=> "sb" := sb).

Definition unpickle_superblock (sbp : word (Rec.len superblock_padded)) (cxp : cache_xparams) : fs_xparams :=
  let sb := ((Rec.of_word sbp) :-> "sb") in
  let lxp := Build_memlog_xparams cxp
    (sb :-> "log_header") (sb :-> "log_commit") (sb :-> "log_descr")
    (sb :-> "log_data") (sb :-> "log_len") in
  let ixp := Build_inode_xparams
    (sb :-> "ixstart") (sb :-> "ixlen") in
  let dbxp := Build_balloc_xparams
    (sb :-> "bastart") (sb :-> "banblocks") in
  let ibxp := Build_balloc_xparams
    (sb :-> "iastart") (sb :-> "ianblocks") in
  let maxblock := (sb :-> "maxblock") in
  Build_fs_xparams lxp ixp ibxp dbxp maxblock.

Theorem pickle_unpickle_superblock : forall fsxp,
  unpickle_superblock (pickle_superblock fsxp) (LogCache (FSXPMemLog fsxp)) = fsxp.
Proof.
  unfold pickle_superblock, unpickle_superblock.
  destruct fsxp.
  repeat rewrite Rec.of_to_id.
  destruct FSXPMemLog0.
  destruct FSXPInode0.
  destruct FSXPInodeAlloc0.
  destruct FSXPBlockAlloc0.
  unfold Rec.recget', Rec.recset'.
  simpl.
  reflexivity.

  unfold Rec.well_formed.
  simpl.
  intuition.
Qed.

Definition v_pickle_superblock (fsxp : fs_xparams) : valu.
  remember (pickle_superblock fsxp) as sb; clear Heqsb.
  rewrite superblock_padded_len in *.
  exact sb.
Defined.

Definition v_unpickle_superblock (v : valu) (cxp : cache_xparams) : fs_xparams.
  rewrite <- superblock_padded_len in *.
  exact (unpickle_superblock v cxp).
Defined.

Theorem v_pickle_unpickle_superblock : forall fsxp,
  v_unpickle_superblock (v_pickle_superblock fsxp) (LogCache (FSXPMemLog fsxp)) = fsxp.
Proof.
  intros.
  unfold v_pickle_superblock, v_unpickle_superblock.
  unfold eq_rec_r, eq_rec.
  rewrite eq_rect_nat_double.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  apply pickle_unpickle_superblock.
Qed.

Definition sb_rep (fsxp : fs_xparams) : @pred _ (@weq addrlen) _ :=
  ($0 |=> v_pickle_superblock fsxp)%pred.

Definition sb_load T cxp rx : prog T :=
  v <- Read $0;
  rx (v_unpickle_superblock v cxp).

Theorem sb_load_ok : forall cxp,
  {< fsxp,
  PRE    sb_rep fsxp
  POST:r sb_rep fsxp * [[ r = fsxp ]]
  CRASH  sb_rep fsxp
  >} sb_load cxp.
Proof.
  unfold sb_load.
  hoare.
  subst.
  (* XXX cache config is somewhat annoying *)
  (* rewrite v_pickle_unpickle_superblock. *)
  admit.
Qed.

Definition sb_init T fsxp rx : prog T :=
  Write $0 (v_pickle_superblock fsxp);;
  Sync $0;;
  rx tt.

Theorem sb_init_ok : forall fsxp,
  {< _:unit,
  PRE    $0 |->?
  POST:_ sb_rep fsxp
  CRASH  $0 |->?
  >} sb_init fsxp.
Proof.
  unfold sb_rep, sb_init.
  hoare.
Qed.
