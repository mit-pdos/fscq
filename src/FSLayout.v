Require Import Prog.
Require Import Word.
Require Import Rec.
Require Import List.
Require Import Pred PredCrash.
Require Import Eqdep_dec.
Require Import Arith.
Require Import Hoare.
Require Import SepAuto.
Require Import Cache.
Require Import AsyncDisk.
Require Import Omega.

Import ListNotations.
Set Implicit Arguments.

Record log_xparams := {
  DataStart : addr; (* Where the actual data section starts *)
  LogHeader : addr; (* Store the header here *)

  LogDescriptor : addr; (* Start of descriptor region in log *)
  LogDescLen : addr; (* Number of descriptor blocks *)
  LogData : addr;    (* Start of data region in log *)
  LogLen : addr      (* Maximum number of entries in log; length but still use addr type *)
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
  FSXPLog : log_xparams;
  FSXPInode : inode_xparams;
  FSXPInodeAlloc : balloc_xparams;
  FSXPBlockAlloc : balloc_xparams;
  FSXPRootInum : addr;
  FSXPMaxBlock : addr
}.

Definition log_xparams_ok xp :=
  goodSize addrlen (DataStart xp) /\
  goodSize addrlen (LogHeader xp) /\
  goodSize addrlen ((LogDescriptor xp) + (LogDescLen xp)) /\
  goodSize addrlen ((LogData xp) + (LogLen xp)).

Definition balloc_xparams_ok xp :=
  goodSize addrlen ((BmapStart xp) + (BmapNBlocks xp)).

Definition inode_xparams_ok xp :=
  goodSize addrlen ((IXStart xp) + (IXLen xp)).

Definition fs_xparams_ok xp :=
  log_xparams_ok (FSXPLog xp) /\
  inode_xparams_ok (FSXPInode xp) /\
  balloc_xparams_ok (FSXPBlockAlloc xp) /\
  balloc_xparams_ok (FSXPInodeAlloc xp) /\
  goodSize addrlen (FSXPRootInum xp) /\
  goodSize addrlen (FSXPMaxBlock xp).

Lemma goodSize_add_l : forall sz a b,
  goodSize sz (a + b) -> goodSize sz a.
Proof.
  intros; eapply goodSize_trans with (n2 := a + b); auto; omega.
Qed.

Lemma goodSize_add_r : forall sz a b,
  goodSize sz (a + b) -> goodSize sz b.
Proof.
  intros; eapply goodSize_trans with (n2 := a + b); auto; omega.
Qed.

Local Hint Resolve goodSize_add_l goodSize_add_r.

Ltac xparams_ok := 
  match goal with 
  | [ H: fs_xparams_ok ?xp |- goodSize _ _ ] =>
    unfold fs_xparams_ok, log_xparams_ok, balloc_xparams_ok, inode_xparams_ok in H;
    intuition; eauto
  end.


Definition superblock_type : Rec.type := Rec.RecF ([
    ("data_start",  Rec.WordF addrlen);
    ("log_header",  Rec.WordF addrlen);
    ("log_descr",   Rec.WordF addrlen);
    ("log_descrlen",   Rec.WordF addrlen);
    ("log_data",    Rec.WordF addrlen);
    ("log_len",     Rec.WordF addrlen);

    ("ixstart",     Rec.WordF addrlen);
    ("ixlen",       Rec.WordF addrlen);

    ("bastart",     Rec.WordF addrlen);
    ("banblocks",   Rec.WordF addrlen);

    ("iastart",     Rec.WordF addrlen);
    ("ianblocks",   Rec.WordF addrlen);

    ("root_inum",   Rec.WordF addrlen);
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

Definition addr2w (a : addr) : waddr := natToWord addrlen a.

Definition pickle_superblock (fsxp : fs_xparams) : word (Rec.len superblock_padded) :=
  let (lxp, ixp, ibxp, dbxp, rootinum, maxblock) := fsxp in
  let sb := superblock0
    :=> "data_start"  := addr2w (DataStart lxp)
    :=> "log_header"  := addr2w (LogHeader lxp)
    :=> "log_descr"   := addr2w (LogDescriptor lxp)
    :=> "log_descrlen":= addr2w (LogDescLen lxp)
    :=> "log_data"    := addr2w (LogData lxp)
    :=> "log_len"     := addr2w (LogLen lxp)
    :=> "ixstart"     := addr2w (IXStart ixp)
    :=> "ixlen"       := addr2w (IXLen ixp)
    :=> "bastart"     := addr2w (BmapStart dbxp)
    :=> "banblocks"   := addr2w (BmapNBlocks dbxp)
    :=> "iastart"     := addr2w (BmapStart ibxp)
    :=> "ianblocks"   := addr2w (BmapNBlocks ibxp)
    :=> "root_inum"   := addr2w rootinum
    :=> "maxblock"    := addr2w maxblock
  in Rec.to_word (superblock_pad0 :=> "sb" := sb).

Definition unpickle_superblock (sbp : word (Rec.len superblock_padded)) : fs_xparams :=
  let sb := ((Rec.of_word sbp) :-> "sb") in
  let lxp := Build_log_xparams
    # (sb :-> "data_start") # (sb :-> "log_header")
    # (sb :-> "log_descr") # (sb :-> "log_descrlen")
    # (sb :-> "log_data") # (sb :-> "log_len") in
  let ixp := Build_inode_xparams
    # (sb :-> "ixstart") # (sb :-> "ixlen") in
  let dbxp := Build_balloc_xparams
    # (sb :-> "bastart") # (sb :-> "banblocks") in
  let ibxp := Build_balloc_xparams
    # (sb :-> "iastart") # (sb :-> "ianblocks") in
  let rootinum := # (sb :-> "root_inum") in
  let maxblock := # (sb :-> "maxblock") in
  Build_fs_xparams lxp ixp ibxp dbxp rootinum maxblock.

Theorem pickle_unpickle_superblock : forall fsxp,
  fs_xparams_ok fsxp ->
  unpickle_superblock (pickle_superblock fsxp) = fsxp.
Proof.
  unfold pickle_superblock, unpickle_superblock.
  destruct fsxp.
  repeat rewrite Rec.of_to_id.
  destruct FSXPLog0.
  destruct FSXPInode0.
  destruct FSXPInodeAlloc0.
  destruct FSXPBlockAlloc0.
  unfold Rec.recget', Rec.recset'.
  unfold addr2w; simpl; intros.
  repeat rewrite wordToNat_natToWord_idempotent' by xparams_ok.
  auto.
  unfold Rec.well_formed.
  simpl.
  intuition.
Qed.

Definition v_pickle_superblock (fsxp : fs_xparams) : valu.
  remember (pickle_superblock fsxp) as sb; clear Heqsb.
  rewrite superblock_padded_len in *.
  exact sb.
Defined.

Definition v_unpickle_superblock (v : valu) : fs_xparams.
  rewrite <- superblock_padded_len in *.
  exact (unpickle_superblock v).
Defined.

Theorem v_pickle_unpickle_superblock : forall fsxp,
  fs_xparams_ok fsxp ->
  v_unpickle_superblock (v_pickle_superblock fsxp) = fsxp.
Proof.
  intros.
  unfold v_pickle_superblock, v_unpickle_superblock.
  unfold eq_rec_r, eq_rec.
  rewrite eq_rect_nat_double.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  apply pickle_unpickle_superblock; auto.
Qed.

Definition sb_rep (fsxp : fs_xparams) : rawpred :=
  ([[ fs_xparams_ok fsxp ]] * 0 |=> v_pickle_superblock fsxp)%pred.

Definition sb_load T cs rx : prog T :=
  let^ (cs, v) <- BUFCACHE.read 0 cs;
  rx ^(cs, v_unpickle_superblock v).

Theorem sb_load_ok : forall cs,
  {< m F fsxp,
  PRE
    BUFCACHE.rep cs m * [[ (F * sb_rep fsxp)%pred m ]]
  POST RET:^(cs',r)
    BUFCACHE.rep cs' m * [[ r = fsxp ]]
  CRASH
    exists cs', BUFCACHE.rep cs' m
  >} sb_load cs.
Proof.
  unfold sb_load, sb_rep.
  hoare.
  subst; apply v_pickle_unpickle_superblock; auto.
Qed.

Definition sb_init T fsxp cs rx : prog T :=
  cs <- BUFCACHE.write 0 (v_pickle_superblock fsxp) cs;
  cs <- BUFCACHE.sync 0 cs;
  rx cs.

Theorem sb_init_ok : forall fsxp cs,
  {< m F,
  PRE
    BUFCACHE.rep cs m * [[ fs_xparams_ok fsxp /\ (F * 0 |->?)%pred m ]]
  POST RET:cs
    exists m',
    BUFCACHE.rep cs m' * [[ (F * sb_rep fsxp)%pred m' ]]
  CRASH
    exists cs' m', BUFCACHE.rep cs' m' * [[ (F * 0 |->?)%pred m' ]]
  >} sb_init fsxp cs.
Proof.
  unfold sb_rep, sb_init.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq (sb_load _) _) => apply sb_load_ok : prog.
Hint Extern 1 ({{_}} progseq (sb_init _ _) _) => apply sb_init_ok : prog.

Theorem crash_xform_sb_rep : forall fsxp,
  crash_xform (sb_rep fsxp) =p=> sb_rep fsxp.
Proof.
  unfold sb_rep; intros.
  autorewrite with crash_xform.
  cancel.
Qed.

Hint Rewrite crash_xform_sb_rep : crash_xform.

Hint Extern 0 (okToUnify (sb_rep _) (sb_rep _)) => constructor : okToUnify.
