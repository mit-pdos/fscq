Require Import Coq.Strings.String.
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
Require Import FSLayout.

Import ListNotations.
Set Implicit Arguments.

Module SB.

  Local Hint Resolve goodSize_add_l goodSize_add_r.

  Definition magic_number := # (natToWord addrlen 3932).  (* 0xF5C = FSC in C *)

  Definition superblock_type : Rec.type := Rec.RecF ([
      ("data_start",  Rec.WordF addrlen);
      ("log_header",  Rec.WordF addrlen);
      ("log_descr",   Rec.WordF addrlen);
      ("log_descrlen",   Rec.WordF addrlen);
      ("log_data",    Rec.WordF addrlen);
      ("log_len",     Rec.WordF addrlen);

      ("ixstart",     Rec.WordF addrlen);
      ("ixlen",       Rec.WordF addrlen);

      ("bastart1",    Rec.WordF addrlen);
      ("banblocks1",  Rec.WordF addrlen);
      ("bastart2",    Rec.WordF addrlen);
      ("banblocks2",  Rec.WordF addrlen);

      ("iastart",     Rec.WordF addrlen);
      ("ianblocks",   Rec.WordF addrlen);

      ("root_inum",   Rec.WordF addrlen);
      ("maxblock",    Rec.WordF addrlen);
      ("magic",       Rec.WordF addrlen)  
    ]).

  Definition superblock_padded : Rec.type := Rec.RecF ([
      ("sb", superblock_type);
      ("pad", Rec.WordF (valulen - (Rec.len superblock_type)))
    ]).

  Theorem superblock_padded_len :
    Rec.len superblock_padded = valulen.
  Proof.
    simpl. rewrite valulen_is. apply Nat.eqb_eq.
    compute. reflexivity.
  Qed.

  Definition superblock0 := @Rec.of_word superblock_type (wzero _).
  Definition superblock_pad0 := @Rec.of_word superblock_padded (wzero _).

  Definition pickle_superblock (fsxp : fs_xparams) : word (Rec.len superblock_padded) :=
    let (lxp, ixp, dbxp1, dbxp2, ibxp, rootinum, maxblock, magic) := fsxp in
    let sb := superblock0
      :=> "data_start"  := addr2w (DataStart lxp)
      :=> "log_header"  := addr2w (LogHeader lxp)
      :=> "log_descr"   := addr2w (LogDescriptor lxp)
      :=> "log_descrlen":= addr2w (LogDescLen lxp)
      :=> "log_data"    := addr2w (LogData lxp)
      :=> "log_len"     := addr2w (LogLen lxp)
      :=> "ixstart"     := addr2w (IXStart ixp)
      :=> "ixlen"       := addr2w (IXLen ixp)
      :=> "bastart1"    := addr2w (BmapStart dbxp1)
      :=> "banblocks1"  := addr2w (BmapNBlocks dbxp1)
      :=> "bastart2"    := addr2w (BmapStart dbxp2)
      :=> "banblocks2"  := addr2w (BmapNBlocks dbxp2)
      :=> "iastart"     := addr2w (BmapStart ibxp)
      :=> "ianblocks"   := addr2w (BmapNBlocks ibxp)
      :=> "root_inum"   := addr2w rootinum
      :=> "maxblock"    := addr2w maxblock
      :=> "magic"       := addr2w magic
    in Rec.to_word (superblock_pad0 :=> "sb" := sb).

  Definition unpickle_superblock (sbp : word (Rec.len superblock_padded)) : fs_xparams :=
    let sb := ((Rec.of_word sbp) :-> "sb") in
    let lxp := Build_log_xparams
      # (sb :-> "data_start") # (sb :-> "log_header")
      # (sb :-> "log_descr") # (sb :-> "log_descrlen")
      # (sb :-> "log_data") # (sb :-> "log_len") in
    let ixp := Build_inode_xparams
      # (sb :-> "ixstart") # (sb :-> "ixlen") in
    let dbxp1 := Build_balloc_xparams
      # (sb :-> "bastart1") # (sb :-> "banblocks1") in
    let dbxp2 := Build_balloc_xparams
      # (sb :-> "bastart2") # (sb :-> "banblocks2") in
    let ibxp := Build_balloc_xparams
      # (sb :-> "iastart") # (sb :-> "ianblocks") in
    let rootinum := # (sb :-> "root_inum") in
    let maxblock := # (sb :-> "maxblock") in
    let magic := # (sb :-> "magic") in
    Build_fs_xparams lxp ixp dbxp1 dbxp2 ibxp rootinum maxblock magic.


  Theorem pickle_unpickle_superblock : forall fsxp,
    fs_xparams_ok fsxp ->
    unpickle_superblock (pickle_superblock fsxp) = fsxp.
  Proof.
    unfold pickle_superblock, unpickle_superblock.
    destruct fsxp.
    repeat rewrite Rec.of_to_id.
    destruct FSXPLog.
    destruct FSXPInode.
    destruct FSXPInodeAlloc.
    destruct FSXPBlockAlloc1.
    destruct FSXPBlockAlloc2.
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

  Theorem goodSize_magic_number :
    goodSize addrlen magic_number.
  Proof.
    unfold magic_number.
    eapply wordToNat_natToWord_idempotent'_iff; eauto.
  Qed.

  Definition rep (fsxp : fs_xparams) : rawpred :=
    ([[ fs_xparams_ok fsxp ]] *
     [[ FSXPMagic fsxp = magic_number ]] *
     0 |+> (v_pickle_superblock fsxp, nil))%pred.

  Definition load cs :=
    let^ (cs, v) <- BUFCACHE.read 0 cs;
    Ret ^(cs, v_unpickle_superblock v).

  Theorem load_ok : forall cs,
    {< m F fsxp,
    PRE:hm
      BUFCACHE.rep cs m * [[ (F * rep fsxp)%pred m ]]
    POST:hm' RET:^(cs',r)
      BUFCACHE.rep cs' m * [[ r = fsxp ]]
    CRASH:hm'
      exists cs', BUFCACHE.rep cs' m
    >} load cs.
  Proof.
    unfold load, rep.
    hoare.
    apply v_pickle_unpickle_superblock; auto.
  Qed.

  Definition init fsxp cs :=
    cs <- BUFCACHE.write 0 (v_pickle_superblock fsxp) cs;
    cs <- BUFCACHE.begin_sync cs;
    cs <- BUFCACHE.sync 0 cs;
    cs <- BUFCACHE.end_sync cs;
    Ret cs.

  Theorem init_ok : forall fsxp cs,
    {< m F,
    PRE:hm
      BUFCACHE.rep cs m * 
      [[ fs_xparams_ok fsxp ]] *
      [[ FSXPMagic fsxp = magic_number ]] *
      [[ (F * 0 |->?)%pred m ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:cs
      exists m',
      BUFCACHE.rep cs m' * [[ (F * rep fsxp)%pred m' ]]
    XCRASH:hm'
      exists cs' m' vs, BUFCACHE.rep cs' m' * 
      [[ (F * 0 |+> vs)%pred m' ]]
    >} init fsxp cs.
  Proof.
    unfold rep, init.
    step.
    rewrite ptsto_pimpl_ptsto_subset; cancel.
    hoare.
    xcrash.
    xcrash.
    xcrash.
    xcrash.
  Qed.

  Hint Extern 1 ({{_}} Bind (load _) _) => apply load_ok : prog.
  Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.

  Theorem crash_xform_rep : forall fsxp,
    crash_xform (rep fsxp) <=p=> rep fsxp.
  Proof.
    unfold rep; intros; split;
    rewrite crash_xform_sep_star_dist;
    rewrite crash_xform_sep_star_dist;
    repeat rewrite crash_xform_lift_empty.

    rewrite crash_xform_ptsto_subset; cancel.
    rewrite ptsto_pimpl_ptsto_subset.
    subst; auto.

    rewrite <- crash_xform_ptsto_subset_r.
    cancel.
    rewrite ptsto_subset_pimpl_ptsto; eauto.
    unfold vsmerge; simpl; auto.
  Qed.

  Hint Rewrite crash_xform_rep : crash_xform.

  Theorem sync_invariant_rep : forall xp,
    sync_invariant (rep xp).
  Proof.
    unfold rep; eauto.
  Qed.

  Hint Resolve sync_invariant_rep.
  Hint Extern 0 (okToUnify (rep _) (rep _)) => constructor : okToUnify.

  Theorem rep_magic_number : forall fsxp,
    rep fsxp =p=> rep fsxp * [[ FSXPMagic fsxp = magic_number ]].
  Proof.
    unfold rep; intros; cancel.
  Qed.

End SB.
