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
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.


Module Type BlockPtrSig.

  Parameter irec     : Type.               (* inode record type *)
  Parameter iattr    : Type.               (* part of irec that BlockPtr does not touch *)
  Parameter NDirect  : addr.               (* number of direct blocks *)

  (* Number of direct blocks should be quite small to avoid word overflow 
     Using addrlen as its bound is arbitrary *)
  Parameter NDirect_bound : NDirect <= addrlen.

  Parameter IRLen    : irec -> addr.       (* get length *)
  Parameter IRIndPtr : irec -> addr.       (* get indirect block pointer *)
  Parameter IRBlocks : irec -> list waddr. (* get direct block numbers *)
  Parameter IRAttrs  : irec -> iattr.      (* get untouched attributes *)

  (* setters *)
  Parameter upd_len  : irec -> addr -> irec.
  Parameter upd_irec : forall (r : irec) (len : addr) (ibptr : addr) (dbns : list waddr), irec.

  (* getter/setter lemmas *)
  Parameter upd_len_get_len    : forall ir n, goodSize addrlen n -> IRLen (upd_len ir n) = n.
  Parameter upd_len_get_ind    : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
  Parameter upd_len_get_blk    : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
  Parameter upd_len_get_iattr  : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.

  Parameter upd_irec_get_len   : forall ir len ibptr dbns,
     goodSize addrlen len -> IRLen (upd_irec ir len ibptr dbns) = len.
  Parameter upd_irec_get_ind   : forall ir len ibptr dbns,
     goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dbns) = ibptr.
  Parameter upd_irec_get_blk   : forall ir len ibptr dbns,
     IRBlocks (upd_irec ir len ibptr dbns) = dbns.
  Parameter upd_irec_get_iattr : forall ir len ibptr dbns,
      IRAttrs (upd_irec ir len ibptr dbns) = IRAttrs ir.

End BlockPtrSig.


(* block pointer abstraction for individule inode *)
Module BlockPtr (BPtr : BlockPtrSig).

  Import BPtr.


  (* RecArray for indirect blocks *)

  Definition indrectype := Rec.WordF addrlen.

  Module IndSig <: RASig.

    Definition xparams := addr.
    Definition RAStart := fun (x : xparams) => x.
    Definition RALen := fun (_ : xparams) => 1.
    Definition xparams_ok (_ : xparams) := True.

    Definition itemtype := indrectype.
    Definition items_per_val := valulen / (Rec.len itemtype).

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val.
      rewrite valulen_is; compute; auto.
    Qed.

  End IndSig.

  Module IndRec  := LogRecArray IndSig.
  Hint Extern 0 (okToUnify (IndRec.rep _ _) (IndRec.rep _ _)) => constructor : okToUnify.

  Notation "'NIndirect'" := IndSig.items_per_val.
  Notation "'NBlocks'"   := (NDirect + NIndirect)%nat.

  (* Various bounds *)
  Lemma NIndirect_is : NIndirect = 512.
  Proof.
    unfold IndSig.items_per_val.
    rewrite valulen_is; compute; auto.
  Qed.

  Lemma NBlocks_roundtrip : # (natToWord addrlen NBlocks) = NBlocks.
  Proof.
    unfold IndSig.items_per_val.
    erewrite wordToNat_natToWord_bound with (bound:=$ valulen).
    reflexivity.
    eapply le_trans.
    eapply plus_le_compat_r.
    apply NDirect_bound.
    apply Nat.sub_0_le.
    rewrite valulen_is.
    compute; reflexivity.
  Qed.

  Lemma NDirect_roundtrip : # (natToWord addrlen NDirect) = NDirect.
  Proof.
    intros.
    eapply wordToNat_natToWord_bound with (bound := natToWord addrlen NBlocks).
    rewrite NBlocks_roundtrip; omega.
  Qed.

  Lemma NIndirect_roundtrip : # (natToWord addrlen NIndirect) = NIndirect.
  Proof.
    intros.
    eapply wordToNat_natToWord_bound with (bound := natToWord addrlen NBlocks).
    rewrite NBlocks_roundtrip; omega.
  Qed.

  Lemma le_ndirect_goodSize : forall n,
    n <= NDirect -> goodSize addrlen n.
  Proof.
    intros; eapply goodSize_word_bound; eauto.
    rewrite NDirect_roundtrip; auto.
  Qed.

  Lemma le_nindirect_goodSize : forall n,
    n <= NIndirect -> goodSize addrlen n.
  Proof.
    intros; eapply goodSize_word_bound; eauto.
    rewrite NIndirect_roundtrip; auto.
  Qed.

  Lemma le_nblocks_goodSize : forall n,
    n <= NBlocks -> goodSize addrlen n.
  Proof.
    intros; eapply goodSize_word_bound; eauto.
    rewrite NBlocks_roundtrip; auto.
  Qed.

  Local Hint Resolve le_ndirect_goodSize le_nindirect_goodSize le_nblocks_goodSize.


  (************* program *)

  Definition get T lxp (ir : irec) off ms rx : prog T :=
    If (lt_dec off NDirect) {
      rx ^(ms, selN (IRBlocks ir) off $0)
    } else {
      let^ (ms, v) <- IndRec.get lxp (IRIndPtr ir) (off - NDirect) ms;
      rx ^(ms, v)
    }.


  Definition read T lxp (ir : irec) ms rx : prog T :=
    If (le_dec (IRLen ir) NDirect) {
      rx ^(ms, firstn (IRLen ir) (IRBlocks ir))
    } else {
      let^ (ms, indbns) <- IndRec.read lxp (IRIndPtr ir) 1 ms;
      rx ^(ms, (firstn (IRLen ir) ((IRBlocks ir) ++ indbns)))
    }.


  Definition free_ind_dec ol nl :
    { ol > NDirect /\ nl <= NDirect } + { ol <= NDirect \/ nl > NDirect }.
  Proof.
    destruct (gt_dec ol NDirect).
    destruct (le_dec nl NDirect).
    left; split; assumption.
    right; right; apply not_le; assumption.
    right; left; apply not_gt; assumption.
  Defined.


  Definition shrink T lxp bxp (ir : irec) nr ms rx : prog T :=
    let nl := ((IRLen ir) - nr) in
    If (free_ind_dec (IRLen ir) nl) {
      ms <- BALLOC.free lxp bxp (IRIndPtr ir) ms;
      rx ^(ms, upd_len ir nl)
    } else {
      rx ^(ms, upd_len ir nl)
    }.


  Definition grow T lxp bxp (ir : irec) bn ms rx : prog T :=
    let len := (IRLen ir) in
    If (lt_dec len NDirect) {
      (* change direct block address *)
      rx ^(ms, Some (upd_irec ir (S len) (IRIndPtr ir) (updN (IRBlocks ir) len bn)))
    } else {
      (* allocate indirect block if necessary *)
      let^ (ms, ibn) <- IfRx irx (addr_eq_dec len NDirect) {
        let^ (ms, r) <- BALLOC.alloc lxp bxp ms;
        match r with
        | None => rx ^(ms, None)
        | Some ibn =>
            ms <- IndRec.init lxp ibn ms;
            irx ^(ms, ibn)
        end
      } else {
        irx ^(ms, (IRIndPtr ir))
      };
      (* write indirect block *)
      ms <- IndRec.put lxp ibn (len - NDirect) bn ms;
      rx ^(ms, Some (upd_irec ir (S len) ibn (IRBlocks ir)))
    }.


  (************** rep invariant *)

  Definition indrep bxp (l : list waddr) ibn indlist :=
    ( [[ length l <= NDirect ]] \/
      [[ length l > NDirect /\ length indlist = NIndirect /\ BALLOC.bn_valid bxp ibn ]] *
      IndRec.rep ibn indlist )%pred.


  Definition rep bxp (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp l (IRIndPtr ir) indlist *
      [[ l = firstn (length l) ((IRBlocks ir) ++ indlist) ]] )%pred.

  Definition rep_direct (ir : irec) (l : list waddr) : @pred _ addr_eq_dec valuset :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l <= NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      [[ l = firstn (length l) (IRBlocks ir) ]] )%pred.

  Definition rep_indirect bxp (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l > NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, IndRec.rep (IRIndPtr ir) indlist *
      [[ length indlist = NIndirect /\ BALLOC.bn_valid bxp (IRIndPtr ir) ]] *
      [[ l = (IRBlocks ir) ++ firstn (length l - NDirect) indlist ]] )%pred.

  (* Necessary to make subst work when there's a recursive term like:
     l = firstn (length l) ... *)
  Set Regular Subst Tactic.

  Lemma rep_piff_direct : forall bxp ir l,
    length l <= NDirect ->
    rep bxp ir l <=p=> rep_direct ir l.
  Proof.
    unfold rep, indrep, rep_direct; intros; split; cancel; try omega.
    substl l at 1; rewrite firstn_app_l by omega; auto.
    rewrite app_nil_r; auto.
  Qed.


  Lemma rep_piff_indirect : forall bxp ir l,
    length l > NDirect ->
    rep bxp ir l <=p=> rep_indirect bxp ir l.
  Proof.
    unfold rep, indrep, rep_indirect; intros; split; cancel; try omega.
    rewrite <- firstn_app_r; setoid_rewrite H3.
    replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    substl l at 1; rewrite <- firstn_app_r. setoid_rewrite H3.
    replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    Unshelve. eauto.
  Qed.


  Lemma rep_selN_direct_ok : forall F bxp ir l m off,
    (F * rep bxp ir l)%pred m ->
    off < NDirect ->
    off < length l ->
    selN (IRBlocks ir) off $0 = selN l off $0.
  Proof.
    unfold rep, indrep; intros; destruct_lift H.
    substl.
    rewrite selN_firstn by auto.
    rewrite selN_app1 by omega; auto.
  Qed.


  Theorem get_ok : forall lxp bxp ir off ms,
    {< F Fm m0 m l,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: Fm * rep bxp ir l ]]] *
           [[ off < length l ]]
    POST RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = selN l off $0 ]]
    CRASH  LOG.intact lxp F m0
    >} get lxp ir off ms.
  Proof.
    unfold get.
    step.
    step.
    eapply rep_selN_direct_ok; eauto.

    prestep; norml.
    rewrite rep_piff_indirect in H by omega.
    unfold rep_indirect in H; destruct_lift H; cancel; try omega.
    step; substl.
    substl NDirect; rewrite selN_app2.
    rewrite selN_firstn by omega; auto.
    omega.
  Qed.


  Theorem read_ok : forall lxp bxp ir ms,
    {< F Fm m0 m l,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: Fm * rep bxp ir l ]]]
    POST RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = l ]]
    CRASH  LOG.intact lxp F m0
    >} read lxp ir ms.
  Proof.
    unfold read.
    step; denote rep as Hx.
    step.
    rewrite rep_piff_direct in Hx; unfold rep_direct in Hx; destruct_lift Hx.
    substl; substl (length l); auto.
    unfold rep in H; destruct_lift H; omega.

    prestep; norml.
    rewrite rep_piff_indirect in Hx.
    unfold rep_indirect in Hx; destruct_lift Hx; cancel.
    step; substl.
    rewrite Nat.add_0_r, firstn_app_le by omega.
    setoid_rewrite firstn_oob at 2; try omega.
    substl (length l); substl NDirect; auto.
    unfold rep in Hx; destruct_lift Hx; omega.
  Qed.



  Lemma indrec_ptsto_pimpl : forall ibn indrec,
    IndRec.rep ibn indrec =p=> exists v, ibn |-> (v, nil).
  Proof.
    unfold IndRec.rep; cancel.
    assert (length (synced_list vl) = 1).
    unfold IndRec.items_valid in H2; intuition.
    rewrite synced_list_length; subst.
    rewrite IndRec.Defs.ipack_length.
    setoid_rewrite H1.
    rewrite Rounding.divup_mul; auto.
    apply IndRec.Defs.items_per_val_not_0.

    rewrite arrayN_isolate with (i := 0) by omega.
    unfold IndSig.RAStart; rewrite Nat.add_0_r.
    rewrite skipn_oob by omega; simpl.
    instantiate (2 := ($0, nil)).
    rewrite synced_list_selN; cancel.
  Qed.

  Hint Rewrite cuttail_length : core.
  Hint Rewrite upd_len_get_len upd_len_get_ind upd_len_get_blk upd_len_get_iattr : core.
  Hint Rewrite upd_irec_get_len upd_irec_get_ind upd_irec_get_blk upd_irec_get_iattr : core.
  Local Hint Resolve upd_len_get_iattr upd_irec_get_iattr.

  Theorem shrink_ok : forall lxp bxp ir nr ms,
    {< F Fm m0 m l freelist,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST RET:^(ms, r)  exists m' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp r (cuttail nr l) * BALLOC.rep bxp freelist') ]]] *
           [[ r = upd_len ir ((IRLen ir) - nr) ]]
    CRASH  LOG.intact lxp F m0
    >} shrink lxp bxp ir nr ms.
  Proof.
    unfold shrink.
    prestep; norml.
    assert (length l = (IRLen ir)); denote rep as Hx.
    unfold rep in Hx; destruct_lift Hx; omega.

    (* needs to free indirect block *)
    prestep; norml.
    rewrite rep_piff_indirect in Hx by omega.
    unfold rep_indirect in Hx; destruct_lift Hx.
    denote IndRec.rep as Hx; rewrite indrec_ptsto_pimpl in Hx.
    destruct_lift Hx; cancel.

    step.
    rewrite rep_piff_direct by (rewrite cuttail_length; omega).
    unfold rep_direct; cancel; autorewrite with core; try omega.
    apply le_ndirect_goodSize; omega.

    substl l at 1; unfold cuttail.
    rewrite app_length, firstn_length_l by omega.
    rewrite firstn_app_l by omega.
    f_equal; omega.

    (* no free indirect block *)
    cancel.

    (* case 1: all in direct blocks *)
    repeat rewrite rep_piff_direct by (autorewrite with core; omega).
    unfold rep_direct; cancel; autorewrite with core; try omega.
    apply le_ndirect_goodSize; omega.

    substl l at 1; unfold cuttail.
    rewrite firstn_length_l by omega.
    rewrite firstn_firstn, Nat.min_l by omega; auto.

    (* case 1: all in indirect blocks *)
    repeat rewrite rep_piff_indirect by (autorewrite with core; omega).
    unfold rep_indirect; cancel; autorewrite with core; eauto; try omega.
    apply le_nblocks_goodSize; omega.

    substl l at 1; unfold cuttail.
    rewrite app_length, firstn_length_l by omega.
    replace (length (IRBlocks ir) + (length l - NDirect) - nr) with
            (length (IRBlocks ir) + (length l - nr - NDirect)) by omega.
    rewrite firstn_app_r; f_equal.
    rewrite firstn_firstn, Nat.min_l by omega; auto.
  Qed.


  Theorem grow_ok : forall lxp bxp ir bn ms,
    {< F Fm m0 m l freelist,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ length l < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms \/
           exists m' freelist' ir',
           [[ r = Some ir' ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ir' (l ++ [bn]) * BALLOC.rep bxp freelist') ]]] *
           [[ IRAttrs ir' = IRAttrs ir /\ length (IRBlocks ir') = length (IRBlocks ir) ]]
    CRASH  LOG.intact lxp F m0
    >} grow lxp bxp ir bn ms.
  Proof.
    unfold grow.
    prestep; norml.
    assert (length l = (IRLen ir)); denote rep as Hx.
    unfold rep in Hx; destruct_lift Hx; omega.
    cancel.

    (* only update direct block *)
    prestep; norml.
    rewrite rep_piff_direct in Hx by omega.
    unfold rep_direct in Hx; cancel.
    or_r; cancel.
    rewrite rep_piff_direct by (autorewrite with lists; simpl; omega).
    unfold rep_direct; autorewrite with core lists; simpl.
    cancel; try omega.
    substl l at 1; substl (length l).
    apply firstn_app_updN_eq; omega.
    apply le_nblocks_goodSize; omega.
    autorewrite with core lists; auto.

    (* update indirect blocks *)
    step.
    step.

    (* case 1 : need allocate indirect block *)
    step; try (eapply BALLOC.bn_valid_facts; eauto).
    unfold IndSig.xparams_ok; auto.
    instantiate (vsl0 := [(v0_cur, v0_old)]); simpl; auto.
    simpl; unfold IndSig.RAStart; cancel.

    step.
    rewrite repeat_length; omega.
    step.
    or_r; cancel.
    rewrite rep_piff_direct by omega.
    rewrite rep_piff_indirect by (rewrite app_length; simpl; omega).
    unfold rep_direct, rep_indirect; cancel;
      repeat (autorewrite with core lists; simpl; eauto; try omega).
    eapply BALLOC.bn_valid_goodSize; eauto.
    apply le_nblocks_goodSize; omega.
    eapply BALLOC.bn_valid_goodSize; eauto.

    substl l at 1; substl (length l); substl (IRLen ir).
    rewrite firstn_oob, minus_plus, Nat.sub_diag by omega.
    erewrite firstn_S_selN, selN_updN_eq by (autorewrite with lists; omega).
    simpl; auto.
    autorewrite with core lists; auto.

    (* case 2 : just update the indirect block *)
    prestep; norml.
    rewrite rep_piff_indirect in Hx by omega.
    unfold rep_indirect in Hx; destruct_lift Hx; cancel; try omega.
    step.
    or_r; cancel.
    rewrite rep_piff_indirect by (rewrite app_length; simpl; omega).
    unfold rep_indirect; cancel;
      repeat (autorewrite with core lists; simpl; eauto; try omega).
    eapply BALLOC.bn_valid_goodSize; eauto.
    apply le_nblocks_goodSize; omega.
    eapply BALLOC.bn_valid_goodSize; eauto.
    substl l at 1; substl (length l).
    replace (IRLen ir + 1 - NDirect) with (IRLen ir - NDirect + 1) by omega.
    rewrite <- app_assoc; f_equal.
    rewrite firstn_app_updN_eq; auto.
    substl (length indlist); omega.
    autorewrite with core lists; auto.

    Unshelve. all:eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (shrink _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_}} progseq (grow _ _ _ _ _) _) => apply grow_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


End BlockPtr.









Module INODE.

  (************* on-disk representation of inode *)

  Definition iattrtype : Rec.type := Rec.RecF ([
    ("bytes",  Rec.WordF 64) ;       (* file size in bytes *)
    ("uid",    Rec.WordF 32) ;        (* user id *)
    ("gid",    Rec.WordF 32) ;        (* group id *)
    ("dev",    Rec.WordF 64) ;        (* device major/minor *)
    ("mtime",  Rec.WordF 32) ;        (* last modify time *)
    ("atime",  Rec.WordF 32) ;        (* last access time *)
    ("ctime",  Rec.WordF 32) ;        (* create time *)
    ("itype",  Rec.WordF  8) ;        (* type code, 0 = regular file, 1 = directory, ... *)
    ("unused", Rec.WordF 24)          (* reserved (permission bits) *)
  ]).

  Definition NDirect := 9.

  Definition irectype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);     (* number of blocks *)
    ("attrs", iattrtype);           (* file attributes *)
    ("indptr", Rec.WordF addrlen);  (* indirect block pointer *)
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) NDirect)]).


  (* RecArray for inodes records *)
  Module IRecSig <: RASig.

    Definition xparams := inode_xparams.
    Definition RAStart := IXStart.
    Definition RALen := IXLen.
    Definition xparams_ok (_ : xparams) := True.

    Definition itemtype := irectype.
    Definition items_per_val := valulen / (Rec.len itemtype).


    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; rewrite valulen_is; compute; auto.
    Qed.

  End IRecSig.

  Module IRec := LogRecArray IRecSig.
  Hint Extern 0 (okToUnify (IRec.rep _ _) (IRec.rep _ _)) => constructor : okToUnify.


  Definition iattr := Rec.data iattrtype.
  Definition irec := IRec.Defs.item.
  Definition bnlist := list waddr.

  Module BPtrSig <: BlockPtrSig.

    Definition irec     := irec.
    Definition iattr    := iattr.
    Definition NDirect  := NDirect.

    Fact NDirect_bound : NDirect <= addrlen.
      compute; omega.
    Qed.

    Definition IRLen    (x : irec) := Eval compute_rec in # ( x :-> "len").
    Definition IRIndPtr (x : irec) := Eval compute_rec in # ( x :-> "indptr").
    Definition IRBlocks (x : irec) := Eval compute_rec in ( x :-> "blocks").
    Definition IRAttrs  (x : irec) := Eval compute_rec in ( x :-> "attrs").

    Definition upd_len (x : irec) v  := Eval compute_rec in (x :=> "len" := $ v).

    Definition upd_irec (x : irec) len ibptr dbns := Eval compute_rec in
      (x :=> "len" := $ len :=> "indptr" := $ ibptr :=> "blocks" := dbns).

    (* getter/setter lemmas *)
    Fact upd_len_get_len : forall ir n,
      goodSize addrlen n -> IRLen (upd_len ir n) = n.
    Proof.
      unfold IRLen, upd_len; intros; simpl.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_len_get_ind : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_blk : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_len_get_iattr : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_len : forall ir len ibptr dbns,
      goodSize addrlen len -> IRLen (upd_irec ir len ibptr dbns) = len.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_ind : forall ir len ibptr dbns,
      goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dbns) = ibptr.
    Proof.
      intros; cbn.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Fact upd_irec_get_blk : forall ir len ibptr dbns, 
      IRBlocks (upd_irec ir len ibptr dbns) = dbns.
    Proof. intros; simpl; auto. Qed.

    Fact upd_irec_get_iattr : forall ir len ibptr dbns, 
      IRAttrs (upd_irec ir len ibptr dbns) = IRAttrs ir.
    Proof. intros; simpl; auto. Qed.

  End BPtrSig.

  Module Ind := BlockPtr BPtrSig.

  Definition NBlocks := NDirect + Ind.IndSig.items_per_val.


  (************* program *)


  Definition getlen T lxp xp inum ms rx : prog T := Eval compute_rec in
    let^ (ms, (ir : irec)) <- IRec.get_array lxp xp inum ms;
    rx ^(ms, # (ir :-> "len" )).

  Definition getattrs T lxp xp inum ms rx : prog T := Eval compute_rec in
    let^ (ms, (i : irec)) <- IRec.get_array lxp xp inum ms;
    rx ^(ms, (i :-> "attrs")).

  Definition setattrs T lxp xp inum attr ms rx : prog T := Eval compute_rec in
    let^ (ms, (i : irec)) <- IRec.get_array lxp xp inum ms;
    ms <- IRec.put_array lxp xp inum (i :=> "attrs" := attr) ms;
    rx ms.

  (* For updattr : a convenient way for setting individule attribute *)

  Inductive iattrupd_arg :=
  | IABytes (v : word 64)
  | IAMTime (v : word 32)
  | IAType  (v : word  8)
  .

  Definition iattr_upd (e : iattr) (a : iattrupd_arg) := Eval compute_rec in
  match a with
  | IABytes v => (e :=> "bytes" := v)
  | IAMTime v => (e :=> "mtime" := v)
  | IAType  v => (e :=> "itype" := v)
  end.

  Definition updattr T lxp xp inum a ms rx : prog T := Eval compute_rec in
    let^ (ms, (i : irec)) <- IRec.get_array lxp xp inum ms;
    ms <- IRec.put_array lxp xp inum (i :=> "attrs" := (iattr_upd (i :-> "attrs") a)) ms;
    rx ms.


  Definition getbnum T lxp xp inum off ms rx : prog T :=
    let^ (ms, (ir : irec)) <- IRec.get_array lxp xp inum ms;
    ms <- Ind.get lxp ir off ms;
    rx ms.

  Definition getallbnum T lxp xp inum ms rx : prog T :=
    let^ (ms, (ir : irec)) <- IRec.get_array lxp xp inum ms;
    ms <- Ind.read lxp ir ms;
    rx ms.

  Definition shrink T lxp bxp xp inum nr ms rx : prog T :=
    let^ (ms, (ir : irec)) <- IRec.get_array lxp xp inum ms;
    let^ (ms, ir') <- Ind.shrink lxp bxp ir nr ms;
    ms <- IRec.put_array lxp xp inum ir' ms;
    rx ms.

  Definition grow T lxp bxp xp inum bn ms rx : prog T :=
    let^ (ms, (ir : irec)) <- IRec.get_array lxp xp inum ms;
    let^ (ms, r) <- Ind.grow lxp bxp ir ($ bn) ms;
    match r with
    | None => rx ^(ms, false)
    | Some ir' =>
        ms <- IRec.put_array lxp xp inum ir' ms;
        rx ^(ms, true)
    end.


  (************** rep invariant *)

  Record inode := mk_inode {
    IBlocks : bnlist;
    IAttr   : iattr
  }.

  Definition iattr0 := @Rec.of_word iattrtype $0.
  Definition inode0 := mk_inode nil iattr0.
  Definition irec0 := IRec.Defs.item0.


  Definition inode_match bxp ino (ir : irec) := Eval compute_rec in
    ( [[ IAttr ino = (ir :-> "attrs") ]] *
      Ind.rep bxp ir (IBlocks ino) )%pred.

  Definition rep bxp xp (ilist : list inode) := (
     exists reclist, IRec.rep xp reclist *
     listmatch (inode_match bxp) ilist reclist)%pred.


  (************** Basic lemmas *)

  Lemma irec_well_formed : forall Fm xp l i inum m,
    (Fm * IRec.rep xp l)%pred m
    -> i = selN l inum irec0
    -> Rec.well_formed i.
  Proof.
    intros; subst.
    eapply IRec.item_wellforemd; eauto.
  Qed.

  Lemma direct_blocks_length: forall (i : irec),
    Rec.well_formed i
    -> length (i :-> "blocks") = NDirect.
  Proof.
    intros; simpl in H.
    destruct i; repeat destruct p.
    repeat destruct d0; repeat destruct p; intuition.
  Qed.

  Lemma irec_blocks_length: forall m xp l inum Fm,
    (Fm * IRec.rep xp l)%pred m ->
    length (selN l inum irec0 :-> "blocks") = NDirect.
  Proof.
    intros.
    apply direct_blocks_length.
    eapply irec_well_formed; eauto.
  Qed.

  Lemma irec_blocks_length': forall m xp l inum Fm d d0 d1 d2 u,
    (Fm * IRec.rep xp l)%pred m ->
    (d, (d0, (d1, (d2, u)))) = selN l inum irec0 ->
    length d2 = NDirect.
  Proof.
    intros.
    eapply IRec.item_wellforemd with (i := inum) in H.
    setoid_rewrite <- H0 in H.
    unfold Rec.well_formed in H; simpl in H; intuition.
  Qed.


  (**************  Automation *)


  (* Hints for resolving default values *)

  Fact resolve_selN_irec0 : forall l i d,
    d = irec0 -> selN l i d = selN l i irec0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_addr0 : forall l i (d : waddr),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_valu0 : forall l i (d : valu),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Rewrite resolve_selN_irec0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.
  Hint Rewrite resolve_selN_addr0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_valu0   using reflexivity : defaults.

  Ltac filldef :=
    repeat match goal with
    | [ H : context [ selN _ _ ?d ] |- _ ] =>
        is_evar d; autorewrite with defaults in H
    end; autorewrite with defaults.

  Ltac rewrite_ignore H :=
    match type of H with
    | forall _, corr2 _ _ => idtac
    | norm_goal _ => idtac
    end.

  Ltac simplen_rewrite_hyp H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints lists)) in H); subst_evars;
      [ try simplen_rewrite_hyp H | try autorewrite with lists .. ]
    ).

  Ltac simplen_rewrite := repeat match goal with
    | [H : @eqlen _ ?T ?a ?b |- context [length ?a] ] => setoid_replace (length a) with (length b) by auto
    | [H : context[length ?x] |- _] =>
           progress ( first [ is_var x | rewrite_ignore H | simplen_rewrite_hyp H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => first [ rewrite_ignore H2 | rewrite H in H2 ]
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : @eqlen _ ?T ?l nil |- context [?l] ] => replace l with (@nil T) by eauto
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac genseplen_rewrite := repeat match goal with
    | [H : ( _ * ?a |-> ?v)%pred (list2nmem ?l) |- _ ] =>
            apply list2nmem_inbound in H
    | [H : context [ listmatch ?a ?b ] |- _ ] =>
            match goal with
            | [ H' : length ?a = length ?b |- _ ] => idtac
            | [ H' : length ?b = length ?a |- _ ] => idtac
            | _ => setoid_rewrite listmatch_length_pimpl in H; destruct_lift H
            end
  end.

  Ltac simplen' := unfold eqlen in *; eauto;
    repeat (try subst; simpl; auto;
      genseplen_rewrite; simplen_rewrite;
      autorewrite with defaults core lists);
    simpl; eauto; try omega.


  Ltac extract_listmatch_at H ix :=
    match type of H with
    | context [ listmatch ?prd ?a ?b ] =>
      erewrite listmatch_extract with (i := ix) in H by simplen';
      try autorewrite with defaults in H; auto;
      match prd with
      | ?n _ => try unfold n at 2 in H
      | ?n   => try unfold n at 2 in H
      end; destruct_lift H
    end.

  Ltac extract_listmatch :=
    match goal with
      | [  H : context [ listmatch ?prd ?a _ ],
          H2 : ?p%pred (list2nmem ?a) |- _ ] =>
        match p with
          | context [ ( ?ix |-> _)%pred ] =>
              extract_listmatch_at H ix
        end
    end.


  Tactic Notation "extract" :=
    extract_listmatch.

  Tactic Notation "extract" "at" ident(ix) :=
    match goal with
      | [  H : context [ listmatch _ _ _ ] |- _ ] => extract_listmatch_at H ix
    end.


  Ltac rewrite_list2nmem_pred_bound H :=
    let Hi := fresh in
    eapply list2nmem_inbound in H as Hi.

  Ltac rewrite_list2nmem_pred_sel H :=
    let Hx := fresh in
    eapply list2nmem_sel in H as Hx;
    try autorewrite with defaults in Hx.

  Ltac rewrite_list2nmem_pred_upd H:=
    let Hx := fresh in
    eapply list2nmem_array_updN in H as Hx.

  Ltac rewrite_list2nmem_pred :=
    match goal with
    | [ H : (?prd * ?ix |-> ?v)%pred (list2nmem ?l) |- _ ] =>
      rewrite_list2nmem_pred_bound H;
      first [
        is_var v; rewrite_list2nmem_pred_sel H; subst v |
        match prd with
        | arrayN_ex ?ol ix =>
          is_var l; rewrite_list2nmem_pred_upd H;
          [ subst l | simplen'; clear H .. ]
        end ]
    end.

  Ltac seprewrite :=
    repeat rewrite_list2nmem_pred.

  Ltac resolve_list2nmem_sel :=
    match goal with
    | [ |- (?prd * ?ix |-> ?v)%pred (list2nmem ?l) ] =>
        eapply list2nmem_ptsto_cancel ; simplen'
    end.

  Ltac resolve_list2nmem_upd :=
    match goal with
    | [ |- (?prd * ?ix |-> ?v)%pred (list2nmem ?l) ] =>
        eapply list2nmem_updN; eauto
    end.

  Ltac gensep_auto' :=
    subst; first [
        resolve_list2nmem_sel
      | resolve_list2nmem_upd
      | try extract; subst; filldef;
        try rewrite_list2nmem_pred; eauto; simplen';
        try apply list2nmem_ptsto_cancel; simplen';
        autorewrite with defaults; eauto
    ].

  Ltac sepauto :=
    try solve [ gensep_auto' ].

  Ltac simplen :=
    let tac :=
      solve [ match goal with
      | [ |- _ > _ ] =>   simplen'
      | [ |- _ >= _ ] =>  simplen'
      | [ |- _ < _ ] =>   simplen'
      | [ |- _ <= _ ] =>  simplen'
      | [ |- _ = _ ] =>   simplen'
      end ] in
    try solve [ filldef;
    first [ tac
          | seprewrite; subst; tac
          | extract; seprewrite; subst; tac
          ] ].

  Ltac destruct_irec' x :=
    match type of x with
    | irec => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | iattr => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | prod _ _ => let b := fresh in destruct x as [? b] eqn:? ; destruct_irec' b
    | _ => idtac
    end.

  Ltac destruct_irec x :=
    match x with
    | (?a, ?b) => (destruct_irec a || destruct_irec b)
    | fst ?a => destruct_irec a
    | snd ?a => destruct_irec a
    | _ => destruct_irec' x; simpl
    end.

  Ltac smash_rec_well_formed' :=
    match goal with
    | [ |- Rec.well_formed ?x ] => destruct_irec x
    end.

  Ltac smash_rec_well_formed :=
    subst; autorewrite with defaults;
    repeat smash_rec_well_formed';
    unfold Rec.well_formed; simpl;
    try rewrite Forall_forall; intuition.


  Ltac irec_wf :=
    smash_rec_well_formed;
    match goal with
      | [ H : ?p %pred ?mm |- length ?d = NDirect ] =>
      match p with
        | context [ IRec.rep ?xp ?ll ] => 
          eapply irec_blocks_length' with (m := mm) (l := ll) (xp := xp); eauto;
          pred_apply; cancel
      end
    end.

  Arguments Rec.well_formed : simpl never.



  (********************** SPECs *)

  Theorem getlen_ok : forall lxp bxp xp inum ms,
    {< F Fm Fi m0 m ilist ino,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp xp ilist) ]]] *
           [[[ ilist ::: Fi * inum |-> ino ]]]
    POST RET:^(ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = length (IBlocks ino) ]]
    CRASH  LOG.intact lxp F m0
    >} getlen lxp xp inum ms.
  Proof.
    unfold getlen, rep; pose proof irec0.
    hoare.

    sepauto.
    extract. 
    denote Ind.rep as Hx; unfold Ind.rep in Hx; destruct_lift Hx.
    seprewrite; subst; eauto.
  Qed.


  Theorem getattrs_ok : forall lxp bxp xp inum ms,
    {< F Fm Fi m0 m ilist ino,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp xp ilist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:^(ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = IAttr ino ]]
    CRASH  LOG.intact lxp F m0
    >} getattrs lxp xp inum ms.
  Proof.
    unfold getattrs, rep.
    hoare.

    sepauto.
    extract.
    seprewrite; subst; eauto.
  Qed.


  Theorem setattrs_ok : forall lxp bxp xp inum attr ms,
    {< F Fm Fi m0 m ilist ino,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp xp ilist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:ms exists m' ilist' ino',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp xp ilist') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (IBlocks ino) attr ]]
    CRASH  LOG.intact lxp F m0
    >} setattrs lxp xp inum attr ms.
  Proof.
    unfold setattrs, rep.
    hoare.

    sepauto.
    irec_wf.

    sepauto.
    eapply listmatch_updN_selN; simplen.
    instantiate (1 := mk_inode (IBlocks ino) attr).
    unfold inode_match; cancel; sepauto.
    sepauto.
    Unshelve. exact irec0.
  Qed.


  Theorem updattr_ok : forall lxp bxp xp inum kv ms,
    {< F Fm Fi m0 m ilist ino,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp xp ilist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:ms exists m' ilist' ino',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp xp ilist') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (IBlocks ino) (iattr_upd (IAttr ino) kv) ]]
    CRASH  LOG.intact lxp F m0
    >} updattr lxp xp inum kv ms.
  Proof.
    unfold updattr, rep.
    hoare.

    sepauto.
    filldef; abstract (destruct kv; simpl; subst; irec_wf).
    sepauto.
    eapply listmatch_updN_selN; simplen.
    instantiate (1 := mk_inode (IBlocks ino) (iattr_upd (IAttr ino) kv)).
    unfold inode_match; cancel; sepauto.
    sepauto.
    Unshelve. exact irec0.
  Qed.


  Theorem getbnum_ok : forall lxp bxp xp inum off ms,
    {< F Fm Fi m0 m ilist ino,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ off < length (IBlocks ino) ]] *
           [[[ m ::: (Fm * rep bxp xp ilist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = selN (IBlocks ino) off $0 ]]
    CRASH  LOG.intact lxp F m0
    >} getbnum lxp xp inum off ms.
  Proof.
    unfold getbnum, rep.
    step.
    sepauto.

    prestep; norml.
    extract; seprewrite.
    cancel.
  Qed.


  Theorem getallbnum_ok : forall lxp bxp xp inum ms,
    {< F Fm Fi m0 m ilist ino,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp xp ilist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = (IBlocks ino) ]]
    CRASH  LOG.intact lxp F m0
    >} getallbnum lxp xp inum ms.
  Proof.
    unfold getallbnum, rep.
    step.
    sepauto.

    prestep; norml.
    extract; seprewrite.
    cancel.
  Qed.


  Theorem shrink_ok : forall lxp bxp xp inum nr ms,
    {< F Fm Fi m0 m ilist ino freelist,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp xp ilist * BALLOC.rep bxp freelist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:ms exists m' ilist' ino' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp xp ilist' * BALLOC.rep bxp freelist') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode (cuttail nr (IBlocks ino)) (IAttr ino) ]]
    CRASH  LOG.intact lxp F m0
    >} shrink lxp bxp xp inum nr ms.
  Proof.
    unfold shrink, rep.
    step.
    sepauto.

    extract; seprewrite.
    step.
    step.
    subst; unfold BPtrSig.upd_len, BPtrSig.IRLen.
    irec_wf.
    sepauto.

    step.
    2: sepauto.
    rewrite listmatch_updN_removeN by omega.
    cancel.
    unfold inode_match, BPtrSig.upd_len, BPtrSig.IRLen; simpl.
    cancel.
    Unshelve. eauto.
  Qed.


  Lemma grow_wellformed : forall (a : BPtrSig.irec) inum reclist F1 F2 F3 F4 m xp,
    ((((F1 * IRec.rep xp reclist) * F2) * F3) * F4)%pred m ->
    length (BPtrSig.IRBlocks a) = length (BPtrSig.IRBlocks (selN reclist inum irec0)) ->
    inum < length reclist ->
    Rec.well_formed a.
  Proof.
    unfold IRec.rep, IRec.items_valid; intros.
    destruct_lift H.
    denote Forall as Hx.
    apply Forall_selN with (i := inum) (def := irec0) in Hx; auto.
    apply direct_blocks_length in Hx.
    setoid_rewrite <- H0 in Hx.
    cbv in Hx; cbv in a.
    cbv.
    destruct a; repeat destruct p. destruct p0; destruct p.
    intuition.
  Qed.

  Theorem grow_ok : forall lxp bxp xp inum bn ms,
    {< F Fm Fi m0 m ilist ino freelist,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ length (IBlocks ino) < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp xp ilist * BALLOC.rep bxp freelist) ]]] *
           [[[ ilist ::: (Fi * inum |-> ino) ]]]
    POST RET:^(ms, r)
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms \/
           [[ r = true ]] * exists m' ilist' ino' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp xp ilist' * BALLOC.rep bxp freelist') ]]] *
           [[[ ilist' ::: (Fi * inum |-> ino') ]]] *
           [[ ino' = mk_inode ((IBlocks ino) ++ [$ bn]) (IAttr ino) ]]
    CRASH  LOG.intact lxp F m0
    >} grow lxp bxp xp inum bn ms.
  Proof.
    unfold grow, rep.
    step.
    sepauto.

    extract; seprewrite.
    step.
    step.
    eapply grow_wellformed; eauto.
    sepauto.

    step.
    or_r; cancel.
    2: sepauto.
    rewrite listmatch_updN_removeN by omega.
    cancel.
    unfold inode_match, BPtrSig.IRAttrs in *; simpl.
    cancel.
    substl (IAttr (selN ilist inum inode0)); eauto.
    Unshelve. all: eauto; exact emp.
  Qed.

  Hint Extern 1 ({{_}} progseq (getlen _ _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} progseq (getattrs _ _ _ _) _) => apply getattrs_ok : prog.
  Hint Extern 1 ({{_}} progseq (setattrs _ _ _ _ _) _) => apply setattrs_ok : prog.
  Hint Extern 1 ({{_}} progseq (updattr _ _ _ _ _) _) => apply updattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (grow _ _ _ _ _ _) _) => apply grow_ok : prog.
  Hint Extern 1 ({{_}} progseq (shrink _ _ _ _ _ _) _) => apply shrink_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


End INODE.

