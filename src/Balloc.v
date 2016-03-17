Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Nomega.
Require Import Idempotent.
Require Import Psatz.
Require Import Rec.
Require Import NArith.
Require Import Log.
Require Import RecArrayUtils.
Require Import LogRecArray.
Require Import ListPred.
Require Import GenSepN.
Require Import WordAuto.
Require Import FSLayout.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.


(* Bitmap allocator *)

Module Type AllocSig.

  Parameter xparams : Type.
  Parameter BMPStart : xparams -> addr.
  Parameter BMPLen   : xparams -> addr.

End AllocSig.


Module BmapAlloc (Sig : AllocSig).

  Import Sig.

  Module BmpSig <: RASig.

    Definition xparams := xparams.
    Definition RAStart := BMPStart.
    Definition RALen := BMPLen.

    Definition itemtype := Rec.WordF 1.
    Definition items_per_val := valulen.

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; simpl.
      rewrite Nat.mul_1_r; auto.
    Qed.

  End BmpSig.

  Module Bmp := LogRecArray BmpSig.
  Module Defs := Bmp.Defs.

  Definition state := Defs.item.

  Definition state_dec : forall (a : state), {a = $0} + {a = $1}.
    intro.
    rewrite (shatter_word a).
    replace (wtl a) with WO by auto.
    destruct (whd a).
    right; apply eq_refl.
    left; apply eq_refl.
  Defined.

  Definition Avail (s : state) : Prop := s = $0.
  Definition InUse (s : state) : Prop := s = $1.

  Definition is_avail (s : state) := if (state_dec s) then true else false.
  Definition is_inuse (s : state) := if (state_dec s) then false else true.

  Definition free T lxp xp bn ms rx : prog T :=
    ms <- Bmp.put lxp xp bn $0 ms;
    rx ms.

  Definition alloc T lxp xp ms rx : prog T :=
    let^ (ms, r) <- Bmp.ifind lxp xp is_avail ms;
    match r with
    | None =>
        rx ^(ms, None)
    | Some (bn, _) =>
        ms <- Bmp.put lxp xp bn $1 ms;
        rx ^(ms, Some bn)
    end.

  Definition freelist_bmap_equiv freelist bmap :=
    forall a, a < length bmap -> (In a freelist <-> Avail (selN bmap a $0)).

  Definition rep V xp (freelist : list addr) (freepred : @pred _ addr_eq_dec V) :=
    (exists bmap, Bmp.rep xp bmap *
     [[ freelist_bmap_equiv freelist bmap ]] *
     [[ freepred = listpred (fun a => a |->?) freelist ]] )%pred.


  Lemma freelist_bmap_equiv_remove_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    is_avail (selN bmap a $0) = true ->
    a < length bmap ->
    freelist_bmap_equiv (remove addr_eq_dec a freelist) (updN bmap a $1).
  Proof.
    unfold freelist_bmap_equiv; split; intros.
    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    exfalso; eapply remove_In; eauto.
    rewrite selN_updN_ne by auto.
    apply H.
    erewrite <- length_updN; eauto.
    eapply remove_still_In; eauto.

    destruct (addr_eq_dec a a0); subst.
    contradict H3.
    rewrite selN_updN_eq by auto.
    discriminate.
    apply remove_other_In; auto.
    apply H.
    erewrite <- length_updN; eauto.
    erewrite <- selN_updN_ne; eauto.
  Qed.

  Lemma freelist_bmap_equiv_add_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (a :: freelist) (updN bmap a $0).
  Proof.
    unfold freelist_bmap_equiv; split; intros.
    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    unfold Avail; auto.
    rewrite selN_updN_ne by auto.
    apply H.
    erewrite <- length_updN; eauto.
    simpl in H2; destruct H2; auto; congruence.

    destruct (addr_eq_dec a a0); subst; simpl; auto.
    right; apply H.
    erewrite <- length_updN; eauto.
    erewrite <- selN_updN_ne; eauto.
  Qed.

  Lemma is_avail_in_freelist : forall a bmap freelist,
    freelist_bmap_equiv freelist bmap ->
    is_avail (selN bmap a $0) = true ->
    a < length bmap ->
    In a freelist.
  Proof.
    unfold freelist_bmap_equiv, is_avail, Avail.
    intros; apply H; auto.
    destruct (state_dec (selN bmap a $0)); auto; congruence.
  Qed.


  Lemma bmap_rep_length_ok1 : forall F xp bmap d a,
    a < length bmap ->
    (F * Bmp.rep xp bmap)%pred d ->
    a < BMPLen xp * valulen.
  Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H0.
    eapply lt_le_trans; eauto.
    rewrite H6; auto.
  Qed.

  Lemma bmap_rep_length_ok2 : forall F xp bmap d a,
    (F * Bmp.rep xp bmap)%pred d ->
    a < BMPLen xp * valulen ->
    a < length bmap.
  Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H.
    eapply lt_le_trans; eauto.
    rewrite H6; auto.
  Qed.


  Hint Extern 0 (okToUnify (listpred ?prd _ ) (listpred ?prd _)) => constructor : okToUnify.

  Theorem alloc_ok : forall V lxp xp ms,
    {< F Fm m0 m freelist freepred,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[[ m ::: (Fm * @rep V xp freelist freepred) ]]]
    POST RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms
       \/ exists bn m' freelist' freepred', 
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
          [[[ m' ::: (Fm * @rep V xp freelist' freepred') ]]] *
          [[ freepred =p=> freepred' * bn |->? ]] *
          [[ bn < (BMPLen xp) * valulen ]]
    CRASH LOG.intact lxp F m0
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, rep.
    hoare.

    or_r; cancel.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    rewrite listpred_remove; try cancel.
    intros; apply ptsto_conflict.
    eapply is_avail_in_freelist; eauto.
    eapply bmap_rep_length_ok1; eauto.
  Qed.


  Theorem free_ok : forall V lxp xp bn ms,
    {< F Fm m0 m freelist freepred,
    PRE   LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
          [[ bn < (BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V xp freelist freepred) ]]]
    POST RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
          [[[ m' ::: (Fm * @rep V xp (bn :: freelist) freepred') ]]] *
          [[ bn |->? * freepred =p=> freepred' ]]
    CRASH LOG.intact lxp F m0
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep.
    hoare.

    eapply bmap_rep_length_ok2; eauto.
    apply freelist_bmap_equiv_add_ok; auto.
    eapply bmap_rep_length_ok2; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} progseq (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


  (*
  (* Different names for actual on-disk-block allocation *)
  Definition alloc := alloc_gen.
  Definition free := free_gen.

  Definition rep xp (freeblocks : list addr) :=
    (exists genpred genpredn, genpred * rep_gen xp freeblocks genpred genpredn)%pred.

  Theorem alloc_ok : forall lxp xp mscs,
    {< F Fm mbase m freeblocks,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs * [[ (Fm * rep xp freeblocks)%pred (list2mem m) ]]
    POST RET:^(mscs,r)
                   [[ r = None ]] * LOG.rep lxp F (ActiveTxn mbase m) mscs \/
                   exists bn m' freeblocks', [[ r = Some bn ]] *
                   LOG.rep lxp F (ActiveTxn mbase m') mscs *
                   [[ (Fm * bn |->? * rep xp freeblocks')%pred (list2mem m') ]] *
                   [[ valid_block xp bn ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} alloc lxp xp mscs.
  Proof.
    unfold alloc, rep.
    intros.
    eapply pimpl_ok2. apply alloc_gen_ok.
    cancel.
    step.
    rewrite H10 in H7.
    apply pimpl_or_r. right.
    cancel.
  Qed.

  Theorem free_ok : forall lxp xp bn mscs,
    {< F Fm mbase m freeblocks,
    PRE        LOG.rep lxp F (ActiveTxn mbase m) mscs *
               [[ (Fm * rep xp freeblocks * bn |->?)%pred (list2mem m) ]] *
               [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST RET:mscs
               exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
               [[ (Fm * rep xp (bn :: freeblocks))%pred (list2mem m') ]]
    CRASH      LOG.would_recover_old lxp F mbase
    >} free lxp xp bn mscs.
  Proof.
    unfold free, rep.
    intros.
    eapply pimpl_ok2. apply free_gen_ok.
    cancel.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (BALLOC.alloc _ _ _) _) => apply BALLOC.alloc_ok : prog.
  Hint Extern 1 ({{_}} progseq (BALLOC.free _ _ _ _) _) => apply BALLOC.free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.
  *)

End BmapAlloc.
