Require Import Arith.
Require Import Pred PredCrash.
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
  Parameter xparams_ok : xparams -> Prop.

End AllocSig.


Module BmapAlloc (Sig : AllocSig).

  Import Sig.

  Module BmpSig <: RASig.

    Definition xparams := xparams.
    Definition RAStart := BMPStart.
    Definition RALen := BMPLen.
    Definition xparams_ok := xparams_ok.

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
  Definition state_dec := bit_dec.

  Definition Avail (s : state) : Prop := s = $0.
  Definition InUse (s : state) : Prop := s = $1.

  Definition is_avail (s : state) := if (state_dec s) then true else false.
  Definition avail_nonzero s i := if (addr_eq_dec i 0) then false else is_avail s.

  Definition free lxp xp bn ms :=
    ms <- Bmp.put lxp xp bn $0 ms;
    Ret ms.

  Definition ifind_avail_nonzero lxp xp ms :=
    Bmp.ifind lxp xp avail_nonzero ms.

  Definition alloc lxp xp ms :=
    let^ (ms, r) <- ifind_avail_nonzero lxp xp ms;
    match r with
    | None =>
        Ret ^(ms, None)
    | Some (bn, _) =>
        ms <- Bmp.put lxp xp bn $1 ms;
        Ret ^(ms, Some bn)
    end.

  Definition steal lxp xp bn ms :=
    ms <- Bmp.put lxp xp bn $1 ms;
    Ret ms.

  Definition init lxp xp ms :=
    ms <- Bmp.init lxp xp ms;
    Ret ms.

  (* init with no free objects *)
  Definition init_nofree lxp xp ms :=
    ms <- Bmp.init lxp xp ms;
    ms <- Bmp.write lxp xp (repeat $1 ((BMPLen xp) * valulen)) ms;
    Ret ms.

  Definition freelist_bmap_equiv freelist bmap :=
    forall a, a < length bmap -> (In a freelist <-> Avail (selN bmap a $0)).

  Definition rep V FP xp (freelist : list addr) (freepred : @pred _ addr_eq_dec V) :=
    (exists bmap, Bmp.rep xp bmap *
     [[ freelist_bmap_equiv freelist bmap ]] *
     [[ freepred <=p=> listpred (fun a => exists v, a |-> v * [[ FP v ]]) freelist ]] )%pred.


  Lemma freelist_bmap_equiv_remove_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
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
    contradict H2.
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

  Lemma avail_nonzero_is_avail : forall bmap i,
    avail_nonzero (selN bmap i $0) i = true ->
    is_avail (selN bmap i $0) = true.
  Proof.
    unfold avail_nonzero; intros.
    destruct (addr_eq_dec i 0); congruence.
  Qed.

  Lemma avail_nonzero_not_zero : forall bmap i,
    avail_nonzero (selN bmap i $0) i = true -> i <> 0.
  Proof.
    unfold avail_nonzero; intros.
    destruct (addr_eq_dec i 0); congruence.
  Qed.

  Local Hint Resolve avail_nonzero_is_avail avail_nonzero_not_zero.

  Lemma freelist_bmap_equiv_init_ok : forall xp,
    freelist_bmap_equiv (seq 0 (BMPLen xp * valulen))
      (repeat Bmp.Defs.item0 (BmpSig.RALen xp * BmpSig.items_per_val)).
  Proof.
    unfold freelist_bmap_equiv; split; intros.
    - rewrite repeat_length in H.
      rewrite repeat_selN; auto.
      cbv; auto.
    - rewrite repeat_length in H.
      apply in_seq; intuition.
  Qed.


  Hint Extern 0 (okToUnify (listpred ?prd _ ) (listpred ?prd _)) => constructor : okToUnify.

  Theorem init_ok : forall V FP lxp xp ms,
    {< F Fm m0 m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:hm' RET:ms exists m' freelist freepred,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ forall bn, bn < (BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep; intros.
    step.
    step.
    apply freelist_bmap_equiv_init_ok.
    apply in_seq; intuition.
    apply arrayN_listpred_seq_fp; auto.
  Qed.

  Theorem init_nofree_ok : forall V FP lxp xp ms,
    {< F Fm m0 m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init_nofree lxp xp ms.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
    unfold Bmp.items_valid; intuition.
    rewrite repeat_length; auto.
    step.
    unfold freelist_bmap_equiv; split; intros.
    denote (In _ nil) as Hx; inversion Hx.
    denote (Avail _) as Hx; unfold Avail in Hx.
    rewrite repeat_selN in Hx; inversion Hx.
    rewrite repeat_length in *; auto.
    Unshelve.
    all: try exact $0; try exact tt.
  Qed.


  Theorem steal_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ In bn freelist /\ bn < (BMPLen xp) * valulen ]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep; intros.
    step.
    eapply bmap_rep_length_ok2; eauto.

    prestep. norm. cancel.
    intuition simpl.
    pred_apply; cancel.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    eapply bmap_rep_length_ok2; eauto.
    apply piff_refl.
    denote freepred as Hp; rewrite Hp, listpred_remove.
    eassign bn; cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.
    auto.
    eauto.
  Qed.

  Theorem alloc_ok : forall V FP lxp xp ms,
    {< F Fm m0 m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:hm' RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, ifind_avail_nonzero, rep.
    step.
    step.
    step.

    or_r; cancel.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    apply piff_refl.
    denote freepred as Hp; rewrite Hp, listpred_remove.
    eassign a_1; cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.
    eapply is_avail_in_freelist; eauto.
    eapply avail_nonzero_not_zero; eauto.
    eapply bmap_rep_length_ok1; eauto.
    eapply is_avail_in_freelist; eauto.
  Qed.


  Theorem free_ok : forall V FP lxp xp bn ms,
    {< F Fm m0 m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ bn < (BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred') ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep.
    hoare.

    eapply bmap_rep_length_ok2; eauto.
    apply freelist_bmap_equiv_add_ok; auto.
    eapply bmap_rep_length_ok2; eauto.
    denote (freepred <=p=> _) as Hfp. apply Hfp.
    Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.


  Lemma xform_rep : forall V FP xp l p,
    crash_xform (@rep V FP xp l p) <=p=> @rep V FP xp l p.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Bmp.xform_rep; cancel.
  Qed.

  Lemma xform_rep_rawpred : forall xp FP l p,
    (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p) =p=> rep FP xp l p * [[ crash_xform p =p=> p ]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    rewrite H2.
    rewrite xform_listpred_ptsto_fp; auto.
  Qed.


End BmapAlloc.

(* BmapAlloc with a list of free items to speed up allocation *)

(*

Module BmapAllocCache.

   Module Sig <: AllocSig.
    Definition xparams := balloc_xparams.
    Definition BMPStart := BmapStart.
    Definition BMPLen := BmapNBlocks.

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 bytes of disk space *)
    Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := list addr.

  Record memstate := mk_memstate {
    MSLog  : LOG.memstate;
    MSCache   : BmapCacheType; 
  }.

  Definition freelist0 : BmapCacheType := (@nil addr).

  Definition init lxp xp fms : prog memstate :=
    fms <- Alloc.init lxp xp fms;
    Ret (mk_memstate fms freelist0 ).

  Definition init_nofree lxp xp ms :=
    fms <- Alloc.init_nofree lxp xp ms;
    Ret (mk_memstate fms freelist0).


  Definition alloc lxp xp ms :=
    match (MSCache ms) with
    | nil =>
      let^ (fms, r) <- Alloc.alloc lxp xp (MSLog ms);
      Ret ^((mk_memstate fms (MSCache ms)), r)
    | bn :: freelist =>
      fms <- Alloc.steal lxp xp bn (MSLog ms);
      Ret ^((mk_memstate fms freelist), Some bn)
    end.

  Definition free lxp xp bn ms :=
    fms <- Alloc.free lxp xp bn (MSLog ms) ;
    Ret (mk_memstate fms (bn ::(MSCache ms))).

  Definition steal lxp xp bn (ms:memstate) :=
    fms <- Alloc.steal lxp xp bn (MSLog ms) ;
    Ret (mk_memstate fms freelist0).

Import ListUtils.

  Definition rep V xp freelist (freepred : @pred _ addr_eq_dec V) cache :=
    (Alloc.rep xp freelist freepred *
    [[incl_count addr_eq_dec cache freelist ]])%pred.

(*
    [[forall bn, In bn cache -> 
      bn <> 0 /\ 
      bn < (Sig.BMPLen xp) * valulen /\ 
      In bn freelist ]])%pred. *)

  Theorem init_ok : forall V lxp xp (ms:memstate),
    {< F Fm m0 m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:hm' RET:ms exists m' freepred freelist,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) hm' *
          [[[ m' ::: (Fm * @rep V xp freelist freepred (MSCache ms)) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init lxp xp (MSLog ms).
  Proof.
    unfold init, rep; intros.
    step.
    step.
  Qed.

  Theorem alloc_ok : forall V lxp xp (ms:memstate),
    {< F Fm m0 m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) hm *
          [[[ m ::: (Fm * @rep V xp freelist freepred (MSCache ms)) ]]]
    POST:hm' RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) hm' *
          [[[ m' ::: (Fm * @rep V xp (remove addr_eq_dec bn freelist) freepred' (MSCache ms)) ]]] *
          [[ freepred =p=> freepred' * bn |->? ]] *
          [[ bn <> 0 /\ bn < (Sig.BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, rep; intros.
    destruct_branch.
    step.
    step.
    step.


    Search In incl_count.

    specialize (H8 n).
    intuition.
    specialize (H8 n).
    intuition.
    step.
    or_r.
    cancel. 
    eapply NoDup_cons_iff; eauto.
    specialize (H8 bn). subst.
    destruct H8. right. auto.
    congruence.
    specialize (H8 bn).
    intuition.
    specialize (H8 bn).
    intuition.
    destruct (addr_eq_dec n bn).
    intros.  subst.
    destruct H6. eauto.
    exfalso. inversion H9. subst.
    congruence.
    intros. subst.
    Search remove.
    apply remove_other_In; eauto.
    specialize (H8 n). subst; destruct H8.
    left. auto. congruence.
    specialize (H8 n).
    intuition.
    specialize (H8 n).
    intuition.
  Qed.

  Theorem free_ok : forall V lxp xp bn ms,
    {< F Fm m0 m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) hm *
          [[ bn < (Sig.BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V xp freelist freepred (MSCache ms)) ]]]
    POST:hm' RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) hm' *
          [[[ m' ::: (Fm * @rep V xp (bn :: freelist) freepred' (MSCache ms)) ]]] *
          [[ bn |->? * freepred =p=> freepred' ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep; intros.
    step.
    step.
    specialize (H9 bn).
    destruct (In_dec addr_eq_dec bn (MSCache ms)).
    destruct H9. eauto.
    intuition.
    exfalso. admit. (* H and H0? *)
    constructor; auto.
    specialize (H9 bn).
    subst.
    destruct (In_dec addr_eq_dec 0 (MSCache ms)).
    destruct H9. eauto. congruence.
    admit.
    subst.
    admit.
    specialize (H9 bn0).
    destruct H9. intuition. intuition.
    specialize (H9 bn0).  destruct H9. auto. intuition.
  Admitted.

  Theorem steal_ok : forall V lxp xp bn (ms:memstate),
    {< F Fm m0 m freelist freepred,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) hm *
          [[[ m ::: (Fm * @rep V xp freelist freepred (MSCache ms))]]] *
          [[ In bn freelist /\ bn < (Sig.BMPLen xp) * valulen ]]
    POST:hm' RET:ms' exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms') hm' *
          [[[ m' ::: (Fm * @rep V xp (remove addr_eq_dec bn freelist) freepred' (MSCache ms)) ]]] *
          [[ freepred =p=> freepred' * bn |->? ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep; intros.
    step.
    step.
  Qed.


End BmapAllocCache.
*)


(* Specialize for actual on-disk-block allocation *)

Module BALLOC.

  Module Sig <: AllocSig.
    Definition xparams := balloc_xparams.
    Definition BMPStart := BmapStart.
    Definition BMPLen := BmapNBlocks.

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 bytes of disk space *)
    Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;
    Ret r.

  Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;
    Ret r.

  Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;
    Ret r.

  Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;
    Ret r.

  Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;
    Ret r.

  Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Definition FP (x : valuset) := True.

  Definition rep xp (freeblocks : list addr) :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred)%pred.


  Theorem init_ok : forall lxp xp ms,
    {< F Fm m0 m bl dl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:hm' RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * rep xp freeblocks) ]]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep; intros.
    step.
    step.
  Qed.

  Theorem init_nofree_ok : forall lxp xp ms,
    {< F Fm m0 m bl,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * rep xp nil) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} init_nofree lxp xp ms.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
  Qed.

  Theorem steal_ok : forall lxp xp bn ms,
    {< F Fm m0 m freeblocks,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: (Fm * rep xp freeblocks) ]]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
          [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep, bn_valid.
    step.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    denote pimpl as Hx; rewrite Hx.
    cancel; cancel.
    eauto.
    Unshelve . all: try exact addr_eq_dec; auto.
  Qed.


  Theorem alloc_ok : forall lxp xp ms,
    {< F Fm m0 m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep xp freeblocks) ]]]
    POST:hm' RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
           [[ In bn freeblocks ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, rep, bn_valid.
    hoare.
    match goal with
    | [ H1 : (_ =p=> ?F * _)%pred, H2 : context [ ?F ] |- _ ] => rewrite H1 in H2
    end.
    or_r; cancel.
  Qed.

  Theorem free_ok : forall lxp xp bn ms,
    {< F Fm m0 m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks * bn |->?) ]]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks)) ]]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep, bn_valid.
    hoare.
    rewrite H12; unfold FP; eauto.
  Qed.


  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.


  Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).
  Proof.
    intros; cancel.
  Qed.


  Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm crash m0 freeblocks ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks)) *
                       listpred (fun a => a |->?) (skipn i l) ]]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.


  Theorem freevec_ok : forall lxp xp l ms,
    {< F Fm m0 m freeblocks,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks * listpred (fun a => a |->?) l ) ]]]
    POST:hm' RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks)) ]]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} freevec lxp xp l ms.
  Proof.
    unfold freevec.
    step.

    prestep; norml.
    denote listpred as Hx.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx by (rewrite skipn_length; omega).
    rewrite skipn_selN, Nat.add_0_r in Hx.

    (*** extract the exis from |->? *)
    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eauto.

    step.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.

    step.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    step.
    erewrite <- LOG.intact_hashmap_subset; eauto.
    Unshelve. all: eauto; exact tt.
  Qed.

  Hint Extern 1 ({{_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.


  Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.
  Proof.
    unfold Sig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.

  Lemma bn_valid_goodSize : forall F l m xp a,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.
  Proof.
    unfold rep, bn_valid.
    unfold Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Lemma bn_valid_goodSize_pimpl : forall l xp,
    rep xp l <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply bn_valid_goodSize; eauto.
    cancel.
  Qed.

  Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
  Proof.
    unfold bn_valid; auto.
  Qed.

  Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Theorem bn_valid_roundtrip : forall xp a F l m,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold rep, Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply bn_valid_roundtrip'; auto.
  Qed.

  Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.
  Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.

  Definition items_per_val := Alloc.BmpSig.items_per_val.


  Theorem xform_rep : forall xp l,
    crash_xform (rep xp l) =p=> rep xp l.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Alloc.xform_rep_rawpred.
    cancel.
    auto.
    unfold FP; intros.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.

End BALLOC.



(* Specialize for inode allocation *)

Module IAlloc.

  Module Sig <: AllocSig.
    Definition xparams     := fs_xparams.
    Definition BMPStart xp := BmapStart (FSXPInodeAlloc xp).
    Definition BMPLen   xp := BmapNBlocks (FSXPInodeAlloc xp).

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 inodes *)
    Definition xparams_ok xp := (BMPLen xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition init := Alloc.init.

  Definition alloc := Alloc.alloc.

  Definition free := Alloc.free.

  Definition rep := Alloc.rep.

  Definition ino_valid xp ino := ino < (Sig.BMPLen xp) * valulen.

  Definition init_ok := Alloc.init_ok.

  Definition alloc_ok := Alloc.alloc_ok.

  Definition free_ok := Alloc.free_ok.

  Definition items_per_val := Alloc.BmpSig.items_per_val.

  Hint Extern 1 ({{_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.

  Definition xform_rep := Alloc.xform_rep.

  Lemma xparams_ok_goodSize : forall xp ino,
    Sig.xparams_ok xp ->
    ino_valid xp ino ->
    goodSize addrlen ino.
  Proof.
    unfold Sig.xparams_ok, ino_valid; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.

  Lemma ino_valid_goodSize : forall V FP F l m xp a prd,
    (F * @rep V FP xp l prd)%pred m ->
    ino_valid xp a ->
    goodSize addrlen a.
  Proof.
    unfold rep, ino_valid.
    unfold Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Lemma ino_valid_goodSize_pimpl : forall V FP l xp p,
    @rep V FP xp l p <=p=> [[ forall a, ino_valid xp a -> goodSize addrlen a ]] * rep FP xp l p.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply ino_valid_goodSize; eauto.
    cancel.
  Qed.

  Theorem ino_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold ino_valid; intuition.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Theorem ino_valid_roundtrip : forall V FP xp a F l m p,
    (F * @rep V FP xp l p)%pred m ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold rep, Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply ino_valid_roundtrip'; auto.
  Qed.

End IAlloc.
