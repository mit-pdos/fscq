Require Import Hashmap.
Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Classes.SetoidTactics.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import BasicProg.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import Eqdep_dec.
Require Import WordAuto.
Require Import Cache.
Require Import Idempotent.
Require Import ListUtils.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MemLog.
Require Import MapUtils.
Require Import ListPred.
Require Import LogReplay.
Require Import GroupLog.
Require Import DiskSet.
Require Import RelationClasses.
Require Import Morphisms.


Import ListNotations.

Set Implicit Arguments.

Parameter should_flushall : bool.

Module LOG.

  Import AddrMap LogReplay.

  Record mstate := mk_mstate {
    MSTxn   : valumap;         (* memory state for active txns *)
    MSGLog  : GLog.mstate    (* lower-level state *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate mm (ll : GLog.memstate) : memstate := 
    (mk_mstate mm (fst ll), (snd ll)).
  Definition mk_memstate0 (cs: cachestate) := (mk_mstate vmap0 GLog.mk_memstate0, cs).

  Definition MSCache (ms : memstate) := snd ms.
  Definition MSLL (ms : memstate) : GLog.memstate := (MSGLog (fst ms), (snd ms)).

  Definition readOnly (ms ms' : memstate) :=
    (GLog.readOnly (MSLL ms) (MSLL ms') /\
     Map.Empty (MSTxn (fst ms)) /\
     Map.Empty (MSTxn (fst ms'))).


  Inductive state :=
  | NoTxn (cur : diskset)
  (* No active transaction, MemLog.Synced or MemLog.Applying *)

  | ActiveTxn (old : diskset) (cur : diskstate)
  (* A transaction is in progress.
   * It started from the first memory and has evolved into the second.
   *)

  | FlushingTxn (new : diskset)
  (* A flushing is in progress
   *)

  | RollbackTxn (old : diskstate)
  | RecoveringTxn (old : diskstate)
  .

  Definition rep_inner xp st ms hm :=
  let '(cm, mm) := (MSTxn ms, MSGLog ms) in
  (match st with
    | NoTxn ds =>
      [[ Map.Empty cm ]] *
      GLog.rep xp (GLog.Cached ds) mm hm
    | ActiveTxn ds cur =>
      [[ map_valid cm ds!! ]] *
      [[ map_replay cm ds!! cur ]] *
      GLog.rep xp (GLog.Cached ds) mm hm
    | FlushingTxn ds =>
      GLog.would_recover_any xp ds hm
    | RollbackTxn d =>
      [[ Map.Empty cm ]] *
      GLog.rep xp (GLog.Rollback d) mm hm
    | RecoveringTxn d =>
      [[ Map.Empty cm ]] *
      GLog.rep xp (GLog.Recovering d) mm hm
  end)%pred.

  Definition rep xp F st ms hm :=
    (exists raw, BUFCACHE.rep (snd ms) raw *
      [[ (F * rep_inner xp st (fst ms) hm)%pred raw ]])%pred.

  Definition intact xp F ds hm :=
    (exists ms,
      rep xp F (NoTxn ds) ms hm \/
      exists new, rep xp F (ActiveTxn ds new) ms hm)%pred.

  Definition recover_any xp F ds hm :=
    (exists ms, rep xp F (FlushingTxn ds) ms hm)%pred.

  Theorem sync_invariant_rep : forall xp F st ms hm,
    sync_invariant F ->
    sync_invariant (rep xp F st ms hm).
  Proof.
    unfold rep; destruct st; intros; eauto.
  Qed.
  Hint Resolve sync_invariant_rep.

  Theorem sync_invariant_intact : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (intact xp F ds hm).
  Proof.
    unfold intact; auto.
  Qed.

  Theorem sync_invariant_recover_any : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (recover_any xp F ds hm).
  Proof.
    unfold recover_any; auto.
  Qed.
  Hint Resolve sync_invariant_intact sync_invariant_recover_any.

  Lemma active_intact : forall xp F old new ms hm,
    rep xp F (ActiveTxn old new) ms hm =p=> intact xp F old hm.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma notxn_intact : forall xp F old ms hm,
    rep xp F (NoTxn old) ms hm =p=> intact xp F old hm.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma flushing_any : forall xp F ds ms hm,
    rep xp F (FlushingTxn ds) ms hm =p=> recover_any xp F ds hm.
  Proof.
    unfold recover_any; cancel.
  Qed.

  Lemma intact_any : forall xp F ds hm,
    intact xp F ds hm =p=> recover_any xp F ds hm.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    apply GLog.cached_recover_any.
    Unshelve. all: eauto.
  Qed.

  Lemma notxn_any : forall xp F ds ms hm,
    rep xp F (NoTxn ds) ms hm =p=> recover_any xp F ds hm.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    Unshelve. all: eauto.
  Qed.

  Lemma active_notxn : forall xp F old new ms hm,
    rep xp F (ActiveTxn old new) ms hm =p=>
    rep xp F (NoTxn old) (mk_mstate vmap0 (MSGLog (fst ms)), (snd ms)) hm.
  Proof.
    unfold rep, rep_inner; cancel.
  Qed.

  Lemma intact_dsupd_latest : forall xp F ds a v hm gms,
    GLog.dset_match xp (GLog.effective ds (length gms)) gms ->
    intact xp F (dsupd (ds!!, nil) a v) hm =p=>
    recover_any xp F (dsupd ds a v) hm.
  Proof.
    unfold dsupd at 1, d_map at 1; simpl; intros.
    rewrite <- dsupd_latest.
    unfold intact, rep, rep_inner.
    unfold recover_any, rep, rep_inner; cancel.
    rewrite GLog.cached_dsupd_latest_recover_any; eauto.
    rewrite GLog.cached_dsupd_latest_recover_any; eauto.
    Unshelve. all: eauto.
  Qed.

  Lemma intact_dssync_vecs_latest : forall xp F ds al hm gms,
    GLog.dset_match xp (GLog.effective ds (length gms)) gms ->
    intact xp F (dssync_vecs (ds!!, nil) al) hm =p=>
    recover_any xp F (dssync_vecs ds al) hm.
  Proof.
    unfold dssync_vecs at 1, d_map at 1; simpl; intros.
    rewrite <- dssync_vecs_latest.
    unfold intact, rep, rep_inner.
    unfold recover_any, rep, rep_inner; cancel.
    rewrite GLog.cached_dssync_vecs_latest_recover_any; eauto.
    rewrite GLog.cached_dssync_vecs_latest_recover_any; eauto.
    Unshelve. all: eauto.
  Qed.

  Lemma active_dset_match_pimpl : forall xp F ds d hm ms,
    rep xp F (ActiveTxn ds d) ms hm <=p=>
    rep xp F (ActiveTxn ds d) ms hm * 
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) gms ]].
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.

  Lemma notxn_dset_match_pimpl : forall xp F ds hm ms,
    rep xp F (NoTxn ds) ms hm <=p=>
    rep xp F (NoTxn ds) ms hm * 
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) gms ]].
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.

  Lemma rep_inner_hashmap_subset : forall xp ms hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep_inner xp st ms hm
        =p=> rep_inner xp st ms hm'.
  Proof.
    intros.
    destruct st; unfold rep_inner, GLog.would_recover_any.
    all: try erewrite GLog.rep_hashmap_subset; eauto.
    cancel.
    erewrite GLog.rep_hashmap_subset; eauto.
    auto.
  Qed.

  Lemma rep_hashmap_subset : forall xp F ms hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp F st ms hm
        =p=> rep xp F st ms hm'.
  Proof.
    unfold rep; intros; cancel.
    erewrite rep_inner_hashmap_subset; eauto.
  Qed.

  Lemma intact_hashmap_subset : forall xp F ds hm hm',
    (exists l, hashmap_subset l hm hm')
    -> intact xp F ds hm
        =p=> intact xp F ds hm'.
  Proof.
    unfold intact; intros; cancel;
    erewrite rep_hashmap_subset; eauto.
    all: cancel.
  Qed.

  Lemma rep_inner_notxn_pimpl : forall xp d ms hm,
    rep_inner xp (NoTxn (d, nil)) ms hm
    =p=> exists ms', rep_inner xp (RecoveringTxn d) ms' hm.
  Proof.
    unfold rep_inner; intros.
    rewrite GLog.cached_recovering.
    norm'l. cancel.
    eassign (mk_mstate vmap0 ms'); auto.
    apply map_empty_vmap0.
  Qed.

  Lemma rep_inner_rollbacktxn_pimpl : forall xp d ms hm,
    rep_inner xp (RollbackTxn d) ms hm
    =p=> rep_inner xp (RecoveringTxn d) ms hm.
  Proof.
    unfold rep_inner; intros.
    rewrite GLog.rollback_recovering.
    cancel.
  Qed.

  Lemma readOnlyMapEmpty : forall ms,
    (exists ms0, readOnly ms0 ms) -> Map.Empty (MSTxn (fst ms)).
  Proof.
    unfold readOnly; intros; deex; intuition.
  Qed.

  Hint Resolve readOnlyMapEmpty.

  Theorem readOnlyLL : forall ms ms',
    GLog.readOnly (MSLL ms) (MSLL ms') ->
    Map.Empty (MSTxn (fst ms)) ->
    Map.Empty (MSTxn (fst ms')) ->
    readOnly ms ms'.
  Proof.
    firstorder.
  Qed.

  Hint Resolve readOnlyLL.

  Theorem readOnlyLL' : forall ms mstxn' msll',
    GLog.readOnly (MSLL ms) msll' ->
    Map.Empty (MSTxn (fst ms)) ->
    MSTxn (fst ms) = mstxn' ->
    readOnly ms (mk_memstate mstxn' msll').
  Proof.
    intros; substl; eauto.
  Qed.

  Hint Resolve readOnlyLL'.

  Theorem readOnly_refl : forall ms,
    Map.Empty (MSTxn (fst ms)) ->
    readOnly ms ms.
  Proof.
    intuition.
  Qed.

  Hint Resolve readOnly_refl.

  Theorem readOnly_trans : forall ms ms' ms'',
    readOnly ms ms' -> readOnly ms' ms'' -> readOnly ms ms''.
  Proof.
    unfold readOnly.
    intuition congruence.
  Qed.

  Hint Resolve readOnly_trans.


  Definition init xp cs :=
    mm <- GLog.init xp cs;
    Ret (mk_memstate vmap0 mm).

  Definition begin (xp : log_xparams) (ms : memstate) :=
    Ret ms.

  Definition abort (xp : log_xparams) ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate vmap0 mm).

  Definition write (xp : log_xparams) a v ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate (Map.add a v cm) mm).

  Definition read xp a ms :=
    t1 <- Rdtsc;
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    match Map.find a cm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- GLog.read xp a mm;
             let ms' := mk_memstate cm mm' in
             t2 <- Rdtsc;
               Debug "LOG.read" (t2-t1);;
        Ret ^(ms', v)
    end.

  Definition commit xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let^ (mm', r) <- GLog.submit xp (Map.elements cm) mm;
    If (bool_dec should_flushall true) {
      mm' <- GLog.flushall_noop xp mm';
      Ret ^(mk_memstate vmap0 mm', r)
    } else {
      Ret ^(mk_memstate vmap0 mm', r)
    }.

  (* like abort, but use a better name for read-only transactions *)
  Definition commit_ro (xp : log_xparams) ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate vmap0 mm).

  Definition dwrite (xp : log_xparams) a v ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let cm' := Map.remove a cm in
    mm' <- GLog.dwrite xp a v mm;
    Ret (mk_memstate cm' mm').

  Definition dsync xp a ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync xp a mm;
    Ret (mk_memstate cm mm').

  Definition flushsync xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushsync xp mm;
    Ret (mk_memstate cm mm').

  Definition flushall xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall xp mm;
    Ret (mk_memstate cm mm').

  Definition flushsync_noop xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushsync_noop xp mm;
    Ret (mk_memstate cm mm').

  Definition flushall_noop xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall_noop xp mm;
    Ret (mk_memstate cm mm').

  Definition sync_cache xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.sync_cache xp mm;
    Ret (mk_memstate cm mm').

  Definition recover xp cs :=
    mm <- GLog.recover xp cs;
    Ret (mk_memstate vmap0 mm).


  Local Hint Unfold rep rep_inner map_replay: hoare_unfold.
  Arguments GLog.rep: simpl never.
  Hint Extern 0 (okToUnify (GLog.rep _ _ _ _) (GLog.rep _ _ _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; repeat match goal with
  | [ H : eq _ (mk_memstate _ _) |- _ ] =>
     inversion H; subst; simpl; clear H
  | [ |- Map.Empty vmap0 ] => apply Map.empty_1
  | [ |- map_valid vmap0 _ ] => apply map_valid_map0
  | [ H : Map.Empty ?m |- map_valid ?m _ ] => apply map_valid_empty
  end; eauto.

  Local Hint Resolve KNoDup_map_elements.
  Local Hint Resolve MapProperties.eqke_equiv.

  Definition init_ok : forall xp cs,
    {< F l d m,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DiskLogHash.PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: ms exists d,
          rep xp F (NoTxn (d, nil)) ms hm' *
          [[[ d ::: arrayN (@ptsto _ _ _) 0 d ]]] *
          [[ length d = (LogHeader xp) - (DataStart xp) ]]
    XCRASH:hm_crash any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    step.
    apply list2nmem_array.
  Qed.


  Theorem begin_ok: forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm
    POST:hm' RET:r
      rep xp F (ActiveTxn ds ds!!) r hm' *
      [[ readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' hm'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
    rewrite replay_disk_empty; auto.
  Qed.


  Theorem abort_ok : forall xp ms,
    {< F ds m,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' hm'
    >} abort xp ms.
  Proof.
    unfold abort.
    safestep.
    step using dems; subst; simpl.
    pred_apply; cancel.
    eapply readOnlyLL; eauto; try reflexivity; simpl; dems.
    pimpl_crash; norm. cancel.
    eassign (mk_mstate vmap0 (MSGLog ms_1)).
    intuition; pred_apply; cancel.
  Qed.


  Theorem read_ok: forall xp ms a,
    {< F Fm ds m v,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: Fm * a |-> v ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' hm' * [[ r = fst v ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' hm'
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.
    cancel.
    step.

    eapply replay_disk_eq; eauto.
    eassign ds!!; pred_apply; cancel.
    pimpl_crash; cancel.

    cancel.
    2: step.
    eexists; subst.
    eapply ptsto_replay_disk_not_in; eauto.
    apply MapFacts.not_find_in_iff; eauto.

    pimpl_crash; norm. cancel.
    eassign (mk_mstate (MSTxn ms_1) ms'_1).
    intuition; pred_apply; cancel.
  Qed.


  Theorem write_ok : forall xp ms a v,
    {< F Fm ds m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm * [[ a <> 0 ]] *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' hm' *
      [[[ m' ::: (Fm * a |-> (v, nil)) ]]]
    CRASH:hm'
      exists m' ms', rep xp F (ActiveTxn ds m') ms' hm'
    >} write xp a v ms.
  Proof.
    unfold write.
    hoare using dems.
    pred_apply; cancel.

    apply map_valid_add; eauto.
    erewrite <- replay_disk_length.
    eapply list2nmem_ptsto_bound; eauto.

    rewrite replay_disk_add.
    eapply list2nmem_updN; eauto.
  Qed.


  Set Regular Subst Tactic.

  Theorem dwrite_ok : forall xp ms a v,
    {< F Fm ds vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds',
      rep xp F (ActiveTxn ds' ds'!!) ms' hm' *
      [[[ ds'!! ::: (Fm * a |-> (v, vsmerge vs)) ]]] *
      [[ ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:hm'
      recover_any xp F ds hm' \/
      recover_any xp F (dsupd ds a (v, vsmerge vs)) hm'
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite, recover_any.
    step.
    step; subst.

    eapply map_valid_remove; autorewrite with lists; eauto.
    rewrite dsupd_latest_length; auto.
    rewrite dsupd_latest.
    apply updN_replay_disk_remove_eq; eauto.
    rewrite dsupd_latest.
    eapply list2nmem_updN; eauto.

    (* crash conditions *)
    xcrash.
    or_l; cancel; xform_normr; cancel.

    or_r; cancel.
    xform_normr; cancel.

    Unshelve. all: eauto.
  Qed.


  Theorem dsync_ok : forall xp ms a,
    {< F Fm ds vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds',
      rep xp F (ActiveTxn ds' ds'!!) ms' hm' *
      [[ ds' = dssync ds a ]]
    CRASH:hm'
      recover_any xp F ds hm'
    >} dsync xp a ms.
  Proof.
    unfold dsync, recover_any.
    step.
    step; subst.
    rewrite dssync_latest; unfold vssync; apply map_valid_updN; auto.
    rewrite dssync_latest; substl (ds!!) at 1.
    apply replay_disk_vssync_comm.
    Unshelve. eauto.
  Qed.


  Theorem flushall_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushall xp ms.
  Proof.
    unfold flushall, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.


  Theorem flushsync_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushsync xp ms.
  Proof.
    unfold flushsync, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.

  Theorem flushall_noop_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn ds) ms' hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushall_noop xp ms.
  Proof.
    unfold flushall_noop, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.

  Theorem flushsync_noop_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn ds) ms' hm'
    XCRASH:hm'
      recover_any xp F ds hm'
    >} flushsync_noop xp ms.
  Proof.
    unfold flushsync_noop, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (flushall_noop _ _) _) => apply flushall_noop_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushsync_noop _ _) _) => apply flushsync_noop_ok : prog.

  Local Hint Resolve map_valid_log_valid length_elements_cardinal_gt map_empty_vmap0.

  Theorem commit_ok : forall xp ms,
    {< F ds m,
     PRE:hm  rep xp F (ActiveTxn ds m) ms hm *
            [[ sync_invariant F ]]
     POST:hm' RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn (pushd m ds)) ms' hm') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn (fst ms)) > (LogLen xp) ]] *
            rep xp F (NoTxn ds) ms' hm')
     XCRASH:hm' recover_any xp F (pushd m ds) hm'
    >} commit xp ms.
  Proof.
    unfold commit, recover_any.
    step.
    step.
    step.
    step.

    xcrash.
    unfold GLog.would_recover_any.
    cancel.
    constructor; auto.

    step.
    step.
    step.
    xcrash.
    step.
    xcrash.
    rewrite GLog.cached_recover_any.
    unfold GLog.would_recover_any.
    cancel.
    constructor; auto.
    Unshelve. all: eauto.
  Qed.


  (* a pseudo-commit for read-only transactions *)
  Theorem commit_ro_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' hm'
    >} commit_ro xp ms.
  Proof.
    intros.
    eapply pimpl_ok2.
    apply abort_ok.
    safecancel.
    apply sep_star_comm.
    auto.
    step.
    cancel.
  Qed.


  Definition after_crash xp F ds cs hm :=
    (exists raw, BUFCACHE.rep cs raw *
     [[ ( exists d n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (NoTxn (d, nil)) ms hm \/
            rep_inner xp (RollbackTxn d) ms hm) *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.

  Definition before_crash xp F ds hm :=
    (exists cs raw, BUFCACHE.rep cs raw *
     [[ ( exists d n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (RecoveringTxn d) ms hm) *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.

  Theorem sync_invariant_after_crash : forall xp F ds cs hm,
    sync_invariant F ->
    sync_invariant (after_crash xp F ds cs hm).
  Proof.
    unfold after_crash; eauto.
  Qed.

  Theorem sync_invariant_before_crash : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (before_crash xp F ds hm).
  Proof.
    unfold before_crash; eauto.
  Qed.

  Hint Resolve sync_invariant_after_crash sync_invariant_before_crash.

  Theorem recover_ok: forall xp cs,
    {< F ds,
    PRE:hm
      after_crash xp F ds cs hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' 
      exists d n, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms' hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    XCRASH:hm'
      before_crash xp F ds hm'
    >} recover xp cs.
  Proof.
    unfold recover, after_crash, before_crash, rep, rep_inner.
    safestep.
    unfold GLog.recover_any_pred. norm.
    eassign F; cancel.
    or_l; cancel.
    intuition simpl; eauto.
    unfold GLog.recover_any_pred. norm.
    cancel.
    or_r; cancel.
    intuition simpl; eauto.
    eauto.

    prestep. norm. cancel.
    intuition simpl; eauto.
    pred_apply; cancel.

    norm'l.
    repeat xcrash_rewrite.
    xform_norm; cancel.
    xform_norm; cancel.
    xform_norm.
    norm.
    cancel.
    intuition simpl; eauto.
    pred_apply.
    norm.
    cancel.
    eassign (mk_mstate vmap0 x1); eauto.
    intuition simpl; eauto.
  Qed.


  Lemma crash_xform_before_crash : forall xp F ds hm,
    crash_xform (before_crash xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
  Proof.
    unfold before_crash, after_crash, rep_inner; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    norm.
    cancel.
    intuition.
    pred_apply.
    xform_norm.
    rewrite GLog.crash_xform_recovering.
    unfold GLog.recover_any_pred.
    norm. unfold stars; simpl.
    cancel.
    unfold GLog.recover_any_pred; cancel.
    or_l; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    auto.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.

    unfold stars; simpl.
    cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    auto.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.


  Lemma crash_xform_any : forall xp F ds hm,
    crash_xform (recover_any xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
  Proof.
    unfold recover_any, after_crash, rep, rep_inner; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    xform_norm.
    norm. cancel.
    intuition simpl; pred_apply; xform_norm.
    rewrite GLog.crash_xform_any.
    unfold GLog.recover_any_pred.
    norm. cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    intuition simpl; eauto.

    or_l; cancel.
    intuition simpl; eauto.
    cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    eauto.
    intuition simpl; eauto.
  Qed.


  Lemma after_crash_notxn : forall xp cs F ds hm,
    after_crash xp F ds cs hm =p=>
      exists d n ms, [[ n <= length (snd ds) ]] *
      (rep xp F (NoTxn (d, nil)) ms hm \/
        rep xp F (RollbackTxn d) ms hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
  Proof.
    unfold after_crash, recover_any, rep, rep_inner.
    intros. norm. cancel.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor; destruct_lift H.
    or_l; cancel.
    or_r; cancel.
    intuition simpl. eassumption.
    auto.
  Qed.


  Lemma after_crash_notxn_singular : forall xp cs F d hm,
    after_crash xp F (d, nil) cs hm =p=>
      exists d' ms, (rep xp F (NoTxn (d', nil)) ms hm \/
                      rep xp F (RollbackTxn d') ms hm) *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    intros; rewrite after_crash_notxn; cancel.
  Qed.


  Lemma after_crash_idem : forall xp F ds cs hm,
    crash_xform (after_crash xp F ds cs hm) =p=>
     exists cs', after_crash xp (crash_xform F) ds cs' hm.
  Proof.
    unfold after_crash, rep_inner; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    xform_norm.
    denote crash_xform as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite crash_xform_or_dist in Hx.
    apply sep_star_or_distr in Hx.
    norm. unfold stars; simpl. cancel.
    intuition simpl; eauto.

    destruct Hx as [Hx | Hx];
    autorewrite with crash_xform in Hx;
    destruct_lift Hx; pred_apply.

    rewrite GLog.crash_xform_cached.
    norm. cancel.
    or_l; cancel.
    eassign (mk_mstate vmap0 ms'); cancel.
    auto.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite GLog.crash_xform_rollback.
    norm. cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms'); cancel.
    auto.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.

  Lemma after_crash_idem' : forall xp d ms hm (F : rawpred),
    F (list2nmem d) ->
    crash_xform (rep_inner xp (NoTxn (d, nil)) ms hm
              \/ rep_inner xp (RollbackTxn d) ms hm) =p=>
    exists d' ms',(rep_inner xp (NoTxn (d', nil)) ms' hm \/
                   rep_inner xp (RollbackTxn d') ms' hm) *
                   [[ (crash_xform F) (list2nmem d') ]].
  Proof.
    unfold rep_inner; intros.
    xform_norml.
    rewrite GLog.crash_xform_cached; cancel.
    eassign (mk_mstate vmap0 ms').
    or_l; cancel.
    eapply crash_xform_diskIs_pred; eauto.

    rewrite GLog.crash_xform_rollback; cancel.
    eassign (mk_mstate vmap0 ms').
    or_r; cancel.
    eapply crash_xform_diskIs_pred; eauto.
  Qed.

  Hint Extern 0 (okToUnify (LOG.rep_inner  _ _ _) (LOG.rep_inner _ _ _ _)) => constructor : okToUnify.

  (* TODO: Would be better to rewrite using hashmap_subset. *)
  Instance rep_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> pimpl) rep.
  Proof.
    unfold Proper, respectful; intros.
    unfold rep; cancel.
    apply H0.
  Qed.

  Instance intact_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> pimpl) intact.
  Proof.
    unfold Proper, respectful; intros.
    unfold intact; cancel; or_l.
    rewrite H0; eauto.
    rewrite active_notxn.
    rewrite H0; eauto.
  Qed.

  Instance after_crash_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> pimpl) after_crash.
  Proof.
    unfold Proper, respectful; intros.
    unfold after_crash.
    subst. norm. cancel. intuition simpl.
    pred_apply. norm.

    cancel.
    rewrite sep_star_or_distr.
    or_l; cancel.
    rewrite H0; eauto.
    intuition simpl; eauto.

    cancel.
    rewrite sep_star_or_distr.
    or_r; cancel.
    rewrite H0; eauto.
    intuition simpl; eauto.
  Qed.

  Lemma notxn_after_crash_diskIs : forall xp F n ds d ms hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (NoTxn (d, nil)) ms hm =p=> after_crash xp F ds (snd ms) hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    or_l; cancel.
    eauto.
    auto.
  Qed.

  Lemma rollbacktxn_after_crash_diskIs : forall xp F n d ds ms hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (RollbackTxn d) ms hm =p=> after_crash xp F ds (snd ms) hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    or_r; cancel.
    eauto.
    auto.
  Qed.

  (** idempred includes both before-crash cand after-crash cases *)
  Definition idempred xp F ds hm :=
    (recover_any xp F ds hm \/
      before_crash xp F ds hm \/
      exists cs, after_crash xp F ds cs hm)%pred.

  Theorem sync_invariant_idempred : forall xp F ds hm,
    sync_invariant F ->
    sync_invariant (idempred xp F ds hm).
  Proof.
    unfold idempred; auto.
  Qed.
  Hint Resolve sync_invariant_idempred.

  Theorem idempred_idem : forall xp F ds hm,
    crash_xform (idempred xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
  Proof.
    unfold idempred; intros.
    xform_norm.
    rewrite crash_xform_any; cancel.
    rewrite crash_xform_before_crash; cancel.
    rewrite after_crash_idem; cancel.
  Qed.

  Theorem recover_any_idempred : forall xp F ds hm,
    recover_any xp F ds hm =p=> idempred xp F ds hm.
  Proof.
    unfold idempred; cancel.
  Qed.

  Theorem intact_idempred : forall xp F ds hm,
    intact xp F ds hm =p=> idempred xp F ds hm.
  Proof.
    intros.
    rewrite intact_any.
    apply recover_any_idempred.
  Qed.

  Theorem notxn_idempred : forall xp F ds ms hm,
    rep xp F (NoTxn ds) ms hm =p=> idempred xp F ds hm.
  Proof.
    intros.
    rewrite notxn_intact.
    apply intact_idempred.
  Qed.

  Theorem active_idempred : forall xp F ds ms d hm,
    rep xp F (ActiveTxn ds d) ms hm =p=> idempred xp F ds hm.
  Proof.
    intros.
    rewrite active_intact.
    apply intact_idempred.
  Qed.

  Theorem after_crash_idempred : forall xp F ds cs hm,
    after_crash xp F ds cs hm =p=> idempred xp F ds hm.
  Proof.
    unfold idempred; intros.
    or_r; cancel.
  Qed.

  Theorem before_crash_idempred : forall xp F ds hm,
    before_crash xp F ds hm =p=> idempred xp F ds hm.
  Proof.
    unfold idempred; intros.
    or_r; or_l; cancel.
  Qed.

  Instance idempred_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> pimpl) idempred.
  Proof.
    unfold Proper, respectful; intros.
    unfold idempred; cancel.
    unfold recover_any, rep. or_l; cancel.
    rewrite H0; cancel.

    unfold before_crash, rep.
    or_r; or_l.
    norm. cancel.
    intuition. pred_apply.
    norm. cancel.
    rewrite H0; cancel.
    intuition simpl; eauto.

    unfold after_crash, rep.
    or_r; or_r.
    norm. cancel.
    intuition. pred_apply.
    norm. cancel.
    rewrite sep_star_or_distr.
    or_l; cancel.
    rewrite H0; cancel.
    intuition simpl; eauto.

    norm; auto. cancel.
    rewrite sep_star_or_distr.
    or_r; cancel.
    rewrite H0; cancel.
    intuition simpl; eauto.
  Qed.

  Theorem crash_xform_intact : forall xp F ds hm,
    crash_xform (intact xp F ds hm) =p=>
      exists ms d n, rep xp (crash_xform F) (NoTxn (d, nil)) ms hm *
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
        [[ n <= length (snd ds) ]].
  Proof.
    unfold intact, rep, rep_inner; intros.
    xform_norm;
    rewrite BUFCACHE.crash_xform_rep_pred by eauto;
    xform_norm;
    denote crash_xform as Hx;
    apply crash_xform_sep_star_dist in Hx;
    rewrite GLog.crash_xform_cached in Hx;
    destruct_lift Hx.

    safecancel.
    eassign (mk_mstate (MSTxn x_1) dummy1).
    cancel. auto.
    eauto.
    eauto.

    safecancel.
    eassign (mk_mstate vmap0 dummy1).
    cancel. auto. eauto. auto.
  Qed.

  Theorem crash_xform_idempred : forall xp F ds hm,
    crash_xform (idempred xp F ds hm) =p=>
      exists ms d n,
        (rep xp (crash_xform F) (NoTxn (d, nil)) ms hm \/
          rep xp (crash_xform F) (RollbackTxn d) ms hm) *
        [[ n <= length (snd ds) ]] *
        [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
  Proof.
    unfold idempred, recover_any, after_crash, before_crash, rep, rep_inner; intros.
    xform_norm;
    rewrite BUFCACHE.crash_xform_rep_pred by eauto;
    xform_norm;
    denote crash_xform as Hx.

    - apply crash_xform_sep_star_dist in Hx;
      rewrite GLog.crash_xform_any in Hx;
      unfold GLog.recover_any_pred in Hx;
      destruct_lift Hx.

      denote or as Hor.
      apply sep_star_or_distr in Hor.
      destruct Hor.

      safecancel.
      or_l; cancel.
      eassign (mk_mstate (Map.empty valu) dummy1).
      cancel. auto. eassumption. auto.

      safecancel.
      or_r; cancel.
      eassign (mk_mstate (Map.empty valu) dummy1).
      cancel. auto. eassumption. auto.

    - apply crash_xform_sep_star_dist in Hx;
      rewrite GLog.crash_xform_recovering in Hx;
      unfold GLog.recover_any_pred in Hx;
      destruct_lift Hx.

      denote or as Hor.
      apply sep_star_or_distr in Hor.
      destruct Hor.

      safecancel.
      or_l; cancel.
      eassign (mk_mstate (Map.empty valu) dummy4).
      cancel. auto. eassumption.
      eapply crash_xform_diskIs_trans; eauto.

      safecancel.
      or_r; cancel.
      eassign (mk_mstate (Map.empty valu) dummy4).
      cancel. auto. eassumption.
      eapply crash_xform_diskIs_trans; eauto.

    - apply crash_xform_sep_star_dist in Hx.
      rewrite crash_xform_or_dist in Hx.
      apply sep_star_or_distr in Hx;
      destruct Hx; autorewrite with crash_xform in H0.

      rewrite GLog.crash_xform_cached in H0.
      destruct_lift H0.
      safecancel.
      or_l; cancel.
      eassign (mk_mstate (Map.empty valu) dummy4).
      cancel. auto. eassumption.
      eapply crash_xform_diskIs_trans; eauto.

      rewrite GLog.crash_xform_rollback in H0.
      destruct_lift H0.
      safecancel.
      or_r; cancel.
      eassign (mk_mstate (Map.empty valu) dummy3).
      cancel. auto. eassumption.
      eapply crash_xform_diskIs_trans; eauto.
  Qed.


  Hint Resolve active_intact flushing_any.
  Hint Extern 0 (okToUnify (intact _ _ _ _) (intact _ _ _ _)) => constructor : okToUnify.

  Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (begin _ _) _) => apply begin_ok : prog.
  Hint Extern 1 ({{_}} Bind (abort _ _) _) => apply abort_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} Bind (commit _ _) _) => apply commit_ok : prog.
  Hint Extern 1 ({{_}} Bind (commit_ro _ _) _) => apply commit_ro_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushall _ _) _) => apply flushall_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushsync _ _) _) => apply flushsync_ok : prog.
  Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.


  Definition read_array xp a i ms :=
    let^ (ms, r) <- read xp (a + i) ms;
    Ret ^(ms, r).

  Definition write_array xp a i v ms :=
    ms <- write xp (a + i) v ms;
    Ret ms.

  Notation arrayP := (arrayN (@ptsto _ addr_eq_dec valuset)).

  Theorem read_array_ok : forall xp ms a i,
    {< F Fm ds m vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms hm *
          [[ i < length vs]] *
          [[[ m ::: Fm * arrayP a vs ]]]
    POST:hm' RET:^(ms', r)
          rep xp F (ActiveTxn ds m) ms' hm' *
          [[ r = fst (selN vs i ($0, nil)) ]] *
          [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm' exists ms',
          rep xp F (ActiveTxn ds m) ms' hm'
    >} read_array xp a i ms.
  Proof.
    unfold read_array.
    hoare.

    subst; pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.
  Qed.


  Theorem write_array_ok : forall xp a i v ms,
    {< F Fm ds m vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms hm *
          [[[ m ::: Fm * arrayP a vs ]]] *
          [[ i < length vs /\ a <> 0 ]]
    POST:hm' RET:ms' exists m',
          rep xp F (ActiveTxn ds m') ms' hm' *
          [[[ m' ::: Fm * arrayP a (updN vs i (v, nil)) ]]]
    CRASH:hm' exists m' ms',
          rep xp F (ActiveTxn ds m') ms' hm'
    >} write_array xp a i v ms.
  Proof.
    unfold write_array.
    prestep. norm. cancel.
    unfold rep_inner; intuition.
    pred_apply; cancel.
    subst; pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    step.
  Qed.

  Hint Extern 1 ({{_}} Bind (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} Bind (write_array _ _ _ _ _) _) => apply write_array_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ ?a _) (rep _ _ _ ?a _)) => constructor : okToUnify.

  Definition read_range A xp a nr (vfold : A -> valu -> A) v0 ms :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds m vs ms0 ]
    Loopvar [ ms pf ]
    Invariant
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) v0 ]] *
      [[ (exists ms00, readOnly ms00 ms0) -> readOnly ms0 ms ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array xp a i ms;
      Ret ^(ms, vfold pf v)
    Rof ^(ms, v0);
    Ret ^(ms, r).


  Definition write_range xp a l ms :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm crash ds vs ]
    Loopvar [ ms ]
    Invariant
      exists m, rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayP a (vsupsyn_range vs (firstn i l))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i $0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.


  Theorem read_range_ok : forall A xp a nr vfold (v0 : A) ms,
    {< F Fm ds m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[ nr <= length vs ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' hm' *
      [[ r = fold_left vfold (firstn nr (map fst vs)) v0 ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' hm'
    >} read_range xp a nr vfold v0 ms.
  Proof.
    unfold read_range; intros.
    safestep. auto. auto.
    subst; pred_apply; cancel.

    eapply readOnly_refl; eauto.
    eauto.
    safestep.
    unfold rep_inner; cancel.
    eapply lt_le_trans; eauto.
    subst; denote (Map.elements (MSTxn a1)) as Hx; rewrite <- Hx.
    pred_apply; cancel.

    step.
    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; subst; auto.
    rewrite map_length; omega.

    unfold rep_inner; cancel.
    step.
    cancel.
    eassign raw; pred_apply.
    cancel; eauto.
    apply GLog.rep_hashmap_subset; eauto.
    Unshelve. exact tt. auto.
  Qed.


  Lemma firstn_vsupsyn_range_firstn_S : forall i vs l,
    i < length l ->
    firstn i (vsupsyn_range vs (firstn (S i) l)) =
    firstn i (vsupsyn_range vs (firstn i l)).
  Proof.
    unfold vsupsyn_range; intros.
    erewrite firstn_S_selN with (def := $0) by auto.
    rewrite app_length; simpl.
    rewrite <- repeat_app.
    rewrite combine_app by (autorewrite with lists; auto); simpl.
    rewrite <- app_assoc.
    repeat rewrite firstn_app_l; auto.
    all: autorewrite with lists; rewrite firstn_length_l; omega.
  Qed.

  Lemma skip_vsupsyn_range_skip_S : forall i vs l,
    i < length l -> length l <= length vs ->
    skipn (S i) (vsupsyn_range vs (firstn (S i) l)) =
    skipn (S i) (vsupsyn_range vs (firstn i l)).
  Proof.
    unfold vsupsyn_range; intros.
    setoid_rewrite skipn_selN_skipn with (def := ($0, nil)) at 4.
    rewrite <- cons_nil_app.
    repeat rewrite skipn_app_eq;
      autorewrite with lists; repeat rewrite firstn_length_l by omega;
      simpl; auto; try omega.
    rewrite firstn_length_l; omega.
  Qed.

  Lemma sep_star_reorder_helper1 : forall AT AEQ V (a b c d : @pred AT AEQ V),
    ((a * b * d) * c) =p=> (a * ((b * c) * d)).
  Proof.
    cancel.
  Qed.

  Lemma vsupsyn_range_progress : forall l a m vs,
    m < length l -> length l <= length vs ->
    arrayP a (updN (vsupsyn_range vs (firstn m l)) m (selN l m $0, nil)) =p=>
    arrayP a (vsupsyn_range vs (firstn (S m) l)).
  Proof.
    unfold vsupsyn_range; intros.
    apply arrayN_unify.
    rewrite updN_app2; autorewrite with lists.
    all: repeat rewrite firstn_length_l; try omega.
    erewrite firstn_S_selN, repeat_app_tail by omega.
    rewrite combine_app, <- app_assoc.
    f_equal.
    rewrite Nat.sub_diag, updN_0_skip_1, skipn_skipn.
    rewrite Nat.add_1_l, cons_app.
    apply eq_refl.
    rewrite skipn_length; omega.
    rewrite firstn_length_l, repeat_length; omega.
  Qed.

  Lemma write_range_length_ok : forall F a i ms d vs,
    i < length vs ->
    (F ✶ arrayP a vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    a + i < length d.
  Proof.
    intros.
    apply list2nmem_arrayN_bound in H0; destruct H0; subst; simpl in *.
    inversion H.
    rewrite replay_disk_length in *.
    omega.
  Qed.

  Theorem write_range_ok : forall xp a l ms,
    {< F Fm ds m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ a <> 0 /\ length l <= length vs ]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' hm' *
      [[[ m' ::: (Fm * arrayP a (vsupsyn_range vs l)) ]]]
    CRASH:hm' exists ms' m',
      rep xp F (ActiveTxn ds m') ms' hm'
    >} write_range xp a l ms.
  Proof.
    unfold write_range; intros.
    step.

    safestep.
    unfold rep_inner; cancel. eauto.
    rewrite vsupsyn_range_length; auto.
    omega.
    rewrite firstn_length_l; omega.

    step.
    eapply vsupsyn_range_progress; eauto.
    unfold rep_inner; cancel.

    step.
    erewrite firstn_oob; eauto.
    eassign raw.
    pred_apply; cancel.
    apply GLog.rep_hashmap_subset; eauto.
    auto.
    Unshelve. exact tt. eauto.
  Qed.


  (* like read_range, but stops when cond is true *)
  Definition read_cond A xp a nr (vfold : A -> valu -> A) v0 (cond : A -> bool) ms :=
    let^ (ms, pf, ret) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds m vs ms0 ]
    Loopvar [ ms pf ret ]
    Invariant
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ ret = None ->
        cond pf = false ]] *
      [[ forall v, ret = Some v ->
        cond v = true ]] *
      [[ ret = None ->
        pf = fold_left vfold (firstn i (map fst vs)) v0 ]] *
      [[ (exists ms00, readOnly ms00 ms0) -> readOnly ms0 ms ]]
    OnCrash  crash
    Begin
      If (is_some ret) {
        Ret ^(ms, pf, ret)
      } else {
        let^ (ms, v) <- read_array xp a i ms;
            let pf' := vfold pf v in
            If (bool_dec (cond pf') true) {
                Ret ^(ms, pf', Some pf')
            } else {
                Ret ^(ms, pf', None)
            }
      }
    Rof ^(ms, v0, None);
    Ret ^(ms, ret).

  Theorem read_cond_ok : forall A xp a nr vfold (v0 : A) cond ms,
    {< F Fm ds m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[ nr <= length vs /\ cond v0 = false ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' hm' *
      ( exists v, [[ r = Some v /\ cond v = true ]] \/
      [[ r = None /\ cond (fold_left vfold (firstn nr (map fst vs)) v0) = false ]]) *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' hm'
    >} read_cond xp a nr vfold v0 cond ms.
  Proof.
    unfold read_cond; intros.
    step.

    safestep.
    safestep.
    safestep.

    unfold rep_inner; cancel.
    eapply lt_le_trans; eauto.
    denote (replay_disk _ _ = replay_disk _ _) as Heq; rewrite <- Heq.
    subst; pred_apply; cancel.

    step; step.
    apply not_true_is_false; auto.
    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; subst; auto.
    rewrite map_length; omega.

    pimpl_crash. unfold rep_inner; norm. cancel. intuition simpl. pred_apply.
    eassign (mk_mstate (MSTxn a1) (MSGLog ms'_1)); cancel.
    eexists.
    eapply hashmap_subset_trans; eauto.

    destruct a2.
    safestep.
    or_l; cancel.
    safestep.
    or_r; cancel.
    eassign raw; pred_apply; cancel.
    apply GLog.rep_hashmap_subset; eauto.
    eauto.

    Unshelve. all: eauto; try exact tt; try exact nil.
  Qed.

  Hint Extern 1 ({{_}} Bind (read_cond _ _ _ _ _ _ _) _) => apply read_cond_ok : prog.
  Hint Extern 1 ({{_}} Bind (read_range _ _ _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_}} Bind (write_range _ _ _ _) _) => apply write_range_ok : prog.


  (******** batch direct write and sync *)

  (* dwrite_vecs discard everything in active transaction *)
  Definition dwrite_vecs (xp : log_xparams) avl ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dwrite_vecs xp avl mm;
    Ret (mk_memstate vmap0 mm').

  Definition dsync_vecs xp al ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync_vecs xp al mm;
    Ret (mk_memstate cm mm').


  Lemma dwrite_ptsto_inbound : forall (F : @pred _ _ valuset) ovl avl m,
    (F * listmatch (fun v e => fst e |-> v) ovl avl)%pred (list2nmem m) ->
    Forall (fun e => (@fst _ valu) e < length m) avl.
  Proof.
    intros.
    apply Forall_map_l.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply.
    rewrite listmatch_map_l.
    rewrite listmatch_sym. eauto.
  Qed.

  Lemma sep_star_reorder_helper2: forall AT AEQ V (a b c d : @pred AT AEQ V),
    (a * (b * (c * d))) <=p=> (a * b * d) * c.
  Proof.
    split; cancel.
  Qed.

  Lemma sep_star_reorder_helper3: forall AT AEQ V (a b c d : @pred AT AEQ V),
    ((a * b) * (c * d)) <=p=> ((a * c * d) * b).
  Proof.
    split; cancel.
  Qed.

  Lemma dwrite_vsupd_vecs_ok : forall avl ovl m F,
    (F * listmatch (fun v e => fst e |-> v) ovl avl)%pred (list2nmem m) ->
    NoDup (map fst avl) ->
    (F * listmatch (fun v e => fst e |-> (snd e, vsmerge v)) ovl avl)%pred (list2nmem (vsupd_vecs m avl)).
  Proof.
    unfold listmatch; induction avl; destruct ovl;
    simpl; intros; eauto; destruct_lift H; inversion H2.
    inversion H0; subst.
    rewrite vsupd_vecs_vsupd_notin by auto.
    denote NoDup as Hx.
    refine (_ (IHavl ovl m _ _ Hx)); [ intro | pred_apply; cancel ].
    erewrite (@list2nmem_sel _ _ m a_1 (p_cur, _)) by (pred_apply; cancel).
    erewrite <- vsupd_vecs_selN_not_in; eauto.
    apply sep_star_reorder_helper2.
    eapply list2nmem_updN.
    pred_apply; cancel.
  Qed.

  Lemma dsync_vssync_vecs_ok : forall al vsl m F,
    (F * listmatch (fun vs a => a |-> vs) vsl al)%pred (list2nmem m) ->
    (F * listmatch (fun vs a => a |-> (fst vs, nil)) vsl al)%pred (list2nmem (vssync_vecs m al)).
  Proof.
    unfold listmatch; induction al; destruct vsl;
    simpl; intros; eauto; destruct_lift H; inversion H1.
    refine (_ (IHal vsl (vssync m a) _ _)).
    apply pimpl_apply; cancel.
    unfold vssync.
    erewrite <- (@list2nmem_sel _ _ m a) by (pred_apply; cancel).
    apply sep_star_reorder_helper3.
    eapply list2nmem_updN.
    pred_apply; cancel.
  Qed.

  Lemma dsync_vssync_vecs_partial : forall al n vsl F m,
    (F * listmatch (fun vs a => a |-> vs) vsl al)%pred (list2nmem m) ->
    (F * listmatch (fun vs a => a |-> vs \/ a |=> fst vs) vsl al)%pred 
        (list2nmem (vssync_vecs m (firstn n al))).
  Proof.
    unfold listmatch; induction al; destruct vsl;
    simpl; intros; eauto; destruct_lift H; inversion H1.
    rewrite firstn_nil; simpl; pred_apply; cancel.

    destruct n; simpl.
    apply sep_star_comm; apply sep_star_assoc; apply sep_star_comm.
    apply sep_star_lift_apply'; auto.
    refine (_ (IHal 0 vsl _ m _)); intros.
    simpl in x; pred_apply; cancel.
    pred_apply; repeat cancel.

    apply sep_star_comm; apply sep_star_assoc; apply sep_star_comm.
    apply sep_star_lift_apply'; auto.
    refine (_ (IHal n vsl _ (vssync m a) _)); intros.
    pred_apply; cancel.

    unfold vssync.
    erewrite <- (@list2nmem_sel _ _ m a) by (pred_apply; cancel); simpl.
    apply sep_star_comm in H.
    apply sep_star_assoc in H.
    eapply list2nmem_updN with (y := (p_cur, nil)) in H.
    pred_apply; repeat cancel.
  Qed.


  Theorem dwrite_vecs_ok : forall xp ms avl,
    {< F Fm ds ovl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm *
      [[[ ds!! ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]] *
      [[ NoDup (map fst avl) /\ sync_invariant F ]]
    POST:hm' RET:ms' exists ds',
      rep xp F (ActiveTxn ds' ds'!!) ms' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]] *
      [[ ds' = (dsupd_vecs ds avl) ]]
    XCRASH:hm'
      recover_any xp F ds hm' \/
      recover_any xp F (dsupd_vecs ds avl) hm'
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs.
    step.
    eapply dwrite_ptsto_inbound; eauto.

    step; subst.
    apply map_valid_map0.
    rewrite dsupd_vecs_latest; apply dwrite_vsupd_vecs_ok; auto.


    (* crash conditions *)
    xcrash.
    or_l; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog ms_1), x0); simpl; eauto.
    pred_apply; cancel.

    or_r; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog ms_1), x0); simpl; eauto.
    pred_apply; cancel.
  Qed.


  Theorem dsync_vecs_ok : forall xp ms al,
    {< F Fm ds vsl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds',
      rep xp F (ActiveTxn ds' ds'!!) ms' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl al ]]] *
      [[ ds' = dssync_vecs ds al ]]
    CRASH:hm'
      recover_any xp F ds hm'
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs, recover_any.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.

    step; subst; try rewrite dssync_vecs_latest.
    apply map_valid_vssync_vecs; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    apply dsync_vssync_vecs_ok; auto.

    Unshelve. eauto.
  Qed.


  Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


  Lemma idempred_hashmap_subset : forall xp F ds hm hm',
    (exists l, hashmap_subset l hm hm')
    -> idempred xp F ds hm
       =p=> idempred xp F ds hm'.
  Proof.
    unfold idempred, recover_any, after_crash, before_crash; cancel.
    rewrite rep_hashmap_subset by eauto.
    or_l; cancel.
    rewrite rep_inner_hashmap_subset in * by eauto.
    or_r. safecancel.
    rewrite rep_inner_hashmap_subset in * by eauto.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor.
    or_r; or_r.
    norm. cancel.
    intuition.
    pred_apply. norm. cancel.
    or_l; cancel.
    intuition simpl; eauto.
    or_r; or_r.
    norm. cancel.
    intuition.
    pred_apply. norm. cancel.
    rewrite rep_inner_hashmap_subset by eauto.
    or_r; cancel.
    intuition simpl; eauto.
  Qed.

  Lemma crash_xform_intact_dssync_vecs_idempred : forall xp F ds al hm,
    crash_xform (LOG.intact xp F (dssync_vecs ds al) hm) =p=>
    LOG.idempred xp (crash_xform F) ds hm.
  Proof.
    intros.
    rewrite crash_xform_intact.
    xform_norm.
    rewrite notxn_after_crash_diskIs.
    rewrite after_crash_idempred.
    cancel.
    pred_apply.
    rewrite dssync_vecs_nthd.
    rewrite crash_xform_diskIs_vssync_vecs; eauto.
    rewrite map_length in *; auto.
  Qed.


  Lemma crash_xform_intact_dssync_vecs_latest_idempred : forall xp F ds al hm gms,
    GLog.dset_match xp ds gms ->
    crash_xform (intact xp F (dssync_vecs (ds!!, nil) al) hm) =p=>
    LOG.idempred xp (crash_xform F) ds hm.
  Proof.
    intros.
    rewrite crash_xform_intact.
    xform_norm.
    apply crash_xform_diskIs_vssync_vecs in H3.
    rewrite notxn_after_crash_diskIs.
    simpl.
    rewrite after_crash_idempred.
    cancel.
    eassign (length ds_2).
    pred_apply.
    repeat rewrite nthd_oob.
    auto.
    all: simpl; auto.
  Qed.

  Lemma crash_xform_cached_before: forall fsxp F d hm ms ds n,
    n <= length (snd ds) ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    crash_xform (rep (FSXPLog fsxp) F (LOG.NoTxn (d, [])) ms hm)
        =p=> crash_xform (before_crash (FSXPLog fsxp) F ds hm).
  Proof.
    intros.
    unfold rep, before_crash, rep_inner.
    xform_norm. cancel.
    xform_norm. cancel.
    xform_norm. norm.
    cancel.
    intuition simpl; eauto.
    pred_apply.
    norm.
    cancel.
    2: eauto.
    unfold GLog.rep.
    intros. norm.
    cancel.
    rewrite MLog.rep_synced_pimpl.
    cancel.
    intuition simpl; auto.
  Qed.


End LOG.


(* rewrite rules for recover_either_pred *)




Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.commit.
Global Opaque LOG.commit_ro.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
