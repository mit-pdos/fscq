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

Import SyncedMem.
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

  Definition rep_inner xp st ms sm hm :=
  let '(cm, mm) := (MSTxn ms, MSGLog ms) in
  (match st with
    | NoTxn ds =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm ds ]] *
      GLog.rep xp (GLog.Cached ds) mm hm
    | ActiveTxn ds cur =>
      [[ map_valid cm ds!! ]] *
      [[ map_replay cm ds!! cur ]] *
      [[ sm_ds_valid sm (pushd cur ds) ]] *
      GLog.rep xp (GLog.Cached ds) mm hm
    | FlushingTxn ds =>
      [[ sm_ds_valid sm ds ]] *
      GLog.would_recover_any xp ds hm
    | RollbackTxn d =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm (d, nil) ]] *
      GLog.rep xp (GLog.Rollback d) mm hm
    | RecoveringTxn d =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm (d, nil) ]] *
      GLog.rep xp (GLog.Recovering d) mm hm
  end)%pred.

  Definition rep xp F st ms sm hm :=
    (exists raw, BUFCACHE.rep (snd ms) raw *
      [[ (F * rep_inner xp st (fst ms) sm hm)%pred raw ]])%pred.

  Definition intact xp F ds sm hm :=
    (exists ms,
      rep xp F (NoTxn ds) ms sm hm \/
      exists new, rep xp F (ActiveTxn ds new) ms sm hm)%pred.

  Definition recover_any xp F ds sm hm :=
    (exists ms, rep xp F (FlushingTxn ds) ms sm hm)%pred.

  Theorem sync_invariant_rep : forall xp F st ms sm hm,
    sync_invariant F ->
    sync_invariant (rep xp F st ms sm hm).
  Proof.
    unfold rep; destruct st; intros; eauto.
  Qed.
  Hint Resolve sync_invariant_rep.

  Theorem sync_invariant_intact : forall xp F ds sm hm,
    sync_invariant F ->
    sync_invariant (intact xp F ds sm hm).
  Proof.
    unfold intact; auto.
  Qed.

  Theorem sync_invariant_recover_any : forall xp F ds sm hm,
    sync_invariant F ->
    sync_invariant (recover_any xp F ds sm hm).
  Proof.
    unfold recover_any; auto.
  Qed.
  Hint Resolve sync_invariant_intact sync_invariant_recover_any.

  Lemma active_intact : forall xp F old new ms sm hm,
    rep xp F (ActiveTxn old new) ms sm hm =p=> intact xp F old sm hm.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma notxn_intact : forall xp F old ms sm hm,
    rep xp F (NoTxn old) ms sm hm =p=> intact xp F old sm hm.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma flushing_any : forall xp F ds ms sm hm,
    rep xp F (FlushingTxn ds) ms sm hm =p=> recover_any xp F ds sm hm.
  Proof.
    unfold recover_any; cancel.
  Qed.

  Lemma intact_any : forall xp F ds sm hm,
    intact xp F ds sm hm =p=> recover_any xp F ds sm hm.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    apply GLog.cached_recover_any.
    eapply sm_ds_valid_pushd_r; eauto.
    Unshelve. all: eauto.
  Qed.

  Lemma notxn_any : forall xp F ds ms sm hm,
    rep xp F (NoTxn ds) ms sm hm =p=> recover_any xp F ds sm hm.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    Unshelve. all: eauto.
  Qed.

  Lemma active_notxn : forall xp F old new ms sm hm,
    rep xp F (ActiveTxn old new) ms sm hm =p=>
    rep xp F (NoTxn old) (mk_mstate vmap0 (MSGLog (fst ms)), (snd ms)) sm hm.
  Proof.
    unfold rep, rep_inner; cancel.
    eapply sm_ds_valid_pushd_r; eauto.
  Qed.

  Lemma active_dset_match_pimpl : forall xp F ds d hm sm ms,
    rep xp F (ActiveTxn ds d) ms sm hm <=p=>
    rep xp F (ActiveTxn ds d) ms sm hm *
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) gms ]].
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.

  Lemma notxn_dset_match_pimpl : forall xp F ds hm sm ms,
    rep xp F (NoTxn ds) ms sm hm <=p=>
    rep xp F (NoTxn ds) ms sm hm *
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) gms ]].
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.

  Lemma rep_inner_hashmap_subset : forall xp ms hm sm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep_inner xp st ms sm hm
        =p=> rep_inner xp st ms sm hm'.
  Proof.
    intros.
    destruct st; unfold rep_inner, GLog.would_recover_any.
    all: try erewrite GLog.rep_hashmap_subset; eauto.
    cancel.
    erewrite GLog.rep_hashmap_subset; eauto.
    auto.
  Qed.

  Lemma rep_hashmap_subset : forall xp F ms hm sm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp F st ms sm hm
        =p=> rep xp F st ms sm hm'.
  Proof.
    unfold rep; intros; cancel.
    erewrite rep_inner_hashmap_subset; eauto.
  Qed.

  Lemma intact_hashmap_subset : forall xp F ds hm sm hm',
    (exists l, hashmap_subset l hm hm')
    -> intact xp F ds sm hm
        =p=> intact xp F ds sm hm'.
  Proof.
    unfold intact; intros; cancel;
    erewrite rep_hashmap_subset; eauto.
    all: cancel.
  Qed.

  Lemma rep_inner_notxn_pimpl : forall xp d ms sm hm,
    rep_inner xp (NoTxn (d, nil)) ms sm hm
    =p=> exists ms', rep_inner xp (RecoveringTxn d) ms' sm hm.
  Proof.
    unfold rep_inner; intros.
    rewrite GLog.cached_recovering.
    norm'l. cancel.
    eassign (mk_mstate vmap0 ms'); auto.
    apply map_empty_vmap0.
  Qed.

  Lemma rep_inner_rollbacktxn_pimpl : forall xp d ms sm hm,
    rep_inner xp (RollbackTxn d) ms sm hm
    =p=> rep_inner xp (RecoveringTxn d) ms sm hm.
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
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    match Map.find a cm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- GLog.read xp a mm;
        Ret ^(mk_memstate cm mm', v)
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

  Lemma possible_crash_list2nmem_synced: forall d' d,
    possible_crash d (list2nmem d') ->
    Forall (fun v => snd v = nil) d'.
  Proof.
    induction d' using rev_ind; intros.
    constructor.
    apply Forall_app.
    eapply IHd'.
    eapply possible_crash_mem_except in H.
    rewrite list2nmem_except_last in *.
    eauto.
    specialize (H (length d')); cbn in *.
    erewrite list2nmem_sel_inb in *.
    intuition.
    congruence.
    rewrite selN_app2 in * by auto.
    rewrite Nat.sub_diag in *; cbn in *.
    repeat deex.
    inversion H; subst; auto.
    inversion H; subst; auto.
    rewrite app_length; cbn; omega.
  Unshelve.
    all: auto.
  Qed.

  Lemma sm_vs_valid_crash_xform: forall ds sm d n,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    sm_ds_valid sm ds ->
    sm_vs_valid sm d.
  Proof.
    intros.
    unfold crash_xform, diskIs in *.
    deex.
    eapply sm_vs_valid_all_synced.
    eapply sm_ds_valid_nthd; eauto.
    eauto using possible_crash_list2nmem_length.
    eauto using possible_crash_list2nmem_synced.
  Qed.

  Lemma sm_vs_valid_disk_synced: forall d d',
    crash_xform (diskIs (list2nmem d')) (list2nmem d) ->
    sm_vs_valid (sm_disk_synced d) d.
  Proof.
    intros.
    apply crash_xform_diskIs in H.
    destruct_lift H.
    unfold diskIs in *; subst.
    eapply possible_crash_list2nmem_synced in H0.
    unfold sm_disk_synced, sm_vs_valid.
    rewrite Forall_forall in *.
    intuition.
    erewrite list2nmem_sel_inb in H1.
    congruence.
    autorewrite with lists; auto.
    unfold vs_synced.
    rewrite H0; auto.
    eapply in_selN; auto.
  Unshelve.
    all: constructor.
  Qed.


  Lemma listpred_ptsto_combine_ex : forall AT AEQ V a b,
    length a = length b ->
    listpred (pprd (fun y x => @ptsto AT AEQ V x y)) (List.combine b a) =p=> listpred (fun x => x |->?) a.
  Proof.
    induction a; cbn; intros;
      destruct b; cbn in *; try congruence.
    rewrite IHa by omega.
    cancel.
  Qed.

  Lemma listpred_ptsto_combine_same : forall AT AEQ V f k a b,
    length a = length b ->
    (forall (x : AT) (y : V), In (y, x) (filter (fun x => f (snd x)) (List.combine b a)) -> y = k) ->
    listpred (pprd (fun y x => @ptsto AT AEQ V x y)) (filter (fun x => f (snd x)) (List.combine b a)) =p=> listpred (fun x => x |-> k) (filter f a).
  Proof.
    intros.
    setoid_rewrite filter_In in H0.
    generalize dependent b.
    generalize dependent a.
    induction a; cbn; intros;
      destruct b; cbn in *; try congruence.
    denote In as Hi.
    destruct f eqn:Hf; cbn in *; eauto.
    rewrite IHa; auto.
    cancel.
    erewrite Hi with (y := v); eauto.
    intuition.
    eapply Hi; split; eauto.
    rewrite IHa; eauto.
    intuition.
    eapply Hi; split; eauto.
  Qed.

  Lemma listpred_ptsto_combine_same' : forall AT AEQ V (F : (V * AT) -> @pred AT AEQ V) k a b,
    length a = length b ->
    (forall x y, In (y, x) (List.combine b a) -> F (y, x) =p=> x |-> k) ->
    listpred F (List.combine b a) =p=> listpred (fun x => x |-> k) a.
  Proof.
    induction a; cbn; intros;
      destruct b; cbn in *; try congruence.
    rewrite IHa, H0 by (auto; omega). cancel.
  Qed.


  Local Hint Resolve sm_vs_valid_upd_synced vs_synced_updN_synced
     sm_ds_valid_synced sm_ds_valid_pushd_l sm_ds_valid_pushd_r
     sm_ds_valid_pushd sm_ds_valid_dsupd sm_ds_valid_pushd_latest
     sm_ds_valid_dssync list2nmem_inbound ptsto_upd'
     sm_ds_valid_dsupd_vecs sm_ds_valid_dssync_vecs.


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
    POST:hm' RET: ms exists d sm l,
          rep xp F (NoTxn (d, nil)) ms sm hm' *
          [[[ d ::: arrayN (@ptsto _ _ _) 0 d ]]] *
          [[ arrayN (@ptsto _ _ _) 0 l sm ]] * [[ length l = length d ]] *
          [[ length d = (LogHeader xp) - (DataStart xp) ]]
    XCRASH:hm_crash any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    step.
    apply sm_ds_valid_synced.
    apply sm_vs_valid_disk_exact.
    apply list2nmem_array.
    apply list2nmem_array.
    autorewrite with lists. auto.
  Qed.


  Theorem begin_ok: forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm
    POST:hm' RET:r
      rep xp F (ActiveTxn ds ds!!) r sm hm' *
      [[ readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' sm hm'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
    rewrite replay_disk_empty; auto.
  Qed.


  Theorem abort_ok : forall xp ms,
    {< F ds sm m,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r sm hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' sm hm'
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
    {< F Fm ds sm m v,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: Fm * a |-> v ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm hm' * [[ r = fst v ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' sm hm'
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
    {< F Fm ds m sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm * [[ a <> 0 ]] *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' sm hm' *
      [[[ m' ::: (Fm * a |-> (v, nil)) ]]]
    CRASH:hm'
      exists m' ms', rep xp F (ActiveTxn ds m') ms' sm hm'
    >} write xp a v ms.
  Proof.
    unfold write.
    hoare using dems.
    pred_apply; cancel.

    apply map_valid_add; eauto.
    erewrite <- replay_disk_length.
    eapply list2nmem_ptsto_bound; eauto.

    rewrite replay_disk_add; eauto.

    rewrite replay_disk_add.
    eapply list2nmem_updN. eauto.
  Qed.

  Set Regular Subst Tactic.

  Theorem dwrite_ok : forall xp ms a v,
    {< F Fm Fs ds sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ (Fs * a |->?)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: (Fm * a |-> (v, vsmerge vs)) ]]] *
      [[ (Fs * a |-> false)%pred sm' ]] *
      [[ ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:hm'
      recover_any xp F ds sm hm' \/
      recover_any xp F (dsupd ds a (v, vsmerge vs)) (Mem.upd sm a false) hm'
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
    eauto.

    or_r; cancel.
    xform_normr; cancel.
    eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem dsync_ok : forall xp ms a,
    {< F Fm Fs ds sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ (Fs * a |->?)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[ ds' = dssync ds a ]] *
      [[ (Fs * a |-> true)%pred sm' ]]
    CRASH:hm'
      recover_any xp F ds sm hm'
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
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds sm hm'
    >} flushall xp ms.
  Proof.
    unfold flushall, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.


  Theorem flushsync_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds sm hm'
    >} flushsync xp ms.
  Proof.
    unfold flushsync, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.

  Theorem flushall_noop_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn ds) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds sm hm'
    >} flushall_noop xp ms.
  Proof.
    unfold flushall_noop, recover_any.
    hoare.
    xcrash.
    Unshelve. eauto.
  Qed.

  Theorem flushsync_noop_ok : forall xp ms,
    {< F sm ds,
    PRE:hm
      rep xp F (NoTxn ds) ms sm hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      rep xp F (NoTxn ds) ms' sm hm'
    XCRASH:hm'
      recover_any xp F ds sm hm'
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
    {< F sm ds m,
     PRE:hm  rep xp F (ActiveTxn ds m) ms sm hm *
            [[ sync_invariant F ]]
     POST:hm' RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn (pushd m ds)) ms' sm hm') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn (fst ms)) > (LogLen xp) ]] *
            rep xp F (NoTxn ds) ms' sm hm')
     XCRASH:hm' recover_any xp F (pushd m ds) sm hm'
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
    {< F sm ds,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r sm hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' sm hm'
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
     [[ ( exists d sm n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (NoTxn (d, nil)) ms sm hm \/
            rep_inner xp (RollbackTxn d) ms sm hm) *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.

  Definition before_crash xp F ds hm :=
    (exists cs raw, BUFCACHE.rep cs raw *
     [[ ( exists d sm n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (RecoveringTxn d) ms sm hm) *
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
      exists d sm n, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms' sm hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
      [[ arrayN (@ptsto _ _ _) 0 (repeat true (length d)) sm ]]
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
    eapply sm_ds_valid_synced.
    eapply sm_vs_valid_disk_synced; eauto.
    apply list2nmem_array.

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
    eapply sm_ds_valid_synced.
    eapply sm_vs_valid_disk_synced; eauto.
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
    eapply sm_ds_valid_disk_unsynced.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.

    unfold stars; simpl.
    cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    auto.
    eapply sm_ds_valid_disk_unsynced.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.


  Lemma crash_xform_any : forall xp F ds sm hm,
    crash_xform (recover_any xp F ds sm hm) =p=>
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
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    intuition simpl; eauto.
    cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms); eauto.
    eauto.
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    intuition simpl; eauto.
  Qed.


  Lemma after_crash_notxn : forall xp cs F ds hm,
    after_crash xp F ds cs hm =p=>
      exists d n sm ms, [[ n <= length (snd ds) ]] *
      (rep xp F (NoTxn (d, nil)) ms sm hm \/
        rep xp F (RollbackTxn d) ms sm hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
  Proof.
    unfold after_crash, recover_any, rep, rep_inner.
    intros. norm. cancel.
    denote or as Hor; apply sep_star_or_distr in Hor.
    destruct Hor; destruct_lift H.
    or_l; cancel.
    eauto.
    or_r; cancel.
    intuition simpl. eassumption.
    auto.
  Qed.


  Lemma after_crash_notxn_singular : forall xp cs F d hm,
    after_crash xp F (d, nil) cs hm =p=>
      exists d' sm ms, (rep xp F (NoTxn (d', nil)) ms sm hm \/
                      rep xp F (RollbackTxn d') ms sm hm) *
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
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.

    rewrite GLog.crash_xform_rollback.
    norm. cancel.
    or_r; cancel.
    eassign (mk_mstate vmap0 ms'); cancel.
    auto.
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    intuition simpl; eauto.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.

  Lemma after_crash_idem' : forall xp d ms sm hm (F : rawpred),
    F (list2nmem d) ->
    crash_xform (rep_inner xp (NoTxn (d, nil)) ms sm hm
              \/ rep_inner xp (RollbackTxn d) ms sm hm) =p=>
    exists d' ms' sm',(rep_inner xp (NoTxn (d', nil)) ms' sm' hm \/
                   rep_inner xp (RollbackTxn d') ms' sm' hm) *
                   [[ (crash_xform F) (list2nmem d') ]].
  Proof.
    unfold rep_inner; intros.
    xform_norml.
    rewrite GLog.crash_xform_cached; cancel.
    eassign (mk_mstate vmap0 ms').
    or_l; cancel.
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    eapply crash_xform_diskIs_pred; eauto.

    rewrite GLog.crash_xform_rollback; cancel.
    eassign (mk_mstate vmap0 ms').
    or_r; cancel.
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    eapply crash_xform_diskIs_pred; eauto.
  Qed.

  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _ _) (LOG.rep_inner _ _ _ _ _)) => constructor : okToUnify.

  (* TODO: Would be better to rewrite using hashmap_subset. *)
  Instance rep_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> eq ==> pimpl) rep.
  Proof.
    unfold Proper, respectful; intros.
    unfold rep; cancel.
    apply H0.
  Qed.

  Instance intact_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> pimpl) intact.
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

  Lemma notxn_after_crash_diskIs : forall xp F n ds d ms sm hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (NoTxn (d, nil)) ms sm hm =p=> after_crash xp F ds (snd ms) hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    or_l; cancel.
    eauto.
    eauto.
    auto.
  Qed.

  Lemma rollbacktxn_after_crash_diskIs : forall xp F n d ds ms sm hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (RollbackTxn d) ms sm hm =p=> after_crash xp F ds (snd ms) hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    or_r; cancel.
    eauto.
    eauto.
    auto.
  Qed.

  (** idempred includes both before-crash cand after-crash cases *)
  Definition idempred xp F ds sm hm :=
    (recover_any xp F ds sm hm \/
      before_crash xp F ds hm \/
      exists cs, after_crash xp F ds cs hm)%pred.

  Theorem sync_invariant_idempred : forall xp F ds sm hm,
    sync_invariant F ->
    sync_invariant (idempred xp F ds sm hm).
  Proof.
    unfold idempred; auto.
  Qed.
  Hint Resolve sync_invariant_idempred.

  Theorem idempred_idem : forall xp F ds sm hm,
    crash_xform (idempred xp F ds sm hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
  Proof.
    unfold idempred; intros.
    xform_norm.
    rewrite crash_xform_any; cancel.
    rewrite crash_xform_before_crash; cancel.
    rewrite after_crash_idem; cancel.
  Qed.

  Theorem recover_any_idempred : forall xp F ds sm hm,
    recover_any xp F ds sm hm =p=> idempred xp F ds sm hm.
  Proof.
    unfold idempred; cancel.
  Qed.

  Theorem intact_idempred : forall xp F ds sm hm,
    intact xp F ds sm hm =p=> idempred xp F ds sm hm.
  Proof.
    intros.
    rewrite intact_any.
    apply recover_any_idempred.
  Qed.

  Theorem notxn_idempred : forall xp F ds ms sm hm,
    rep xp F (NoTxn ds) ms sm hm =p=> idempred xp F ds sm hm.
  Proof.
    intros.
    rewrite notxn_intact.
    apply intact_idempred.
  Qed.

  Theorem active_idempred : forall xp F ds ms d sm hm,
    rep xp F (ActiveTxn ds d) ms sm hm =p=> idempred xp F ds sm hm.
  Proof.
    intros.
    rewrite active_intact.
    apply intact_idempred.
  Qed.

  Theorem after_crash_idempred : forall xp F ds cs sm hm,
    after_crash xp F ds cs hm =p=> idempred xp F ds sm hm.
  Proof.
    unfold idempred; intros.
    or_r; cancel.
  Qed.

  Theorem before_crash_idempred : forall xp F ds sm hm,
    before_crash xp F ds hm =p=> idempred xp F ds sm hm.
  Proof.
    unfold idempred; intros.
    or_r; or_l; cancel.
  Qed.

  Instance idempred_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> pimpl) idempred.
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

  Theorem crash_xform_intact : forall xp F ds sm hm,
    crash_xform (intact xp F ds sm hm) =p=>
      exists ms d n, rep xp (crash_xform F) (NoTxn (d, nil)) ms sm hm *
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
    eapply sm_ds_valid_synced.
    eapply sm_vs_valid_crash_xform; eauto.
    eauto.
    eauto.

    safecancel.
    eassign (mk_mstate vmap0 dummy1).
    cancel. auto.
    eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto.
    eauto. auto.
  Qed.

  Theorem crash_xform_idempred : forall xp F ds sm hm,
    crash_xform (idempred xp F ds sm hm) =p=>
      exists ms d sm n,
        (rep xp (crash_xform F) (NoTxn (d, nil)) ms sm hm \/
          rep xp (crash_xform F) (RollbackTxn d) ms sm hm) *
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
      cancel. auto.
      eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto.
      eassumption. auto.

      safecancel.
      or_r; cancel.
      eassign (mk_mstate (Map.empty valu) dummy1).
      cancel. auto.
      eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto.
      eassumption. auto.

    - apply crash_xform_sep_star_dist in Hx;
      rewrite GLog.crash_xform_recovering in Hx;
      unfold GLog.recover_any_pred in Hx;
      destruct_lift Hx.

      denote or as Hor.
      apply sep_star_or_distr in Hor.
      destruct Hor.

      safecancel.
      or_l; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.


      safecancel.
      or_r; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.

    - apply crash_xform_sep_star_dist in Hx.
      rewrite crash_xform_or_dist in Hx.
      apply sep_star_or_distr in Hx;
      destruct Hx; autorewrite with crash_xform in H0.

      rewrite GLog.crash_xform_cached in H0.
      destruct_lift H0.
      safecancel.
      or_l; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.

      rewrite GLog.crash_xform_rollback in H0.
      destruct_lift H0.
      safecancel.
      or_r; cancel.
      match goal with |- context [?x] => eassign (mk_mstate (Map.empty valu) x) end.
      cancel. auto.
      eapply sm_ds_valid_synced, sm_vs_valid_crash_xform; eauto; eauto.
      eassumption.
      eapply crash_xform_diskIs_trans; eauto.
  Unshelve.
    all: eauto.
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

  Notation arrayP := (arrayN (@ptsto _ addr_eq_dec _)).

  Theorem read_array_ok : forall xp ms a i,
    {< F Fm ds m sm vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms sm hm *
          [[ i < length vs]] *
          [[[ m ::: Fm * arrayP a vs ]]]
    POST:hm' RET:^(ms', r)
          rep xp F (ActiveTxn ds m) ms' sm hm' *
          [[ r = fst (selN vs i ($0, nil)) ]] *
          [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm' exists ms',
          rep xp F (ActiveTxn ds m) ms' sm hm'
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
    {< F Fm ds sm m vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms sm hm *
          [[[ m ::: Fm * arrayP a vs ]]] *
          [[ i < length vs /\ a <> 0 ]]
    POST:hm' RET:ms' exists m',
          rep xp F (ActiveTxn ds m') ms' sm hm' *
          [[[ m' ::: Fm * arrayP a (updN vs i (v, nil)) ]]]
    CRASH:hm' exists m' ms',
          rep xp F (ActiveTxn ds m') ms' sm hm'
    >} write_array xp a i v ms.
  Proof.
    unfold write_array.
    prestep. norm. cancel.
    unfold rep_inner; intuition.
    pred_apply; cancel.
    eauto.
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

  Hint Extern 0 (okToUnify (rep _ _ _ ?a _ _) (rep _ _ _ ?a _ _)) => constructor : okToUnify.

  Definition read_range A xp a nr (vfold : A -> valu -> A) v0 ms :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds sm m vs ms0 ]
    Loopvar [ ms pf ]
    Invariant
      rep xp F (ActiveTxn ds m) ms sm hm *
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
    Ghost [ F Fm crash ds sm vs ]
    Loopvar [ ms ]
    Invariant
      exists m, rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: (Fm * arrayP a (vsupsyn_range vs (firstn i l))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i $0) ms;
      Ret ^(ms)
    Rof ^(ms);
    Ret ms.


  Theorem read_range_ok : forall A xp a nr vfold (v0 : A) ms,
    {< F Fm ds sm m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[ nr <= length vs ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm hm' *
      [[ r = fold_left vfold (firstn nr (map fst vs)) v0 ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' sm hm'
    >} read_range xp a nr vfold v0 ms.
  Proof.
    unfold read_range; intros.
    safestep. auto. auto. eauto.
    subst; pred_apply; cancel.

    eapply readOnly_refl; eauto.
    eauto.
    safestep.
    unfold rep_inner; cancel.
    subst; denote (Map.elements (MSTxn a1)) as Hx; rewrite <- Hx.
    eauto.
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
    {< F Fm ds m sm vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ a <> 0 /\ length l <= length vs ]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' sm hm' *
      [[[ m' ::: (Fm * arrayP a (vsupsyn_range vs l)) ]]]
    CRASH:hm' exists ms' m',
      rep xp F (ActiveTxn ds m') ms' sm hm'
    >} write_range xp a l ms.
  Proof.
    unfold write_range; intros.
    step.

    safestep.
    unfold rep_inner; cancel. eauto. eauto.
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
    auto.
    Unshelve. exact tt. eauto.
  Qed.


  (* like read_range, but stops when cond is true *)
  Definition read_cond A xp a nr (vfold : A -> valu -> A) v0 (cond : A -> bool) ms :=
    let^ (ms, pf, ret) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds sm m vs ms0 ]
    Loopvar [ ms pf ret ]
    Invariant
      rep xp F (ActiveTxn ds m) ms sm hm *
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
    {< F Fm ds sm m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms sm hm *
      [[ nr <= length vs /\ cond v0 = false ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm hm' *
      ( exists v, [[ r = Some v /\ cond v = true ]] \/
      [[ r = None /\ cond (fold_left vfold (firstn nr (map fst vs)) v0) = false ]]) *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' sm hm'
    >} read_cond xp a nr vfold v0 cond ms.
  Proof.
    unfold read_cond; intros.
    step.

    safestep.
    safestep.
    safestep.

    unfold rep_inner; cancel.
    denote (replay_disk _ _ = replay_disk _ _) as Heq; rewrite <- Heq.
    eauto.
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


  Lemma sm_upd_vecs_listpred_ptsto: forall a sm F,
    (F * listpred (fun a => (fst a) |->?) a)%pred sm ->
    (F * listpred (fun a => (fst a) |-> false) a)%pred (sm_upd_vecs sm a).
  Proof.
    induction a; intros.
    cbn in *; auto.
    rewrite sm_upd_vecs_cons.
    cbn in *.
    destruct_lifts.
    eapply pimpl_apply.
    2: eapply ptsto_upd'. cancel.
    eapply pimpl_apply in H.
    eapply IHa in H.
    2: cancel.
    pred_apply; cancel.
  Qed.

  Lemma sm_sync_vecs_listpred_ptsto: forall a sm F,
    (F * listpred (fun a => a |->?) a)%pred sm ->
    (F * listpred (fun a => a |-> true) a)%pred (sm_sync_vecs sm a).
  Proof.
    induction a; intros.
    cbn in *; auto.
    rewrite sm_sync_vecs_cons.
    cbn in *.
    destruct_lifts.
    eapply pimpl_apply.
    2: eapply ptsto_upd'. cancel.
    eapply pimpl_apply in H.
    eapply IHa in H.
    2: cancel.
    pred_apply; cancel.
  Qed.


  Theorem dwrite_vecs_ok : forall xp ms avl,
    {< F Fs Fm ds sm ovl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]] *
      [[ (Fs * listpred (fun e => (fst e) |->?) avl)%pred sm ]] *
      [[ NoDup (map fst avl) /\ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]] *
      [[ (Fs * listpred (fun e => (fst e) |-> false) avl)%pred sm' ]] *
      [[ ds' = (dsupd_vecs ds avl) ]]
    XCRASH:hm'
      recover_any xp F ds sm hm' \/
      recover_any xp F (dsupd_vecs ds avl) (sm_upd_vecs sm avl) hm'
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs.
    step.
    eapply dwrite_ptsto_inbound; eauto.

    step; subst.
    apply map_valid_map0.
    rewrite dsupd_vecs_latest; apply dwrite_vsupd_vecs_ok; auto.
    eapply sm_upd_vecs_listpred_ptsto; eauto.

    (* crash conditions *)
    xcrash.
    or_l; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog ms_1), x0); simpl; eauto.
    unfold rep_inner.
    pred_apply; cancel.
    eauto.

    or_r; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog ms_1), x0); simpl; eauto.
    unfold rep_inner.
    pred_apply; cancel.
    eauto.
  Qed.


  Theorem dsync_vecs_ok : forall xp ms al,
    {< F Fs Fm ds sm vsl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]] *
      [[ (Fs * listpred (fun a => a |->?) al)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl al ]]] *
      [[ (Fs * listpred (fun a => a |-> true) al)%pred sm' ]] *
      [[ ds' = dssync_vecs ds al ]]
    CRASH:hm'
      recover_any xp F ds sm hm'
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
    apply sm_sync_vecs_listpred_ptsto; eauto.

    Unshelve. eauto.
  Qed.

  Lemma sm_vs_valid_listpred_Forall: forall l F sm vs,
    (F * listpred (fun a => a |-> true) l)%pred sm ->
    sm_vs_valid sm vs ->
    Forall (fun a => vs_synced a vs) l.
  Proof.
    induction l; intros.
    constructor.
    constructor.
    cbn in H.
    eapply pimpl_apply, ptsto_valid with (a := a) in H.
    2: cancel.
    eapply sm_vs_valid_vs_synced; eauto.
    eapply IHl; eauto.
    pred_apply; cancel.
  Qed.

  Lemma sm_ds_valid_listpred_Forall: forall l F sm ds,
    (F * listpred (fun a => a |-> true) l)%pred sm ->
    sm_ds_valid sm ds ->
    Forall (fun a => ds_synced a ds) l.
  Proof.
    induction l; intros.
    constructor.
    constructor.
    cbn in H.
    eapply pimpl_apply, ptsto_valid with (a := a) in H.
    2: cancel.
    eapply sm_ds_valid_ds_synced; eauto.
    eapply IHl; eauto.
    pred_apply; cancel.
  Qed.

  (* alternative spec for syncing only the unsynced subset of a list *)
  Theorem dsync_vecs_additional_ok' : forall xp ms al,
    {< F Fs Fm ds sm all synced vsl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[ all = al ++ synced ]] *
      [[ (Fs * listpred (fun a => a |->?) al * listpred (fun a => a |-> true) synced)%pred sm ]] *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl all ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl all ]]] *
      [[ (Fs * listpred (fun a => a |-> true) all)%pred sm' ]] *
      [[ ds' = dssync_vecs ds all ]]
    CRASH:hm'
      recover_any xp F ds sm hm'
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs, recover_any.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.
    eassign (firstn (length al) vsl).
    erewrite <- firstn_skipn with (l := vsl) (n := length al) at 1.
    rewrite listmatch_app_rev. cancel.
    rewrite firstn_length_l in *; auto.
    destruct_lifts.
    erewrite listmatch_length_pimpl in H.
    destruct_lift H.
    autorewrite with lists in *; omega.

    step; subst; try rewrite dssync_vecs_latest.
    apply map_valid_vssync_vecs; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    erewrite <- vssync_vecs_nop with (vs := ds!!).
    rewrite vssync_vecs_app', vssync_vecs_app_comm.
    apply dsync_vssync_vecs_ok; auto.

    eapply sm_vs_valid_listpred_Forall; eauto.
    rewrite listpred_app.
    eapply pimpl_apply.
    2: eapply sm_sync_vecs_listpred_ptsto. cancel.
    pred_apply; cancel.

    rewrite dssync_vecs_app.
    rewrite dssync_vecs_nop with (l := synced); auto.
    eapply sm_ds_valid_listpred_Forall; eauto.
    eapply sm_ds_valid_dssync_vecs'; eauto.
    Unshelve. eauto.
  Qed.

  Hint Resolve Nat.eqb_eq.
  Hint Rewrite sort_by_index_length split_length_l split_length_r : lists.

  (* alternative spec for syncing only the unsynced subset of a list *)
  Theorem dsync_vecs_additional_ok : forall xp ms al,
    {< F Fs Fm ds sm all vsl sml,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms sm hm *
      [[ (Fs * listmatch (fun b a => a |-> b) sml all)%pred sm ]] *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl all ]]] *
      [[ forall i, i < length all -> In (selN all i 0) al \/ selN sml i false = true ]] *
      [[ incl al all ]] * [[ NoDup al (* not strictly necessary, but useful *)]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl all ]]] *
      [[ (Fs * listpred (fun a => a |-> true) all)%pred sm' ]] *
      [[ ds' = dssync_vecs ds all ]]
    CRASH:hm'
      recover_any xp F ds sm hm'
    >} dsync_vecs xp al ms.
  Proof.
    intros.
    eapply pimpl_ok2.
    eapply dsync_vecs_additional_ok'.
    intros. norml.
    assert (NoDup all).
    eapply listmatch_nodup with (m := sm) (b := sml).
    pred_apply. rewrite listmatch_sym. cancel.
    assert (length sml = length all) by eauto using listmatch_length_r.
    assert (length vsl = length all) by eauto using listmatch_length_r.
    cancel.

    (* split synced from all in syncedmem *)
    unfold listmatch.
    erewrite listpred_partition with (f := fun x => inb al (snd x)).
    rewrite partition_eq_filter; cbn [fst snd].
    rewrite listpred_permutation with (a := filter _ _).
    2: eapply Permutation.Permutation_sym, filter_elements_permutation; auto.
    2: rewrite map_snd_combine; auto.
    erewrite <- listpred_ptsto_combine_ex.
    rewrite <- sort_by_index_combine with (f := Nat.eqb) (la := sml) (lb := all); eauto.
    eassign 0. repeat eassign true.
    cancel.
    erewrite filter_ext.
    rewrite listpred_ptsto_combine_same; auto.
    solve [apply pimpl_refl | apply sep_star_comm].
    2: intros; cbn.
    2: match goal with |- ?X = ?Y ?y =>
        match eval pattern y in X with
        | ?X' y => unify X' Y end end; auto.
    intros x y Hi.
    rewrite filter_In in Hi. destruct Hi as [Ha Hb].
    denote selN as Hs.
    unfold inb in Hb.
    eapply in_selN_exists in Ha.
    destruct Ha as [i [Hc Ha] ].
    erewrite selN_combine in Ha by auto.
    rewrite <- Ha in *.
    destruct in_dec; cbn in *; try congruence.
    rewrite combine_length_eq2 in Hc by auto.
    eapply Hs in Hc.
    intuition eauto.
    inversion Ha; eauto.
    autorewrite with lists; auto.
    intros.
    eapply in_combine_ex_l; eauto; omega.

    (* split unsynced from all on disk *)
    unfold listmatch.
    rewrite listpred_permutation.
    cancel. solve [reflexivity].
    shelve.
    rewrite combine_app.
    erewrite partition_permutation_app.
    rewrite partition_eq_filter.
    cbn [fst snd].
    apply Permutation.Permutation_app.
    rewrite <- filter_elements_permutation with (a := al); auto.
    rewrite sort_by_index_combine; auto.
    rewrite map_snd_combine; auto.
    intros.
    eapply in_combine_ex_l; auto; omega.
    rewrite <- filter_r; auto.
    autorewrite with lists; auto.
    Unshelve.
    2: autorewrite with lists.
    2: replace (length vsl) with (length all) by auto.
    2: erewrite filter_selN_length with (l := all); eauto.
    eapply pimpl_ok2. eauto.
    cancel.

    (* reassemble disk pred *)
    unfold listmatch.
    rewrite listpred_permutation.
    cancel.
    rewrite combine_app by (rewrite split_length_l, sort_by_index_length; auto).
    symmetry.
    eapply Permutation.Permutation_trans.
    apply partition_permutation_app.
    rewrite partition_eq_filter.
    cbn [fst snd].
    apply Permutation.Permutation_app.
    rewrite <- filter_elements_permutation with (a := al); auto.
    rewrite sort_by_index_combine; auto.
    rewrite map_snd_combine; auto.
    intros.
    eapply in_combine_ex_l; auto; omega.
    cbn beta.
    erewrite filter_ext.
    erewrite filter_r; auto.
    2: intros; cbn.
    2: match goal with |- ?X = ?Y ?y =>
        match eval pattern y in X with
        | ?X' y => unify X' Y end end; auto.
    cbn. reflexivity.

    (* reassemble syncedmem pred *)
    unfold listmatch.
    apply listpred_permutation.
    eapply Permutation.Permutation_trans.
    apply partition_permutation_app.
    rewrite partition_eq_filter; cbn [fst snd].
    apply Permutation.Permutation_app; try reflexivity.
    apply permutation_filter; auto.

    (* reorder sync vec arguments *)
    apply dssync_vecs_permutation.
    symmetry.
    eapply Permutation.Permutation_trans.
    eapply partition_permutation_app.
    rewrite partition_eq_filter; cbn [fst snd].
    apply Permutation.Permutation_app; try reflexivity.
    apply permutation_filter; auto.
  Unshelve.
    all: solve [exact 0 | exact ($0, [])].
  Qed.



  Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


  Lemma idempred_hashmap_subset : forall xp F ds sm hm hm',
    (exists l, hashmap_subset l hm hm')
    -> idempred xp F ds sm hm
       =p=> idempred xp F ds sm hm'.
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

  Lemma crash_xform_intact_dssync_vecs_idempred : forall xp F sm ds al hm,
    crash_xform (LOG.intact xp F (dssync_vecs ds al) sm hm) =p=>
    LOG.idempred xp (crash_xform F) ds sm hm.
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


  Lemma crash_xform_cached_before: forall fsxp F d hm ms ds sm n,
    n <= length (snd ds) ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    crash_xform (rep (FSXPLog fsxp) F (LOG.NoTxn (d, [])) ms sm hm)
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
    intuition simpl; eauto.
    intuition simpl; eauto.
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
