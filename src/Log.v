Require Import Arith.
Require Import Bool.
Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Classes.SetoidTactics.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Mem Pred.
Require Import FunctionalExtensionality.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Eqdep_dec.
Require Import WordAuto.
Require Import ListUtils ListPred.
Require Import FSLayout.
Require Import MapUtils.
Require Import RelationClasses.
Require Import Morphisms.

Require Export GroupLog.

Import SyncedMem.
Import ListNotations.

Set Implicit Arguments.

Parameter should_flushall : bool.

Ltac solve_sync_invariant :=
  match goal with
  | [ |- forall _, sync_invariant _] =>
    intros; try solve_sync_invariant
  | [ |- sync_invariant (exists _, _)] =>
    apply sync_invariant_exists; intros; try solve_sync_invariant
  | [ |- sync_invariant (_ * _)] =>
    apply sync_invariant_sep_star; try solve_sync_invariant
  | [ |- sync_invariant (_ /\ _)] =>
    apply sync_invariant_and; try solve_sync_invariant
  | [ |- sync_invariant (_ \/ _)] =>
    apply sync_invariant_or; try solve_sync_invariant
  | [ |- sync_invariant ([[ _ ]]) ] =>
    apply sync_invariant_lift_empty; try solve_sync_invariant
  end.

Hint Extern 0 (sync_invariant _) => solve_sync_invariant.


Module LOG.

  Import AddrMap LogReplay.

  Record mstate := mk_mstate {
    MSTxn   : handlemap;         (* memory state for active txns *)
    MSGLog  : GLog.mstate    (* lower-level state *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate mm (ll : GLog.memstate) : memstate :=
    (mk_mstate mm (fst ll), (snd ll)).
  Definition mk_memstate0 (cs: cachestate) := (mk_mstate hmap0 GLog.mk_memstate0, cs).

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
                
  | RecoveringTxn (old : diskstate)
  .

  Definition rep_inner xp st ms sm bm hm :=
  let '(cm, mm) := (MSTxn ms, MSGLog ms) in
  ([[ Forall (fun t => t = dummy_handle)
            (map fst (extract_blocks bm (map snd (Map.elements cm)))) ]] *  
  match st with
    | NoTxn ds =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm ds ]] *
      GLog.rep xp (GLog.Cached ds) mm bm hm
    | ActiveTxn ds cur =>
      [[ handles_valid_map bm cm ]] *
      [[ map_valid cm ds!! ]] *
      [[ map_replay (extract_blocks_map bm tagged_block0 cm) ds!! cur ]] *
      [[ sm_ds_valid sm (pushd cur ds) ]] *
      GLog.rep xp (GLog.Cached ds) mm bm hm
    | FlushingTxn ds =>
      [[ handles_valid_map bm cm ]] *
      [[ sm_ds_valid sm ds ]] *
      GLog.would_recover_any xp ds bm hm
    | RecoveringTxn d =>
      [[ Map.Empty cm ]] *
      [[ sm_ds_valid sm (d, nil) ]] *
      GLog.rep xp (GLog.Recovering d) mm bm hm
  end)%pred.

  Definition rep xp F st ms sm bm hm :=
    (exists raw, CacheDef.rep (snd ms) raw bm *
      [[ (F * rep_inner xp st (fst ms) sm bm hm)%pred raw ]])%pred.

  Definition intact xp F ds sm bm hm :=
    (exists ms,
      rep xp F (NoTxn ds) ms sm bm hm \/
      exists new, rep xp F (ActiveTxn ds new) ms sm bm hm)%pred.

  Definition recover_any xp F ds sm bm hm :=
    (exists ms, rep xp F (FlushingTxn ds) ms sm bm hm)%pred.

Hint Resolve Forall_nil.
  
  Theorem sync_invariant_rep : forall xp F st ms sm bm hm,
    sync_invariant F ->
    sync_invariant (rep xp F st ms sm bm hm).
  Proof.
    unfold rep; destruct st; intros; eauto.
  Qed.
  Hint Resolve sync_invariant_rep.

  Theorem sync_invariant_intact : forall xp F ds sm bm hm,
    sync_invariant F ->
    sync_invariant (intact xp F ds sm bm hm).
  Proof.
    unfold intact; auto.
  Qed.

  Theorem sync_invariant_recover_any : forall xp F ds sm bm hm,
    sync_invariant F ->
    sync_invariant (recover_any xp F ds sm bm hm).
  Proof.
    unfold recover_any; auto.
  Qed.
  Hint Resolve sync_invariant_intact sync_invariant_recover_any.

  Lemma active_intact : forall xp F old new ms sm bm hm,
    rep xp F (ActiveTxn old new) ms sm bm hm =p=> intact xp F old sm bm hm.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma notxn_intact : forall xp F old ms sm bm hm,
    rep xp F (NoTxn old) ms sm bm hm =p=> intact xp F old sm bm hm.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma flushing_any : forall xp F ds ms sm bm hm,
    rep xp F (FlushingTxn ds) ms sm bm hm =p=> recover_any xp F ds sm bm hm.
  Proof.
    unfold recover_any; cancel.
  Qed.

  Lemma intact_any : forall xp F ds sm bm hm,
    intact xp F ds sm bm hm =p=> recover_any xp F ds sm bm hm.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    eauto.
    apply handles_valid_map_empty; eauto.
    apply GLog.cached_recover_any.
    eauto.
    eauto.
    eapply sm_ds_valid_pushd_r; eauto.
  Qed.

  Lemma notxn_any : forall xp F ds ms sm bm hm,
    rep xp F (NoTxn ds) ms sm bm hm =p=> recover_any xp F ds sm bm hm.
  Proof.
    unfold intact, recover_any, rep, rep_inner; cancel.
    apply GLog.cached_recover_any.
    eauto.
    apply handles_valid_map_empty; eauto.
  Qed.

  Lemma active_notxn : forall xp F old new ms sm bm hm,
    rep xp F (ActiveTxn old new) ms sm bm hm =p=>
    rep xp F (NoTxn old) (mk_mstate hmap0 (MSGLog (fst ms)), (snd ms)) sm bm hm.
  Proof.
    unfold rep, rep_inner; cancel.
    eapply sm_ds_valid_pushd_r; eauto.
  Qed.

  Lemma active_dset_match_pimpl : forall xp F ds d hm sm ms bm,
    rep xp F (ActiveTxn ds d) ms sm bm hm <=p=>
    rep xp F (ActiveTxn ds d) ms sm bm hm *
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) (extract_blocks_nested bm gms) ]].
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.

  Lemma notxn_dset_match_pimpl : forall xp F ds hm sm ms bm,
    rep xp F (NoTxn ds) ms sm bm hm <=p=>
    rep xp F (NoTxn ds) ms sm bm hm *
      [[ exists gms, GLog.dset_match xp (GLog.effective ds (length gms)) (extract_blocks_nested bm gms) ]].
  Proof.
    unfold rep, rep_inner, GLog.rep; intros; split; cancel.
    eexists; eauto.
  Qed.

  Lemma rep_inner_domainmem_subset : forall xp ms hm sm hm' bm,
    hm c= hm'
    -> forall st, rep_inner xp st ms sm bm hm
        =p=> rep_inner xp st ms sm bm hm'.
  Proof.
    intros.
    destruct st; unfold rep_inner, GLog.would_recover_any.
    cancel.
    erewrite GLog.rep_domainmem_subset; eauto.
    cancel.
    erewrite GLog.rep_domainmem_subset; eauto.
  Qed.

  Lemma Forall_public_subset_trans:
    forall A (bm bm': block_mem tagged_block) (hl: list (A * handle)),
      Forall (fun t => t = dummy_handle)
             (map fst (extract_blocks bm (map snd hl))) ->
      handles_valid_list bm hl ->
      bm c= bm' ->
      Forall (fun t => t = dummy_handle)
             (map fst (extract_blocks bm' (map snd hl))).
  Proof.
    unfold handles_valid_list; intros.
    rewrite Forall_forall in *; intros; eapply H.
    erewrite extract_blocks_subset_trans; eauto.
  Qed.
  
  Lemma rep_inner_blockmem_subset : forall xp ms hm sm bm bm',
    bm c= bm'
    -> forall st, rep_inner xp st ms sm bm hm
        =p=> rep_inner xp st ms sm bm' hm.
  Proof.
    intros.
    destruct st; unfold rep_inner, GLog.would_recover_any.
    cancel.
    erewrite GLog.rep_blockmem_subset; eauto.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; auto.
    erewrite GLog.rep_blockmem_subset; eauto.
    cancel.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    unfold map_replay.
    erewrite <- extract_blocks_map_subset_trans; eauto.
    norml. norm.
    eassign ds'; eassign n; eassign ms0; cancel.
    erewrite GLog.rep_blockmem_subset; eauto.
    intuition.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    cancel.
    erewrite GLog.rep_blockmem_subset; eauto.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; auto.
  Qed.

  Lemma rep_domainmem_subset : forall xp F ms hm sm bm hm',
    hm c= hm'
    -> forall st, rep xp F st ms sm bm hm
        =p=> rep xp F st ms sm bm hm'.
  Proof.
    unfold rep; intros; cancel.
  Qed.

  Lemma rep_blockmem_subset : forall xp F ms hm sm bm bm',
    bm c= bm'
    -> forall st, rep xp F st ms sm bm hm
        =p=> rep xp F st ms sm bm' hm.
  Proof.
    unfold rep; intros; cancel.
    erewrite CacheLemmas.block_mem_subset_rep; eauto.
    setoid_rewrite <- rep_inner_blockmem_subset; eauto.
  Qed.
  

  Lemma intact_domainmem_subset : forall xp F ds hm sm hm' bm,
    hm c= hm'
    -> intact xp F ds sm bm hm
        =p=> intact xp F ds sm bm hm'.
  Proof.
    unfold intact; intros; cancel;
    erewrite rep_domainmem_subset; eauto.
    all: cancel.
  Qed.

  Lemma rep_inner_notxn_pimpl : forall xp d ms sm hm bm,
    rep_inner xp (NoTxn (d, nil)) ms sm bm hm
    =p=> exists ms', rep_inner xp (RecoveringTxn d) ms' sm bm hm.
  Proof.
    unfold rep_inner; intros.
    rewrite GLog.cached_recovering.
    norm'l. cancel.
    eassign (mk_mstate hmap0 ms'); auto.
    simpl; eauto.
    apply map_empty_hmap0.
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
    mm <- GLog.init xp cs;;
    Ret (mk_memstate hmap0 mm).

  Definition begin (xp : log_xparams) (ms : memstate) :=
    Ret ms.

  Definition abort (xp : log_xparams) ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate hmap0 mm).

  Definition write (xp : log_xparams) a v ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate (Map.add a v cm) mm).

  Definition read xp a ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    match Map.find a cm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- GLog.read xp a mm;;
        Ret ^(mk_memstate cm mm', v)
    end.

  Definition commit xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let^ (mm', r) <- GLog.submit xp (Map.elements cm) mm;;
    If (bool_dec should_flushall true) {
      mm' <- GLog.flushall_noop xp mm';;
      Ret ^(mk_memstate hmap0 mm', r)
    } else {
      Ret ^(mk_memstate hmap0 mm', r)
    }.

  (* like abort, but use a better name for read-only transactions *)
  Definition commit_ro (xp : log_xparams) ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    Ret (mk_memstate hmap0 mm).

  Definition dwrite (xp : log_xparams) a v ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let cm' := Map.remove a cm in
    mm' <- GLog.dwrite xp a v mm;;
    Ret (mk_memstate cm' mm').

  Definition dsync xp a ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync xp a mm;;
    Ret (mk_memstate cm mm').

  Definition flushsync xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushsync xp mm;;
    Ret (mk_memstate cm mm').

  Definition flushall xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall xp mm;;
    Ret (mk_memstate cm mm').

  Definition flushsync_noop xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushsync_noop xp mm;;
    Ret (mk_memstate cm mm').

  Definition flushall_noop xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall_noop xp mm;;
    Ret (mk_memstate cm mm').

  Definition sync_cache xp ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.sync_cache xp mm;;
    Ret (mk_memstate cm mm').

  Definition recover xp cs :=
    mm <- GLog.recover xp cs;;
    Ret (mk_memstate hmap0 mm).


  Local Hint Unfold rep rep_inner map_replay: hoare_unfold.
  Arguments GLog.rep: simpl never.
  Hint Extern 0 (okToUnify (GLog.rep _ _ _ _ _) (GLog.rep _ _ _ _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; repeat match goal with
  | [ H : eq _ (mk_memstate _ _) |- _ ] =>
     inversion H; subst; simpl; clear H
  | [ |- Map.Empty hmap0 ] => apply Map.empty_1
  | [ |- map_valid hmap0 _ ] => apply map_valid_map0
  | [ H : Map.Empty ?m |- map_valid ?m _ ] => apply map_valid_empty
  end; eauto.

  Local Hint Resolve KNoDup_map_elements.
  Local Hint Resolve MapProperties.eqke_equiv.


   Lemma list2nmem_except_last:
      forall T (l: list T) x,
        (mem_except (list2nmem (l ++ [x])) (length l)) = list2nmem l.
    Proof.
      intros.
      rewrite listapp_memupd.
      rewrite <- mem_except_upd.
      apply mem_except_none.
      apply list2nmem_oob; auto.
    Qed.

  Lemma possible_crash_list2nmem_synced: forall V d' d,
    @possible_crash _ _ V d (list2nmem d') ->
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

  Local Hint Resolve sm_vs_valid_upd_synced sm_vs_valid_same_upd_synced
     vs_synced_updN_synced
     sm_ds_valid_synced sm_ds_valid_pushd_l sm_ds_valid_pushd_r
     sm_ds_valid_pushd sm_ds_valid_dsupd sm_ds_valid_pushd_latest
     sm_ds_valid_dssync list2nmem_inbound ptsto_upd'
     sm_ds_valid_dsupd_vecs sm_ds_valid_dssync_vecs.


  Definition init_ok :
    forall xp cs pr,
    {< F l d m,
    PERM:pr   
    PRE:bm, hm,
          CacheDef.rep cs d bm *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET: ms exists d sm l,
          rep xp F (NoTxn (d, nil)) ms sm bm' hm' *
          [[[ d ::: arrayN (@ptsto _ _ _) 0 d ]]] *
          [[ arrayN (@ptsto _ _ _) 0 l sm ]] * [[ length l = length d ]] *
          [[ length d = (LogHeader xp) - (DataStart xp) ]]
    XCRASH:bm_crash, hm_crash, any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    step.
    step.
    apply sm_ds_valid_synced.
    apply sm_vs_valid_disk_exact.
    apply list2nmem_array.
    apply list2nmem_array.
    autorewrite with lists. auto.
    Unshelve.
    unfold EqDec. apply handle_eq_dec.
  Qed.


  Theorem begin_ok:
    forall xp ms pr,
    {< F sm ds,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (NoTxn ds) ms sm bm hm
    POST:bm', hm', RET:r
      rep xp F (ActiveTxn ds ds!!) r sm bm' hm' *
      [[ readOnly ms r ]]
    CRASH:bm', hm',
      exists ms', rep xp F (NoTxn ds) ms' sm bm' hm'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
    eapply handles_valid_map_empty; auto.
    rewrite replay_disk_empty; auto.
    apply empty_extract_blocks_map; auto.
  Qed.


  Theorem abort_ok :
    forall xp ms pr,
    {< F ds sm m,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds m) ms sm bm hm
    POST:bm', hm', RET:r
      rep xp F (NoTxn ds) r sm bm' hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:bm', hm',
      exists ms', rep xp F (NoTxn ds) ms' sm bm' hm'
    >} abort xp ms.
  Proof.
    unfold abort.
    safestep.
    step using dems; subst; simpl.
    eapply readOnlyLL; eauto; try reflexivity; simpl; dems.
    cancel.
  Qed.

  Theorem abort_ok_weak :
    forall xp ms pr,
    {<W F ds sm m,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds m) ms sm bm hm
    POST:bm', hm', RET:r
      rep xp F (NoTxn ds) r sm bm' hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:bm', hm',
      exists ms', rep xp F (NoTxn ds) ms' sm bm' hm'
    W>} abort xp ms.
  Proof.
    unfold abort.
    weaksafestep.
    weakstep using dems; subst; simpl.
    eapply readOnlyLL; eauto; try reflexivity; simpl; dems.
    cancel.
  Qed.


  Theorem read_ok:
    forall xp ms a pr,
    {< F Fm ds sm m v,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds m) ms sm bm hm *
      [[[ m ::: Fm * a |-> v ]]]
    POST:bm', hm', RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm bm' hm' *
      [[ bm' r = Some (fst v) ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:bm', hm',
      exists ms', rep xp F (ActiveTxn ds m) ms' sm bm' hm'
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.
    cancel.
    step.
    subst.
    match goal with
    | [H: (_ * _ |-> _)%pred (list2nmem _) |- _ ] =>
      eapply list2nmem_sel in H as Hx
    end.
    eapply handles_valid_map_extract in Heqo as Hy; eauto; cleanup.
    apply map_find_elements_in in Heqo.
    erewrite replay_disk_selN_In_KNoDup in Hx.    
    2: apply extract_block_map_some; eauto.
    unfold extract_block in *.
    match goal with
    | [H: _ _ = Some _ |- _ ] =>
      rewrite H in Hx
    end.
    inversion Hx; subst; eauto.
    apply KNoDup_map_elements.
    erewrite <- replay_disk_length.
    eapply list2nmem_inbound; eauto.

    cancel.

    cancel.
    eexists; subst.
    eapply ptsto_replay_disk_not_in; eauto.
    apply MapFacts.not_find_in_iff; eauto.
    apply map_find_In_elements_none; auto.

    step.
    step.
    eapply Forall_public_subset_trans; eauto.
    match goal with
    | [H: ?x c= ?x |- _ ] =>
      clear H
    end.
    eapply handles_valid_map_subset_trans; eauto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    eassign (mk_mstate (MSTxn ms_1) ms'_1).
    intuition; pred_apply; cancel; simpl; eauto.
    simpl; eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eauto.
    erewrite mapeq_elements; eauto.
    apply extract_blocks_map_subset_trans; eauto.
 
    Unshelve.
    exact valuset0.
    unfold EqDec. apply handle_eq_dec.
  Qed.

  Lemma replay_disk_extract_blocks_map_add :
    forall a h v hmap m bm,
      bm h = Some v ->
      replay_disk (Map.elements (extract_blocks_map bm tagged_block0 (Map.add a h hmap))) m =
      updN (replay_disk (Map.elements (extract_blocks_map bm tagged_block0 hmap)) m)  a (v, []).
  Proof.
    intros.
    pose proof (map_add_extract_blocks_mem_comm _ hmap bm (a, h) v tagged_block0 H); simpl in *.
    erewrite <- mapeq_elements; eauto.
    apply replay_disk_add.
  Qed.

  Lemma in_exists_fst_snd:
      forall (A B : Type) (l : list (A * B)) (y : B),
      (exists x : A, In (x, y) l) ->
      In y (map snd l).
    Proof.
      intros; destruct H.
      apply in_fst_snd_map_split in H; intuition.
    Qed.
    
    Lemma add_forall_public:
      forall a h (bm: block_mem tagged_block) v hmap,
        Forall (fun t => t = dummy_handle)
               (map fst (extract_blocks bm (map snd (Map.elements hmap)))) ->
        handles_valid_map bm hmap ->
        bm h = Some v ->
        fst v = dummy_handle ->
        Forall (fun t => t = dummy_handle)
               (map fst (extract_blocks bm (map snd (Map.elements (Map.add a h hmap))))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      denote In as Hin; apply in_map_iff in Hin; cleanup.
      erewrite <- extract_blocks_map_extract_blocks_eq in H4; eauto.
      rewrite <- map_add_extract_blocks_mem_comm with (a:=(a, h)) in H4; eauto.
      denote In as Hin; apply in_map_iff in Hin; cleanup.
      destruct x; simpl in *.
      eapply In_InA in H4.
      apply Map.elements_2 in H4.
      destruct (Nat.eq_dec k a); subst.
      apply mapsto_add in H4; subst; auto.
      apply Map.add_3 in H4.
      rewrite Forall_forall in *.
      apply H.
      apply in_map.
      erewrite <- extract_blocks_map_extract_blocks_eq; eauto.
      eapply in_exists_fst_snd.
      exists k.
      apply InA_eqke_In.
      apply Map.elements_1; eauto.
      unfold Map.E.eq; auto.
      simpl; auto.
      eapply handles_valid_map_add; eauto.
      Unshelve.
      exact tagged_block0.
    Qed.

  Theorem write_ok :
    forall xp ms a h pr,
    {< F Fm ds m sm v vs,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds m) ms sm bm hm *
      [[ a <> 0 ]] *
      [[ bm h = Some v ]] *
      [[ fst v = dummy_handle ]] *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST:bm', hm', RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' sm bm' hm' *
      [[[ m' ::: (Fm * a |-> (v, nil)) ]]]
    CRASH:bm', hm',
      exists m' ms', rep xp F (ActiveTxn ds m') ms' sm bm' hm'
    >} write xp a h ms.
  Proof.
    unfold write.
    hoare using dems.
    eapply add_forall_public; eauto.
    eapply handles_valid_map_add; eauto.
    apply map_valid_add; eauto.
    erewrite <- replay_disk_length.
    eapply list2nmem_ptsto_bound; eauto.
    
    erewrite replay_disk_extract_blocks_map_add; eauto.
    erewrite replay_disk_extract_blocks_map_add; eauto.
    eapply list2nmem_updN. eauto.
  Qed.

  Set Regular Subst Tactic.

  Lemma remove_forall_public:
      forall a (bm: block_mem tagged_block) hmap,
        Forall (fun t => t = dummy_handle)
               (map fst (extract_blocks bm (map snd (Map.elements hmap)))) ->
        handles_valid_map bm hmap ->
        Forall (fun t => t = dummy_handle)
               (map fst (extract_blocks bm (map snd (Map.elements (Map.remove a hmap))))).
    Proof.
      intros.
      rewrite Forall_forall; intros.
      denote In as Hin; apply in_map_iff in Hin; cleanup.
      erewrite <- extract_blocks_map_extract_blocks_eq in H2; eauto.
      rewrite extract_blocks_map_remove in H2; eauto.
      denote In as Hin; apply in_map_iff in Hin; cleanup.
      destruct x; simpl in *.
      eapply In_InA in H2.
      apply Map.elements_2 in H2.
      destruct (Nat.eq_dec k a); subst.
      apply MapFacts.remove_mapsto_iff in H2; intuition.
      apply Map.remove_3 in H2.
      rewrite Forall_forall in *.
      apply H.
      apply in_map.
      erewrite <- extract_blocks_map_extract_blocks_eq; eauto.
      eapply in_exists_fst_snd.
      exists k.
      apply InA_eqke_In.
      apply Map.elements_1; eauto.
      unfold Map.E.eq; auto.
      eapply handles_valid_map_remove; eauto.
      Unshelve.
      exact tagged_block0.
    Qed.

  Theorem dwrite_ok :
    forall xp ms a h pr,
    {< F Fm Fs ds sm v vs,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm *
      [[ bm h = Some v ]] *  
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ (Fs * a |->?)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' bm' hm' *
      [[[ ds'!! ::: (Fm * a |-> (v, vsmerge vs)) ]]] *
      [[ (Fs * a |-> false)%pred sm' ]] *
      [[ ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:bm', hm',
      recover_any xp F ds sm bm' hm' \/
      recover_any xp F (dsupd ds a (v, vsmerge vs)) (Mem.upd sm a false) bm' hm'
    >} dwrite xp a h ms.
  Proof.
    unfold dwrite, recover_any.
    step.
    step.
    safestep; subst.
    eapply remove_forall_public; eauto.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_subset_trans; eauto.
    apply handles_valid_map_remove.
    match goal with
    | [H: ?x c= ?x |- _ ] =>
      clear H
    end. eapply handles_valid_map_subset_trans; eauto.
    
    eapply map_valid_remove; autorewrite with lists; eauto.
    rewrite dsupd_latest_length; auto.
    rewrite dsupd_latest.

    erewrite mapeq_elements.
    apply updN_replay_disk_remove_eq; eauto.
    match goal with
    | [H: ?x c= ?x |- _ ] =>
      clear H
    end.
    eapply MapFacts.Equal_trans.
    apply MapFacts.Equal_sym.
    apply extract_blocks_map_subset_trans; eauto.
    apply handles_valid_map_remove; auto.
    apply extract_blocks_map_remove.
    
    eapply sm_ds_valid_pushd_latest.
    apply sm_ds_valid_dsupd.
    eapply list2nmem_inbound; eauto.
    denote sm_ds_valid as Hsm;
    inversion Hsm; eauto.
         
    rewrite dsupd_latest.    
    eapply list2nmem_updN; eauto.
    eapply ptsto_upd'; eauto.
    auto.
    solve_blockmem_subset.
    (* crash conditions *)

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    or_l; cancel; xform_normr; cancel.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eauto.

    or_r; cancel.
    xform_normr; cancel.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem dsync_ok :
    forall xp ms a pr,
    {< F Fm Fs ds sm vs,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]] *
      [[ (Fs * a |->?)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' bm' hm' *
      [[ ds' = dssync ds a ]] *
      [[ (Fs * a |-> true)%pred sm' ]]
    CRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
    >} dsync xp a ms.
  Proof.
    unfold dsync, recover_any.
    step.
    step.
    safestep; subst.
    eapply Forall_public_subset_trans; eauto.
    match goal with
    | [H: ?x c= ?x |- _ ] =>
      clear H
    end. eapply handles_valid_map_subset_trans; eauto.
    rewrite dssync_latest; unfold vssync; apply map_valid_updN; auto.
    rewrite dssync_latest; substl (ds!!) at 1.
    erewrite mapeq_elements.
    apply replay_disk_vssync_comm.
    apply extract_blocks_map_subset_trans; eauto.
    all: eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem flushall_ok :
    forall xp ms pr,
    {< F sm ds,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (NoTxn ds) ms sm bm hm *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' sm bm' hm'
    XCRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
    >} flushall xp ms.
  Proof.
    unfold flushall, recover_any.
    hoare.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    eapply handles_valid_map_empty; eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem flushsync_ok :
    forall xp ms pr,
    {< F sm ds,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (NoTxn ds) ms sm bm hm *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' sm bm' hm'
    XCRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
    >} flushsync xp ms.
  Proof.
    unfold flushsync, recover_any.
    hoare.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    eapply handles_valid_map_empty; eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem flushall_noop_ok :
    forall xp ms pr,
    {< F sm ds,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (NoTxn ds) ms sm bm hm *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      rep xp F (NoTxn ds) ms' sm bm' hm'
    XCRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
    >} flushall_noop xp ms.
  Proof.
    unfold flushall_noop, recover_any.
    hoare.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    eapply handles_valid_map_empty; eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem flushsync_noop_ok :
    forall xp ms pr,
    {< F sm ds,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (NoTxn ds) ms sm bm hm *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      rep xp F (NoTxn ds) ms' sm bm' hm'
    XCRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
    >} flushsync_noop xp ms.
  Proof.
    unfold flushsync_noop, recover_any.
    hoare.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_empty; eauto.
    eapply handles_valid_map_empty; eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (flushall_noop _ _) _) => apply flushall_noop_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (flushsync_noop _ _) _) => apply flushsync_noop_ok : prog.

  Local Hint Resolve map_valid_log_valid length_elements_cardinal_gt map_empty_hmap0.

  Theorem commit_ok :
    forall xp ms pr,
    {< F sm ds m,
     PERM:pr  
     PRE:bm, hm,
          rep xp F (ActiveTxn ds m) ms sm bm hm *
          [[ sync_invariant F ]]
     POST:bm', hm', RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn (pushd m ds)) ms' sm bm' hm') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn (fst ms)) > (LogLen xp) ]] *
            rep xp F (NoTxn ds) ms' sm bm' hm')
     XCRASH:bm', hm', recover_any xp F (pushd m ds) sm bm' hm'
    >} commit xp ms.
  Proof.
    unfold commit, recover_any.
    step.
    step.
    step.
    step.
    step.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_blockmem_subset.
    solve_blockmem_subset.
    xcrash.
    unfold GLog.would_recover_any.
    cancel.
    constructor; auto.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.

    step.
    step.
    solve_hashmap_subset.

    step.
    step.
    step.
    or_l; cancel.
    erewrite <- extract_blocks_list_map; eauto.
    erewrite mapeq_elements.
    cancel.
    apply MapFacts.Equal_sym.
    apply extract_blocks_map_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_blockmem_subset.
    solve_blockmem_subset.
    xcrash.
    erewrite <- extract_blocks_list_map; eauto.
    erewrite mapeq_elements; eauto.
    apply MapFacts.Equal_sym.
    apply extract_blocks_map_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.

    step.
    step.
    or_l; cancel.
    erewrite <- extract_blocks_list_map; eauto.
    erewrite mapeq_elements.
    cancel.
    apply MapFacts.Equal_sym.
    match goal with
    | [H: ?x c= ?x |- _ ] =>
      clear H
    end.
    apply extract_blocks_map_subset_trans; eauto.
    match goal with
    | [H: ?x c= ?x |- _ ] =>
      clear H
    end. eapply handles_valid_map_subset_trans; eauto.
    solve_hashmap_subset.


    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    rewrite GLog.cached_recover_any.
    unfold GLog.would_recover_any.
    cancel.
    constructor; auto.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_map_subset_trans; eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.
 

  (* a pseudo-commit for read-only transactions *)
  Theorem commit_ro_ok :
    forall xp ms pr,
    {< F sm ds,
    PERM:pr
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm
    POST:bm', hm', RET:r
      rep xp F (NoTxn ds) r sm bm' hm' *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms r ]]
    CRASH:bm', hm',
      exists ms', rep xp F (NoTxn ds) ms' sm bm' hm'
    >} commit_ro xp ms.
  Proof.
    intros.
    eapply pimpl_ok2.
    apply abort_ok.
    safecancel.
    apply sep_star_comm.
    auto.
    step.
    rewrite <- H1; cancel.
  Qed.


  Definition after_crash xp F ds cs bm hm :=
    (exists raw, CacheDef.rep cs raw bm *
     [[ (F * GLog.recover_any_pred xp ds hm)%pred raw ]])%pred.
               

  Definition before_crash xp F ds bm hm :=
    (exists cs raw, CacheDef.rep cs raw bm *
     [[ ( exists d sm n ms, [[ n <= length (snd ds) ]] *
       F * (rep_inner xp (RecoveringTxn d) ms sm bm hm) *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.

  Theorem sync_invariant_after_crash : forall xp F ds cs bm hm,
    sync_invariant F ->
    sync_invariant (after_crash xp F ds cs bm hm).
  Proof.
    unfold after_crash; eauto.
  Qed.

  Theorem sync_invariant_before_crash : forall xp F ds bm hm,
    sync_invariant F ->
    sync_invariant (before_crash xp F ds bm hm).
  Proof.
    unfold before_crash; eauto.
  Qed.

  Hint Resolve sync_invariant_after_crash sync_invariant_before_crash.

    Lemma crash_xform_before_crash : forall xp F ds bm hm,
    crash_xform (before_crash xp F ds bm hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs empty_mem empty_mem.
  Proof.
    unfold before_crash, after_crash, rep_inner; intros.
    xform_norm.
    rewrite crash_xform_rep_pred_empty by eauto.
    norm.
    cancel.
    intuition.
    pred_apply.
    xform_norm.
    rewrite GLog.crash_xform_recovering.
    unfold GLog.recover_any_pred.
    norm. unfold stars; simpl.
    cancel.
    intuition simpl; eauto. 
    eapply crash_xform_diskIs_trans; eauto.
  Qed.

  Lemma crash_xform_any : forall xp F ds sm bm hm,
    crash_xform (recover_any xp F ds sm bm hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs empty_mem empty_mem.
  Proof.
    unfold recover_any, after_crash, rep, rep_inner; intros.
    xform_norm.
    rewrite crash_xform_rep_pred_empty by eauto.
    xform_norm.
    norm. cancel.
    intuition simpl; pred_apply; xform_norm.
    rewrite GLog.crash_xform_any.
    cancel.
  Qed.

  (*
  Lemma after_crash_notxn : forall xp cs F ds bm hm,
    after_crash xp F ds cs bm hm =p=>
      exists d n sm ms, [[ n <= length (snd ds) ]] *
      (rep xp F (NoTxn (d, nil)) ms sm bm hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
  Proof.
    unfold after_crash, recover_any, rep, rep_inner,
    GLog.recover_any_pred, GLog.rep, MLog.crash_rep, MLog.rep.
    intros. norm. cancel.
    intuition eauto.
    pred_apply; cancel; eauto.
    
    eauto.
  Qed.

  Lemma after_crash_notxn_singular : forall xp cs F d bm hm,
    after_crash xp F (d, nil) cs bm hm =p=>
      exists d' sm ms, (rep xp F (NoTxn (d', nil)) ms sm bm hm) *
      [[[ d' ::: crash_xform (diskIs (list2nmem d)) ]]].
  Proof.
    intros; rewrite after_crash_notxn; cancel.
  Qed.
  *)

  Lemma after_crash_idem : forall xp F ds cs bm hm,
    crash_xform (after_crash xp F ds cs bm hm) =p=>
     exists cs', after_crash xp (crash_xform F) ds cs' empty_mem empty_mem.
  Proof.
    unfold after_crash, rep_inner; intros.
    xform_norm.
    rewrite crash_xform_rep_pred_empty by eauto.
    xform_norm.
    denote crash_xform as Hx.
    apply crash_xform_sep_star_dist in Hx.
    norm. unfold stars; simpl. cancel.
    intuition simpl; eauto.

    autorewrite with crash_xform in Hx;
    destruct_lift Hx; pred_apply.
    rewrite GLog.recover_idem; eauto.
    Unshelve.
    all: try exact handle.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  (*
  Lemma after_crash_idem' : forall xp d ms sm bm hm (F : rawpred _),
    F (list2nmem d) ->
    crash_xform (rep_inner xp (NoTxn (d, nil)) ms sm bm hm) =p=>
    exists d' ms' sm',(rep_inner xp (NoTxn (d', nil)) ms' sm' bm hm) *
                   [[ (crash_xform F) (list2nmem d') ]].
  Proof.
    unfold rep_inner; intros.
    xform_norml.
    rewrite GLog.crash_xform_cached; cancel.
    eassign (mk_mstate hmap0 ms').
    eauto.
    simpl.
    apply Forall_nil.
    simpl; eauto.
    eapply sm_ds_valid_synced, sm_vs_valid_disk_exact.
    eapply crash_xform_diskIs_pred; eauto.
  Qed.
  *)
  
  Hint Extern 0 (okToUnify (LOG.rep_inner _ _ _ _ _ _) (LOG.rep_inner _ _ _ _ _ _)) => constructor : okToUnify.

  (* TODO: Would be better to rewrite using hashmap_subset. *)
  Instance rep_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> eq ==> eq ==> pimpl) rep.
  Proof.
    unfold Proper, respectful; intros.
    unfold rep; cancel.
    apply H0.
  Qed.

  Instance intact_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> eq ==> pimpl) intact.
  Proof.
    unfold Proper, respectful; intros.
    unfold intact; cancel; or_l.
    rewrite H0; eauto.
    rewrite active_notxn.
    rewrite H0; eauto.
  Qed.

  Instance after_crash_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> eq ==> pimpl) after_crash.
  Proof.
    unfold Proper, respectful; intros.
    unfold after_crash.
    subst. norm. cancel. intuition simpl.
    pred_apply. norm.

    cancel; eauto.
    rewrite H0; eauto.
    intuition simpl; eauto.
  Qed.

  (*
  Lemma notxn_after_crash_diskIs : forall xp F n ds d ms sm bm hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (NoTxn (d, nil)) ms sm bm hm =p=> after_crash xp F ds (snd ms) bm hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    eauto.
  Qed.
  *)
  (** idempred includes both before-crash cand after-crash cases *)
  Definition idempred xp F ds sm bm hm :=
    (recover_any xp F ds sm bm hm \/
      before_crash xp F ds bm hm \/
      exists cs, after_crash xp F ds cs bm hm)%pred.

  Theorem sync_invariant_idempred : forall xp F ds sm bm hm,
    sync_invariant F ->
    sync_invariant (idempred xp F ds sm bm hm).
  Proof.
    unfold idempred; auto.
  Qed.
  Hint Resolve sync_invariant_idempred.


  Theorem idempred_idem : forall xp F ds sm bm hm,
    crash_xform (idempred xp F ds sm bm hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs empty_mem empty_mem.
  Proof.
    unfold idempred; intros.
    xform_norm.
    rewrite crash_xform_any; cancel.
    rewrite crash_xform_before_crash; cancel.
    rewrite after_crash_idem; cancel.
  Qed.
  
  
  Theorem recover_any_idempred : forall xp F ds sm bm hm,
    recover_any xp F ds sm bm hm =p=> idempred xp F ds sm bm hm.
  Proof.
    unfold idempred; cancel.
  Qed.

  Theorem intact_idempred : forall xp F ds sm bm hm,
    intact xp F ds sm bm hm =p=> idempred xp F ds sm bm hm.
  Proof.
    intros.
    rewrite intact_any.
    apply recover_any_idempred.
  Qed.

  Theorem notxn_idempred : forall xp F ds ms sm bm hm,
    rep xp F (NoTxn ds) ms sm bm hm =p=> idempred xp F ds sm bm hm.
  Proof.
    intros.
    rewrite notxn_intact.
    apply intact_idempred.
  Qed.

  Theorem active_idempred : forall xp F ds ms d sm bm hm,
    rep xp F (ActiveTxn ds d) ms sm bm hm =p=> idempred xp F ds sm bm hm.
  Proof.
    intros.
    rewrite active_intact.
    apply intact_idempred.
  Qed.

  Theorem after_crash_idempred : forall xp F ds cs sm bm hm,
    after_crash xp F ds cs bm hm =p=> idempred xp F ds sm bm hm.
  Proof.
    unfold idempred; intros.
    or_r; cancel.
  Qed.

  Theorem before_crash_idempred : forall xp F ds sm bm hm,
    before_crash xp F ds bm hm =p=> idempred xp F ds sm bm hm.
  Proof.
    unfold idempred; intros.
    or_r; or_l; cancel.
  Qed.

  Instance idempred_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> eq ==> eq ==> pimpl) idempred.
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
    rewrite H0; cancel.
    intuition simpl; eauto.
  Qed.

  Theorem crash_xform_intact : forall xp F ds sm bm hm,
    crash_xform (intact xp F ds sm bm hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs empty_mem empty_mem.
  Proof.
    unfold intact, rep, rep_inner, after_crash; intros.
    xform_norm;
    rewrite crash_xform_rep_pred_empty by eauto;
    xform_norm;
    denote crash_xform as Hx;
    apply crash_xform_sep_star_dist in Hx;
    rewrite GLog.crash_xform_cached in Hx;
    destruct_lift Hx.

    cancel.
    cancel.
    Unshelve.
    all: try exact handle.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem crash_xform_idempred :
  forall xp F ds sm bm hm,
    crash_xform (idempred xp F ds sm bm hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs empty_mem empty_mem.
  Proof.
    apply idempred_idem.
  Qed.
  
  Theorem recover_ok:
    forall xp cs pr,
    {!< F ds,
    PERM:pr   
    PRE:bm, hm,
      after_crash xp F ds cs bm hm *
      [[ bm = empty_mem ]] *
      [[ hm = empty_mem ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      exists d sm n, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms' sm bm' hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]] *
      [[ arrayN (@ptsto _ _ _) 0 (repeat true (length d)) sm ]] *
      [[ hm' dummy_handle = Some Public ]]
    XCRASH:bm', hm',
      exists cs, after_crash xp F ds cs bm' hm'
    >!} recover xp cs.
  Proof.
    unfold recover, after_crash, before_crash, rep, rep_inner.
    safestep.
    cancel; eauto.
    eauto.

    step.
    prestep. norm. cancel.
    intuition simpl; eauto.
    pred_apply; cancel.
    eapply sm_ds_valid_synced.
    eapply sm_vs_valid_disk_synced; eauto.
    apply list2nmem_array.
    solve_hashmap_subset.

    norm'l.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    repeat xcrash_rewrite.
    xform_norm; cancel.
    xform_norm; cancel.
    xform_norm.
    norm.
    cancel.
    intuition simpl; eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Resolve active_intact flushing_any.
  Hint Extern 0 (okToUnify (intact _ _ _ _ _) (intact _ _ _ _ _)) => constructor : okToUnify.

  Hint Extern 1 ({{_|_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (begin _ _) _) => apply begin_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (abort _ _) _) => apply abort_ok : prog.
  Hint Extern 1 ({{W _|_ W}} Bind (abort _ _) _) => apply abort_ok_weak : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (commit _ _) _) => apply commit_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (commit_ro _ _) _) => apply commit_ro_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (flushall _ _) _) => apply flushall_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (flushsync _ _) _) => apply flushsync_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (recover _ _) _) => apply recover_ok : prog.


  Definition read_array xp a i ms :=
    let^ (ms, r) <- read xp (a + i) ms;;
    Ret ^(ms, r).

  Definition write_array xp a i v ms :=
    ms <- write xp (a + i) v ms;;
    Ret ms.

  Notation arrayP := (arrayN (@ptsto _ addr_eq_dec _)).

  Theorem read_array_ok :
    forall xp ms a i pr,
    {< F Fm ds m sm vs,
    PERM:pr   
    PRE:bm, hm,
          rep xp F (ActiveTxn ds m) ms sm bm hm *
          [[ i < length vs]] *
          [[[ m ::: Fm * arrayP a vs ]]]
    POST:bm', hm', RET:^(ms', r)
          rep xp F (ActiveTxn ds m) ms' sm bm' hm' *
          [[ bm' r = Some (fst (selN vs i valuset0)) ]] *
          [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:bm', hm', exists ms',
          rep xp F (ActiveTxn ds m) ms' sm bm' hm'
    >} read_array xp a i ms.
  Proof.
    unfold read_array.
    hoare.
    unfold rep_inner; cancel.
    eauto.
    subst; pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    cancel.
    solve_hashmap_subset.
    unfold rep_inner in *.
    destruct_lift H11.
    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem write_array_ok :
    forall xp a i h ms pr,
    {< F Fm ds sm m v vs,
    PERM:pr   
    PRE:bm, hm,
        rep xp F (ActiveTxn ds m) ms sm bm hm *
        [[ bm h = Some v ]] *
        [[ fst v = dummy_handle ]] *
        [[[ m ::: Fm * arrayP a vs ]]] *
        [[ i < length vs /\ a <> 0 ]]
    POST:bm', hm', RET:ms' exists m',
        rep xp F (ActiveTxn ds m') ms' sm bm' hm' *
        [[[ m' ::: Fm * arrayP a (updN vs i (v, nil)) ]]]
    CRASH:bm', hm', exists m' ms',
          rep xp F (ActiveTxn ds m') ms' sm bm' hm'
    >} write_array xp a i h ms.
  Proof.
    unfold write_array.
    prestep. norm. cancel.
    unfold rep_inner; intuition.
    pred_apply; cancel.
    eauto.
    eauto.
    eauto.
    subst; pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    cancel.

    step.
    step.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    Unshelve.
    exact valuset0.
    all: unfold EqDec; apply handle_eq_dec.
    
  Qed.

  Hint Extern 1 ({{_|_}} Bind (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write_array _ _ _ _ _) _) => apply write_array_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ ?a _ _ _) (rep _ _ _ ?a _ _ _)) => constructor : okToUnify.

  Definition read_range xp a nr ms :=
    let^ (ms, r) <- ForN i < nr
    Blockmem bm
    Hashmap hm
    Ghost [ F Fm crash ds sm m vs ms0 ]
    Loopvar [ ms pf ]
    Invariant
      rep xp F (ActiveTxn ds m) ms sm bm hm *
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ handles_valid bm pf ]] *                      
      [[ extract_blocks bm (rev pf) = firstn i (map fst vs) ]] *
      [[ (exists ms00, readOnly ms00 ms0) -> readOnly ms0 ms ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array xp a i ms;;
      Ret ^(ms, v::pf)
    Rof ^(ms, nil);;
    Ret ^(ms, rev r).


  Definition write_range xp a l ms :=
    let^ (ms) <- ForN i < length l
    Blockmem bm
    Hashmap hm
    Ghost [ F Fm crash ds sm vs ]
    Loopvar [ ms ]
    Invariant
      exists m, rep xp F (ActiveTxn ds m) ms sm bm hm *
      [[ handles_valid bm l ]] *  
      [[[ m ::: (Fm * arrayP a (vsupsyn_range vs (firstn i (extract_blocks bm l)))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i dummy_handle) ms;;
      Ret ^(ms)
    Rof ^(ms);;
    Ret ms.

  Theorem read_range_ok :
    forall xp a nr ms pr,
    {< F Fm ds sm m vs,
    PERM:pr    
    PRE:bm, hm,
      rep xp F (ActiveTxn ds m) ms sm bm hm *
      [[ nr <= length vs ]] *
      [[[ m ::: (Fm * arrayP a vs) ]]]
    POST:bm', hm', RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' sm bm' hm' *
      [[ handles_valid bm' r ]] *             
      [[ extract_blocks bm' r = firstn nr (map fst vs) ]] *
      [[ (exists ms0, readOnly ms0 ms) -> readOnly ms ms' ]]
    CRASH:bm', hm',
      exists ms', rep xp F (ActiveTxn ds m) ms' sm bm' hm'
    >} read_range xp a nr ms.
  Proof.
    unfold read_range; intros.
    safestep. auto. eauto. eauto.
    apply Forall_nil.
   
    eapply readOnly_refl; eauto.
    eauto.
    eauto.
    safestep.
    unfold rep_inner; cancel.
    subst; denote (replay_disk _ _ = replay_disk _ _) as Hx; setoid_rewrite <- Hx.
    eauto.
    eapply lt_le_trans; eauto.
    subst; denote (replay_disk _ _ = replay_disk _ _) as Hx; setoid_rewrite <- Hx.
    pred_apply; cancel.
    eauto.

    step.
    step.
    subst.
    eapply Forall_cons; unfold handle_valid; intuition eauto.
    match goal with
    | [H: ?x c= ?x |- _] =>
      clear H
    end.
    eapply handles_valid_subset_trans; eauto.
    erewrite firstn_S_selN_expand.
    rewrite extract_blocks_app; simpl.
    subst.
    match goal with
    | [H: _ _ = Some _ |- _] =>
      rewrite H
    end.
    erewrite selN_map; subst.
    erewrite <- extract_blocks_subset_trans.
    match goal with
    | [H: extract_blocks _ _ = _ |- _] =>
      rewrite H
    end; auto.
    apply handles_valid_rev_eq; auto.
    auto.
    eapply lt_le_trans; eauto.
    rewrite map_length; eapply lt_le_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1;  unfold rep_inner; cancel.
    solve_blockmem_subset.
    solve_blockmem_subset.
    
    step.
    step.
    apply handles_valid_rev_eq; auto.
    solve_hashmap_subset.
    
    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset));
    unfold false_pred; cancel.
    Unshelve.
    exact tt.
    all: eauto; try exact tagged_block0.
    all: try exact nil.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Lemma firstn_vsupsyn_range_firstn_S : forall i vs l,
    i < length l ->
    firstn i (vsupsyn_range vs (firstn (S i) l)) =
    firstn i (vsupsyn_range vs (firstn i l)).
  Proof.
    unfold vsupsyn_range; intros.
    erewrite firstn_S_selN by eauto.
    rewrite app_length; simpl.
    rewrite <- repeat_app.
    rewrite combine_app by (autorewrite with lists; auto); simpl.
    rewrite <- app_assoc.
    repeat rewrite firstn_app_l; auto.
    all: autorewrite with lists; rewrite firstn_length_l; omega.
    Unshelve. exact tagged_block0.
  Qed.

  Lemma skip_vsupsyn_range_skip_S : forall i vs l,
    i < length l -> length l <= length vs ->
    skipn (S i) (vsupsyn_range vs (firstn (S i) l)) =
    skipn (S i) (vsupsyn_range vs (firstn i l)).
  Proof.
    unfold vsupsyn_range; intros.
    setoid_rewrite skipn_selN_skipn with (def := valuset0) at 4.
    rewrite <- cons_nil_app.
    repeat rewrite skipn_app_eq;
      autorewrite with lists; repeat rewrite firstn_length_l by omega;
      simpl; auto; try omega.
    rewrite firstn_length_l.
    eapply lt_le_trans; eauto.
    omega.
  Qed.

  Lemma sep_star_reorder_helper1 : forall AT AEQ V (a b c d : @pred AT AEQ V),
    ((a * b * d) * c) =p=> (a * ((b * c) * d)).
  Proof.
    cancel.
  Qed.

  Lemma vsupsyn_range_progress : forall l a m vs,
    m < length l -> length l <= length vs ->
    arrayP a (updN (vsupsyn_range vs (firstn m l)) m (selN l m tagged_block0, nil)) =p=>
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

  Theorem write_range_ok :
    forall xp a l ms pr,
    {< F Fm ds m sm vs,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds m) ms sm bm hm *
      [[ handles_valid bm l ]] *
      [[ Forall (fun t => t = dummy_handle) (map fst (extract_blocks bm l)) ]] * 
      [[[ m ::: (Fm * arrayP a vs) ]]] *
      [[ a <> 0 /\ length l <= length vs ]]
    POST:bm', hm', RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' sm bm' hm' *
      [[[ m' ::: (Fm * arrayP a (vsupsyn_range vs (extract_blocks bm' l))) ]]]
    CRASH:bm', hm', exists ms' m',
      rep xp F (ActiveTxn ds m') ms' sm bm' hm'
    >} write_range xp a l ms.
  Proof.
    unfold write_range; intros.
    step.
    unfold vsupsyn_range; simpl.
    simpl; eauto.

    safestep.
    unfold rep_inner; cancel. eauto.
    eapply extract_blocks_selN; eauto.
    denote (Forall (fun t : handle => t = dummy_handle) (map fst (extract_blocks bm l))) as Hf;
    rewrite Forall_forall in Hf; eapply Hf.
    apply in_map.
    erewrite <- extract_blocks_subset_trans; [| |eauto]; eauto.
    apply in_selN.
    rewrite extract_blocks_length; auto.
    eauto.
    rewrite vsupsyn_range_length; auto.
    eapply lt_le_trans; eauto.
    rewrite firstn_length_l.
    eapply le_trans; [|eauto].
    apply Nat.lt_le_incl; auto.
    rewrite extract_blocks_length; auto.
    apply Nat.lt_le_incl; auto.
    eauto.

    step.
    step.
    match goal with
    | [H: ?x c= ?x |- _] =>
      clear H
    end. eapply handles_valid_subset_trans; eauto.
    erewrite vsupsyn_range_progress; simpl; eauto.
    erewrite extract_blocks_subset_trans; eauto.
    rewrite extract_blocks_length; eauto.
    rewrite extract_blocks_length; auto.
    solve_hashmap_subset.
    
    rewrite <- H1; unfold rep_inner; cancel.
    solve_blockmem_subset.
    solve_blockmem_subset.

    step.
    step.
    subst; pred_apply; cancel.
    erewrite <- extract_blocks_length; eauto.
    rewrite firstn_exact; eauto.
    solve_hashmap_subset.

    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset));
    unfold false_pred; cancel.
    
    Unshelve. exact tt.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.
  
  Hint Extern 1 ({{_|_}} Bind (read_range _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (write_range _ _ _ _) _) => apply write_range_ok : prog.


  (******** batch direct write and sync *)

  (* dwrite_vecs discard everything in active transaction *)
  Definition dwrite_vecs (xp : log_xparams) avl ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dwrite_vecs xp avl mm;;
    Ret (mk_memstate hmap0 mm').

  Definition dsync_vecs xp al ms :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync_vecs xp al mm;;
    Ret (mk_memstate cm mm').


  Lemma dwrite_ptsto_inbound : forall (F : @pred _ _ valuset) ovl avl m,
    (F * listmatch (fun v e => fst e |-> v) ovl avl)%pred (list2nmem m) ->
    Forall (fun e => (@fst _ handle) e < length m) avl.
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

  Lemma dwrite_vsupd_vecs_ok : forall avl ovl m F bm,
    (F * listmatch (fun v e => fst e |-> v) ovl avl)%pred (list2nmem m) ->
    NoDup (map fst avl) ->
    handles_valid_list bm avl ->
    (F * listmatch (fun v e => fst e |-> (snd e, vsmerge v)) ovl (extract_blocks_list bm avl))%pred (list2nmem (vsupd_vecs m (extract_blocks_list bm avl))).
  Proof.
    unfold listmatch; induction avl; destruct ovl;
    simpl; intros; eauto; destruct_lift H; inversion H3.
    inversion H0; subst.
    inversion H1; subst.
    unfold handle_valid in *; cleanup.
    erewrite extract_blocks_list_cons; simpl; eauto.
    rewrite vsupd_vecs_vsupd_notin.
    denote NoDup as Hx.
    eapply IHavl in Hx.
    2: pred_apply' H; cancel; eauto.
    erewrite (@list2nmem_sel _ _ _ a_1 (p_1, _)).
    erewrite <- vsupd_vecs_selN_not_in; eauto.
    apply sep_star_reorder_helper2.
    eapply list2nmem_updN.
    pred_apply' Hx; cancel.
    rewrite extract_blocks_list_map_fst; eauto.
    pred_apply' H; cancel.
    cancel.
    auto.
    rewrite extract_blocks_list_map_fst; auto.
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
    pred_apply' H; cancel.
  Qed.

  Lemma dsync_vssync_vecs_partial : forall al n vsl F m,
    (F * listmatch (fun vs a => a |-> vs) vsl al)%pred (list2nmem m) ->
    (F * listmatch (fun vs a => a |-> vs \/ a |=> fst vs) vsl al)%pred
        (list2nmem (vssync_vecs m (firstn n al))).
  Proof.
    unfold listmatch; induction al; destruct vsl;
    simpl; intros; eauto; destruct_lift H; inversion H1.
    rewrite firstn_nil; simpl; pred_apply' H; cancel.

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
    eapply list2nmem_updN with (y := (p_1, nil)) in H.
    pred_apply' H; repeat cancel.
  Qed.


  Lemma sm_upd_vecs_listpred_ptsto: forall a sm bm F,
    (F * listpred (fun a => (fst a) |->?) a)%pred sm ->
    handles_valid_list bm a ->                                  
    (F * listpred (fun a => (fst a) |-> false) a)%pred (sm_upd_vecs sm (extract_blocks_list bm a)).
  Proof.
    induction a; intros.
    cbn in *; auto.
    inversion H0; unfold handle_valid in *; cleanup.
    setoid_rewrite extract_blocks_list_cons; simpl; eauto.
    rewrite sm_upd_vecs_cons.
    cbn in *.
    destruct_lifts.
    eapply pimpl_apply.
    2: eapply ptsto_upd'. cancel.
    eapply pimpl_apply in H.
    eapply IHa in H.
    3: cancel.
    pred_apply' H; cancel.
    auto.
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


  Theorem dwrite_vecs_ok :
    forall xp ms avl pr,
    {< F Fs Fm ds sm ovl,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm *
      [[ handles_valid_list bm avl ]] *  
      [[[ ds!! ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]] *
      [[ (Fs * listpred (fun e => (fst e) |->?) avl)%pred sm ]] *
      [[ NoDup (map fst avl) /\ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' bm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl (extract_blocks_list bm avl) ]]] *
      [[ (Fs * listpred (fun e => (fst e) |-> false) avl)%pred sm' ]] *
      [[ ds' = (dsupd_vecs ds (extract_blocks_list bm avl)) ]]
    XCRASH:bm', hm',
      recover_any xp F ds sm bm' hm' \/
      recover_any xp F (dsupd_vecs ds (extract_blocks_list bm avl)) (sm_upd_vecs sm (extract_blocks_list bm avl)) bm' hm'
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs.
    step.
    eapply dwrite_ptsto_inbound; eauto.
    
    step.
    safestep; subst.
    apply handles_valid_map_empty.
    apply map_empty_hmap0.
    apply map_valid_map0.

    apply sm_ds_valid_pushd_latest.
    apply sm_ds_valid_dsupd_vecs; eauto.
    rewrite dsupd_vecs_latest.
    erewrite extract_blocks_list_subset_trans; eauto.
    apply dwrite_vsupd_vecs_ok; auto.
    match goal with
    | [H: ?x c= ?x |- _] =>
      clear H
    end. eapply handles_valid_list_subset_trans; eauto.
    eapply sm_upd_vecs_listpred_ptsto; eauto.
    match goal with
    | [H: ?x c= ?x |- _] =>
      clear H
    end. eapply handles_valid_list_subset_trans; eauto.
    erewrite <- extract_blocks_list_subset_trans; eauto.
    solve_blockmem_subset.
    
    (* crash conditions *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    or_l; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate hmap0 (MSGLog ms_1), x0); simpl; eauto.
    unfold rep_inner.
    pred_apply; cancel.
    apply handles_valid_map_empty; auto.
    eauto.

    or_r; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate hmap0 (MSGLog ms_1), x0); simpl; eauto.
    unfold rep_inner.
    pred_apply; cancel.
    erewrite <- extract_blocks_list_subset_trans; eauto.
    apply handles_valid_map_empty; auto.
    eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem dsync_vecs_ok :
    forall xp ms al pr,
    {< F Fs Fm ds sm vsl,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]] *
      [[ (Fs * listpred (fun a => a |->?) al)%pred sm ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' bm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl al ]]] *
      [[ (Fs * listpred (fun a => a |-> true) al)%pred sm' ]] *
      [[ ds' = dssync_vecs ds al ]]
    CRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs, recover_any.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.

    step.
    safestep; subst; try rewrite dssync_vecs_latest.
    eapply Forall_public_subset_trans; eauto.
    match goal with
    | [H: ?x c= ?x |- _] =>
      clear H
    end. eapply handles_valid_list_subset_trans; eauto.
    apply map_valid_vssync_vecs; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    erewrite <- extract_blocks_map_subset_trans; eauto.
    rewrite <- dssync_vecs_latest.
    apply sm_ds_valid_pushd_latest.
    apply sm_ds_valid_dssync_vecs.
    denote sm_ds_valid as Hsm;
    inversion Hsm; eauto.
    
    apply dsync_vssync_vecs_ok; auto.
    apply sm_sync_vecs_listpred_ptsto; eauto.
    auto.
    solve_blockmem_subset.

    rewrite <- H1; cancel.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_list_subset_trans; eauto.
    denote sm_ds_valid as Hsm;
    inversion Hsm; eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
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
  Theorem dsync_vecs_additional_ok' :
    forall xp ms al pr,
    {< F Fs Fm ds sm all synced vsl,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm *
      [[ all = al ++ synced ]] *
      [[ (Fs * listpred (fun a => a |->?) al * listpred (fun a => a |-> true) synced)%pred sm ]] *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl all ]]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' bm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl all ]]] *
      [[ (Fs * listpred (fun a => a |-> true) all)%pred sm' ]] *
      [[ ds' = dssync_vecs ds all ]]
    CRASH:sm', hm',
      recover_any xp F ds sm sm' hm'
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

    step.
    safestep; subst; try rewrite dssync_vecs_latest.
    eapply Forall_public_subset_trans; eauto.
    match goal with
    | [H: ?x c= ?x |- _] =>
      clear H
    end. eapply handles_valid_list_subset_trans; eauto.
    apply map_valid_vssync_vecs; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    erewrite <- extract_blocks_map_subset_trans; eauto.
    rewrite <- dssync_vecs_latest.
    apply sm_ds_valid_pushd_latest.
    apply sm_ds_valid_dssync_vecs.
    denote sm_ds_valid as Hsm;
    inversion Hsm; eauto.
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
    solve_blockmem_subset.

    rewrite <- H1; cancel.
    eapply Forall_public_subset_trans; eauto.
    eapply handles_valid_list_subset_trans; eauto.
    denote sm_ds_valid as Hsm;
    inversion Hsm; eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.
                    
    Lemma listmatch_nodup': forall AT AEQ V (a : list AT) (b : list V) (F : @pred AT AEQ V) m,
  (F * listmatch (fun x y => x |-> y) a b)%pred m -> NoDup a.
Proof.
  induction a; cbn; intros.
  constructor.
  destruct b; cbn in *.
  unfold listmatch in *. destruct_lifts. congruence.
  rewrite listmatch_cons in H.
  constructor.
  unfold listmatch in H.
  intro H'.
  eapply in_selN_exists in H'.
  destruct H' as [? [? Hs] ].
  destruct_lifts.
  rewrite listpred_pick in H.
  unfold pprd, prod_curry in *.
  2: eapply in_selN.
  erewrite selN_combine in H by auto.
  2: rewrite combine_length_eq; eauto.
  rewrite Hs in H.
  destruct_lifts.
  eapply ptsto_conflict_F with (a := a) (m := m).
  pred_apply. cancel.
  eapply IHa with (b := b) (m := m). pred_apply. cancel.
Unshelve.
  all: eauto.
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

  Lemma dssync_vecs_permutation: forall ds l l',
  Permutation.Permutation l l' ->
  dssync_vecs ds l = dssync_vecs ds l'.
Proof.
  intros.
  induction H; cbn; auto.
  repeat rewrite ?dssync_vecs_cons, ?dssync_vecs_dssync_comm.
  f_equal; auto.
  repeat rewrite ?dssync_vecs_cons.
  rewrite dssync_comm.
  reflexivity.
  congruence.
Qed.
  
    (* alternative spec for syncing only the unsynced subset of a list *)
  Theorem dsync_vecs_additional_ok : forall xp ms al pr,
    {< F Fs Fm ds sm all vsl sml,
    PERM:pr   
    PRE:bm, hm,
      rep xp F (ActiveTxn ds ds!!) ms sm bm hm *
      [[ (Fs * listmatch (fun b a => a |-> b) sml all)%pred sm ]] *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl all ]]] *
      [[ forall i, i < length all -> In (selN all i 0) al \/ selN sml i false = true ]] *
      [[ incl al all ]] * [[ NoDup al (* not strictly necessary, but useful *)]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds' sm',
      rep xp F (ActiveTxn ds' ds'!!) ms' sm' bm' hm' *
      [[[ ds'!! ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl all ]]] *
      [[ (Fs * listpred (fun a => a |-> true) all)%pred sm' ]] *
      [[ ds' = dssync_vecs ds all ]]
    CRASH:bm', hm',
      recover_any xp F ds sm bm' hm'
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
    safecancel.

    (* split synced from all in syncedmem *)
    eauto.
    cancel.
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
    apply Nat.eqb_eq.
    rewrite split_length_l.
    rewrite sort_by_index_length; auto.
    intros. eapply in_combine_ex_l; eauto; omega.

    (* split unsynced from all on disk *)
    unfold listmatch.
    rewrite listpred_permutation.
    eassign Fm; cancel. (* solve [reflexivity]. *)
    shelve.
    rewrite combine_app.
    erewrite partition_permutation_app.
    rewrite partition_eq_filter.
    cbn [fst snd].
    apply Permutation.Permutation_app.
    rewrite <- filter_elements_permutation with (a := al); auto.
    rewrite sort_by_index_combine; auto.
    apply Nat.eqb_eq.
    rewrite map_snd_combine; auto.
    intros.
    eapply in_combine_ex_l; auto; omega.
    rewrite <- filter_r; auto.
    rewrite split_length_l.
    rewrite sort_by_index_length; auto.
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
    apply Nat.eqb_eq.
    rewrite map_snd_combine; auto.
    intros.
    eapply in_combine_ex_l; auto.
    match goal with
    | [H: ?x = _ |- ?x >= _ ] =>
      setoid_rewrite H
    end; omega.
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
    eauto.
    rewrite split_length_l.
    rewrite sort_by_index_length; auto.
  Unshelve.
    all: solve [exact 0 | exact (tagged_block0, [])].
  Qed.


  Hint Extern 1 ({{_|_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


  Lemma idempred_domainmem_subset : forall xp F ds sm hm hm' bm,
    hm c= hm'
    -> idempred xp F ds sm bm hm
       =p=> idempred xp F ds sm bm hm'.
  Proof.
    unfold idempred, recover_any, after_crash, before_crash; safecancel.
    rewrite rep_domainmem_subset by eauto.
    or_l; cancel.
  Qed.

  Lemma notxn_after_crash_diskIs : forall xp F n ds d x bm hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    after_crash xp F (d, nil) x bm hm =p=> after_crash xp F ds x bm hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel.
    unfold GLog.recover_any_pred.
    safecancel.
    eauto.
    inversion H2; subst; try omega.
    rewrite nthd_0 in *; simpl in *.
    eapply crash_xform_diskIs_trans; eauto.
  Qed.

  Lemma crash_xform_intact_dssync_vecs_idempred : forall xp F sm ds al hm bm,
    crash_xform (LOG.intact xp F (dssync_vecs ds al) sm bm hm) =p=>
    LOG.idempred xp (crash_xform F) ds sm empty_mem empty_mem.
  Proof.
    intros.
    rewrite crash_xform_intact.
    xform_norm.
    unfold idempred, after_crash, GLog.recover_any_pred.
    or_r; or_r. norm. cancel.
    intuition simpl.
    pred_apply; safecancel.
    rewrite map_length in *; eauto.
    rewrite dssync_vecs_nthd.
    rewrite crash_xform_diskIs_vssync_vecs; eauto.    
  Qed.


  Lemma crash_xform_cached_before: forall fsxp F d hm ms ds sm n bm,
    n <= length (snd ds) ->
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    crash_xform (rep (FSXPLog fsxp) F (LOG.NoTxn (d, [])) ms sm bm hm)
        =p=> crash_xform (before_crash (FSXPLog fsxp) F ds bm hm).
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
