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
Require Import NEList.
Require Import RelationClasses.
Require Import Morphisms.


Import ListNotations.

Set Implicit Arguments.


Module LOG.

  Import AddrMap LogReplay.

  Record mstate := mk_mstate {
    MSTxn   : valumap;         (* memory state for active txns *)
    MSGLog  : GLog.mstate    (* lower-level state *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate mm (ll : GLog.memstate) : memstate := 
    (mk_mstate mm (fst ll), (snd ll)).

  Definition MSCache (ms : memstate) := snd ms.
  Definition MSLL (ms : memstate) : GLog.memstate := (MSGLog (fst ms), (snd ms)).


  Inductive state :=
  | NoTxn (cur : GLog.diskset)
  (* No active transaction, MemLog.Synced or MemLog.Applying *)

  | ActiveTxn (old : GLog.diskset) (cur : diskstate)
  (* A transaction is in progress.
   * It started from the first memory and has evolved into the second.
   *)

  | FlushingTxn (new : GLog.diskset)
  (* A flushing is in progress
   *)
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

  Lemma active_notxn : forall xp F old new ms hm,
    rep xp F (ActiveTxn old new) ms hm =p=>
    rep xp F (NoTxn old) (mk_mstate vmap0 (MSGLog (fst ms)), (snd ms)) hm.
  Proof.
    unfold rep, rep_inner; cancel.
  Qed.

  Lemma rep_hashmap_subset : forall xp F ms hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp F st ms hm
        =p=> rep xp F st ms hm'.
  Proof. Admitted.

  Definition init T xp cs rx : prog T :=
    mm <- GLog.init xp cs;
    rx (mk_memstate vmap0 mm).

  Definition begin T (xp : log_xparams) ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    rx (mk_memstate vmap0 mm).

  Definition abort T (xp : log_xparams) ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    rx (mk_memstate vmap0 mm).

  Definition write T (xp : log_xparams) a v ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    rx (mk_memstate (Map.add a v cm) mm).

  Definition read T xp a ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    match Map.find a cm with
    | Some v =>  rx ^(ms, v)
    | None =>
        let^ (mm', v) <- GLog.read xp a mm;
        rx ^(mk_memstate cm mm', v)
    end.

  Definition commit T xp ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let^ (mm', r) <- GLog.submit xp (Map.elements cm) mm;
    rx ^(mk_memstate vmap0 mm', r).

  (* like abort, but use a better name for read-only transactions *)
  Definition commit_ro T (xp : log_xparams) ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    rx (mk_memstate vmap0 mm).

  Definition dwrite T (xp : log_xparams) a v ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    let cm' := Map.remove a cm in
    mm' <- GLog.dwrite xp a v mm;
    rx (mk_memstate cm' mm').

  Definition dsync T xp a ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync xp a mm;
    rx (mk_memstate cm mm').

  Definition sync T xp ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.flushall xp mm;
    rx (mk_memstate cm mm').

  Definition recover T xp cs rx : prog T :=
    mm <- GLog.recover xp cs;
    rx (mk_memstate vmap0 mm).


  Local Hint Unfold rep rep_inner map_replay: hoare_unfold.
  Arguments GLog.rep: simpl never.
  Hint Extern 0 (okToUnify (GLog.rep _ _ _ _) (GLog.rep _ _ _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; repeat match goal with
  | [ H : eq _ (mk_memstate _ _) |- _ ] =>
     inversion H; subst; simpl; clear H
  | [ |- Map.Empty vmap0 ] => apply Map.empty_1
  | [ |- map_valid vmap0 _ ] => apply map_valid_map0
  end; eauto.

  Local Hint Resolve KNoDup_map_elements.
  Local Hint Resolve MapProperties.eqke_equiv.


  Theorem begin_ok: forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm
    POST:hm' RET:r
      rep xp F (ActiveTxn ds ds!!) r hm'
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' hm'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
    pred_apply; cancel; dems.
  Qed.


  Theorem abort_ok : forall xp ms,
    {< F ds m,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r hm'
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' hm'
    >} abort xp ms.
  Proof.
    unfold abort.
    safestep.
    step using dems; subst; simpl.
    pred_apply; cancel.
    pimpl_crash; norm. cancel.
    eassign (mk_mstate vmap0 (MSGLog m0)).
    intuition; pred_apply; cancel.
  Qed.


  Theorem read_ok: forall xp ms a,
    {< F Fm ds m v,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: Fm * a |-> v ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' hm' * [[ r = fst v ]]
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
    eassign (mk_mstate (MSTxn m0) m1).
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
      [[[ ds!! ::: (Fm * a |-> vs) ]]]
    POST:hm' RET:ms' exists m,
      rep xp F (ActiveTxn (m, nil) m) ms' hm' *
      [[[ m ::: (Fm * a |-> (v, vsmerge vs)) ]]]
    XCRASH:hm'
      recover_any xp F ds hm' \/
      exists ms' m',
      rep xp F (ActiveTxn (m', nil) m') ms' hm' *
          [[[ m' ::: (Fm * a |-> (v, vsmerge vs)) ]]]
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite, recover_any.
    step.
    step; subst.

    eapply map_valid_remove; autorewrite with lists; eauto.
    setoid_rewrite singular_latest at 2; simpl; auto.
    rewrite length_updN; auto.

    apply updN_replay_disk_remove_eq; eauto.

    (* crash conditions *)
    xcrash.
    or_l; cancel; xform_normr; cancel.
    or_r; cancel; xform_normr; cancel.
    xform_normr; cancel.
    eassign (mk_mstate (Map.remove a (MSTxn m)) m0); eauto.
    eapply map_valid_remove; autorewrite with lists; eauto.
    setoid_rewrite singular_latest at 2; simpl; auto.
    rewrite length_updN; auto.
    apply updN_replay_disk_remove_eq; eauto.
    eauto.

    Unshelve. eauto.
  Qed.


  Theorem dsync_ok : forall xp ms a,
    {< F Fm ds vs,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm *
      [[[ ds!! ::: (Fm * a |-> vs) ]]]
    POST:hm' RET:ms' exists m,
      rep xp F (ActiveTxn (m, nil) m) ms' hm' *
      [[[ m ::: (Fm * a |-> (fst vs, nil)) ]]]
    XCRASH:hm'
      recover_any xp F ds hm'
    >} dsync xp a ms.
  Proof.
    unfold dsync, recover_any.
    step.
    step; subst.
    apply map_valid_updN; auto.
    setoid_rewrite singular_latest at 2; simpl; auto.
    rewrite <- replay_disk_vssync_comm.
    substl ds!! at 1; auto.

    (* crashes *)
    xcrash.
    Unshelve. eauto.
  Qed.


  Theorem sync_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (NoTxn ds) ms hm
    POST:hm' RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms' hm'
    CRASH:hm'
      recover_any xp F ds hm'
    >} sync xp ms.
  Proof.
    unfold sync, recover_any.
    hoare.
    Unshelve. eauto.
  Qed.


  Local Hint Resolve map_valid_log_valid length_elements_cardinal_gt map_empty_vmap0.

  Theorem commit_ok : forall xp ms,
    {< F ds m,
     PRE:hm  rep xp F (ActiveTxn ds m) ms hm
     POST:hm' RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn (pushd m ds)) ms' hm') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn (fst ms)) > (LogLen xp) ]] *
            rep xp F (NoTxn ds) ms' hm')
     CRASH:hm' exists ms', rep xp F (NoTxn ds) ms' hm'
    >} commit xp ms.
  Proof.
    unfold commit.
    step.
    step.

    eassign (mk_mstate vmap0 m).
    step.
    auto.
  Qed.


  (* a pseudo-commit for read-only transactions *)
  Theorem commit_ro_ok : forall xp ms,
    {< F ds,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm
    POST:hm' RET:r
      rep xp F (NoTxn ds) r hm'
    CRASH:hm'
      exists ms', rep xp F (NoTxn ds) ms' hm'
    >} commit_ro xp ms.
  Proof.
    intros.
    eapply pimpl_ok2.
    apply abort_ok.
    cancel.
    apply sep_star_comm.
  Qed.


  Definition after_crash xp F ds cs hm :=
    (exists raw, BUFCACHE.rep cs raw *
     [[ ( exists d n ms, [[ n <= length (snd ds) ]] *
       F * rep_inner xp (NoTxn (d, nil)) ms hm *
       [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
     )%pred raw ]])%pred.


  Theorem recover_ok: forall xp cs,
    {< F ds,
    PRE:hm
      after_crash xp F ds cs hm
    POST:hm' RET:ms' 
      exists d n, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms' hm' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    CRASH:hm' exists cs',
      after_crash xp F ds cs' hm'
    >} recover xp cs.
  Proof.
    unfold recover, after_crash, rep, rep_inner.
    safestep.
    unfold GLog.recover_any_pred. norm. cancel.
    intuition simpl; eauto.

    prestep. norm. cancel.
    intuition simpl; eauto.
    pred_apply; cancel.

    pimpl_crash. norm. cancel.
    intuition simpl; eauto; pred_apply.
    norm. cancel.
    intuition simpl; eauto.
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
  Qed.


  Lemma after_crash_notxn : forall xp cs F ds hm,
    after_crash xp F ds cs hm =p=>
      exists d n ms, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms hm *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]].
  Proof.
    unfold after_crash, recover_any, rep, rep_inner.
    intros. norm. cancel.
    intuition simpl. eassumption.
    eassign (mk_mstate vmap0 (MSGLog dummy1)).
    pred_apply; cancel.
    auto.
  Qed.


  Lemma after_crash_notxn_singular : forall xp cs F d hm,
    after_crash xp F (d, nil) cs hm =p=>
      exists d' ms, rep xp F (NoTxn (d', nil)) ms hm *
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
    rewrite GLog.crash_xform_cached in Hx.
    destruct_lift Hx.

    norm. cancel. intuition; pred_apply.
    norm. cancel.
    eassign (mk_mstate vmap0 dummy3); cancel.
    intuition simpl; eauto.
    pred_apply.
    eapply crash_xform_diskIs_trans; eauto.
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
    pred_apply. norm. cancel.
    rewrite H0; eauto. intuition simpl; eauto.
  Qed.

  Lemma notxn_after_crash_diskIs : forall xp F n ds d ms hm,
    crash_xform (diskIs (list2nmem (nthd n ds))) (list2nmem d) ->
    n <= length (snd ds) ->
    rep xp F (NoTxn (d, nil)) ms hm =p=> after_crash xp F ds (snd ms) hm.
  Proof.
    unfold rep, after_crash, rep_inner; intros.
    safecancel; auto.
  Qed.

  (** idempred includes both before-crash cand after-crash cases *)
  Definition idempred xp F ds hm :=
    (recover_any xp F ds hm \/ exists cs, after_crash xp F ds cs hm)%pred.

  Theorem idempred_idem : forall xp F ds hm,
    crash_xform (idempred xp F ds hm) =p=>
      exists cs, after_crash xp (crash_xform F) ds cs hm.
  Proof.
    unfold idempred; intros.
    xform_norm.
    rewrite crash_xform_any; cancel.
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

  Instance idempred_proper_iff :
    Proper (eq ==> piff ==> eq ==> eq ==> pimpl) idempred.
  Proof.
    unfold Proper, respectful; intros.
    unfold idempred; cancel.
    unfold recover_any, rep; or_l; cancel.
    rewrite H0; auto.
    or_r; cancel.
    rewrite H0; eauto.
  Qed.

  Theorem crash_xform_intact : forall xp F ds hm,
    crash_xform (intact xp F ds hm) =p=>
      exists ms d, rep xp (crash_xform F) (NoTxn (d, nil)) ms hm *
        [[[ d ::: crash_xform (diskIs (list2nmem (fst ds))) ]]].
  Proof.
    unfold intact, rep, rep_inner; intros.
    xform_norm;
    rewrite BUFCACHE.crash_xform_rep_pred by eauto;
    xform_norm;
    denote crash_xform as Hx;
    apply crash_xform_sep_star_dist in Hx;
    rewrite GLog.crash_xform_cached in Hx;
    destruct_lift Hx.

    cancel.
    eassign (mk_mstate (MSTxn m) dummy0).
    cancel. auto. auto.

    cancel.
    eassign (mk_mstate vmap0 dummy0).
    cancel. auto. auto.
  Qed.


  Hint Resolve active_intact flushing_any.
  Hint Extern 0 (okToUnify (intact _ _ _ _) (intact _ _ _ _)) => constructor : okToUnify.


  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.
  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.
  Hint Extern 1 ({{_}} progseq (commit_ro _ _) _) => apply commit_ro_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.


  Definition read_array T xp a i ms rx : prog T :=
    let^ (ms, r) <- read xp (a + i) ms;
    rx ^(ms, r).

  Definition write_array T xp a i v ms rx : prog T :=
    ms <- write xp (a + i) v ms;
    rx ms.


  Theorem read_array_ok : forall xp ms a i,
    {< F Fm ds m vs,
    PRE:hm   rep xp F (ActiveTxn ds m) ms hm *
          [[ i < length vs]] *
          [[[ m ::: Fm * arrayN a vs ]]]
    POST:hm' RET:^(ms', r)
          rep xp F (ActiveTxn ds m) ms' hm' *
          [[ r = fst (selN vs i ($0, nil)) ]]
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
          [[ i < length vs /\ a <> 0 ]] *
          [[[ m ::: Fm * arrayN a vs ]]]
    POST:hm' RET:ms' exists m',
          rep xp F (ActiveTxn ds m') ms' hm' *
          [[[ m' ::: Fm * arrayN a (updN vs i (v, nil)) ]]]
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
    subst; pred_apply.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _) _) => apply write_array_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ ?a _) (rep _ _ _ ?a _)) => constructor : okToUnify.

  Definition read_range T A xp a nr (vfold : A -> valu -> A) v0 ms rx : prog T :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds m vs ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayN a vs) ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) v0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array xp a i ms;
      lrx ^(ms, vfold pf v)
    Rof ^(ms, v0);
    rx ^(ms, r).


  Definition write_range T xp a l ms rx : prog T :=
    let^ (ms) <- ForN i < length l
    Hashmap hm
    Ghost [ F Fm crash ds vs ]
    Loopvar [ ms ]
    Continuation lrx
    Invariant
      exists m, rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayN a (vsupsyn_range vs (firstn i l))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i $0) ms;
      lrx ^(ms)
    Rof ^(ms);
    rx ms.


  Theorem read_range_ok : forall A xp a nr vfold (v0 : A) ms,
    {< F Fm ds m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[ nr <= length vs ]] *
      [[[ m ::: (Fm * arrayN a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' hm' *
      [[ r = fold_left vfold (firstn nr (map fst vs)) v0 ]]
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' hm'
    >} read_range xp a nr vfold v0 ms.
  Proof.
    unfold read_range; intros.
    safestep. auto.
    subst; pred_apply; cancel.

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
    eauto.
    Unshelve. exact tt.
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

  Lemma vsupsyn_range_progress : forall F l a m vs d,
    m < length l -> length l <= length vs ->
    (F ✶ arrayN a (vsupsyn_range vs (firstn m l)))%pred (list2nmem d) ->
    (F ✶ arrayN a (vsupsyn_range vs (firstn (S m) l)))%pred 
        (list2nmem (updN d (a + m) (selN l m $0, nil))).
  Proof.
    intros.
    rewrite arrayN_isolate with (i := m) (default := ($0, nil)).
    apply sep_star_reorder_helper1.
    rewrite vsupsyn_range_selN.
    rewrite selN_firstn by auto.
    eapply list2nmem_updN.
    pred_apply.
    rewrite arrayN_isolate with (i := m) (default := ($0, nil)).
    rewrite firstn_vsupsyn_range_firstn_S by auto.
    rewrite skip_vsupsyn_range_skip_S by auto.
    cancel.
    all: try rewrite vsupsyn_range_length; try rewrite firstn_length_l; omega.
  Qed.

  Lemma write_range_length_ok : forall F a i ms d vs,
    i < length vs ->
    (F ✶ arrayN a vs)%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
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
      [[ a <> 0 /\ length l <= length vs ]] *
      [[[ m ::: (Fm * arrayN a vs) ]]]
    POST:hm' RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' hm' *
      [[[ m' ::: (Fm * arrayN a (vsupsyn_range vs l)) ]]]
    CRASH:hm' exists ms' m',
      rep xp F (ActiveTxn ds m') ms' hm'
    >} write_range xp a l ms.
  Proof.
    unfold write_range; intros.
    step.
    subst; pred_apply; cancel.

    step.
    apply map_valid_add; auto; try omega.
    eapply write_range_length_ok; eauto; omega.

    subst; rewrite replay_disk_add.
    apply vsupsyn_range_progress; auto.

    step.
    subst; pred_apply.
    erewrite firstn_oob; eauto.
    Unshelve. exact tt.
  Qed.


  (* like read_range, but stops when cond is true *)
  Definition read_cond T A xp a nr (vfold : A -> valu -> A) v0 (cond : A -> bool) ms rx : prog T :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ F Fm crash ds m vs ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      rep xp F (ActiveTxn ds m) ms hm *
      [[[ m ::: (Fm * arrayN a vs) ]]] * [[ cond pf = false ]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) v0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array xp a i ms;
      let pf' := vfold pf v in
      If (bool_dec (cond pf') true) {
        rx ^(ms, Some pf')
      } else {
        lrx ^(ms, pf')
      }
    Rof ^(ms, v0);
    rx ^(ms, None).


  Theorem read_cond_ok : forall A xp a nr vfold (v0 : A) cond ms,
    {< F Fm ds m vs,
    PRE:hm
      rep xp F (ActiveTxn ds m) ms hm *
      [[ nr <= length vs /\ cond v0 = false ]] *
      [[[ m ::: (Fm * arrayN a vs) ]]]
    POST:hm' RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' hm' *
      ( exists v, [[ r = Some v /\ cond v = true ]] \/
      [[ r = None /\ cond (fold_left vfold (firstn nr (map fst vs)) v0) = false ]])
    CRASH:hm'
      exists ms', rep xp F (ActiveTxn ds m) ms' hm'
    >} read_cond xp a nr vfold v0 cond ms.
  Proof.
    unfold read_cond; intros.
    hoare.

    subst; pred_apply; cancel.
    eapply lt_le_trans; eauto.
    subst; denote (Map.elements (MSTxn a0)) as Hx; rewrite <- Hx.
    pred_apply; cancel.
    cancel.
    apply not_true_is_false; auto.

    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; subst; auto.
    rewrite map_length; omega.

    Unshelve. exact tt. eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_cond _ _ _ _ _ _ _) _) => apply read_cond_ok : prog.
  Hint Extern 1 ({{_}} progseq (read_range _ _ _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_range _ _ _ _) _) => apply write_range_ok : prog.


  (******** batch direct write and sync *)

  (* dwrite_vecs discard everything in active transaction *)
  Definition dwrite_vecs T (xp : log_xparams) avl ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dwrite_vecs xp avl mm;
    rx (mk_memstate vmap0 mm').

  Definition dsync_vecs T xp al ms rx : prog T :=
    let '(cm, mm) := (MSTxn (fst ms), MSLL ms) in
    mm' <- GLog.dsync_vecs xp al mm;
    rx (mk_memstate cm mm').


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
    erewrite (@list2nmem_sel _ _ m n (p_cur, _)) by (pred_apply; cancel).
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
      [[ NoDup (map fst avl) ]] *
      [[[ ds!! ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]]
    POST:hm' RET:ms' exists m',
      rep xp F (ActiveTxn (m', nil) m') ms' hm' *
      [[[ m' ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]]
    XCRASH:hm'
      recover_any xp F ds hm' \/
      exists ms' m',
      rep xp F (ActiveTxn (m', nil) m') ms' hm' *
      [[[ m' ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]]
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs.
    step.
    eapply dwrite_ptsto_inbound; eauto.

    step; subst.
    apply map_valid_map0.
    apply dwrite_vsupd_vecs_ok; auto.

    (* crash conditions *)
    xcrash.
    or_l; unfold recover_any, rep; cancel.
    xform_normr; cancel.
    eassign x; eassign (mk_mstate vmap0 (MSGLog m), x0); simpl; eauto.
    pred_apply; cancel.

    or_r; cancel.
    xform_normr; cancel.
    xform_normr; cancel.
    eassign (mk_mstate vmap0 m0); eauto.
    simpl; apply map_valid_map0. eauto.
    apply dwrite_vsupd_vecs_ok; eauto.
  Qed.


  Theorem dsync_vecs_ok : forall xp ms al,
    {< F Fm ds vsl,
    PRE:hm
      rep xp F (ActiveTxn ds ds!!) ms hm *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]]
    POST:hm' RET:ms' exists m',
      rep xp F (ActiveTxn (m', nil) m') ms' hm' *
      [[[ m' ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl al ]]]
    XCRASH:hm'
      recover_any xp F ds hm'
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs, recover_any.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.

    step; subst.
    apply map_valid_vssync_vecs; auto.
    setoid_rewrite singular_latest at 2; simpl; auto.
    rewrite <- replay_disk_vssync_vecs_comm.
    f_equal; auto.
    apply dsync_vssync_vecs_ok; auto.

    (* crashes *)
    xcrash.
    Unshelve. eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


End LOG.


(* rewrite rules for recover_either_pred *)




Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.commit.
Global Opaque LOG.commit_ro.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
