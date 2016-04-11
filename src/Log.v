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

Import ListNotations.

Set Implicit Arguments.


Module LOG.

  Import AddrMap LogReplay.

  Record memstate := mk_memstate {
    MSTxn   : valumap;         (* memory state for active txns *)
    MSMem   : GLog.memstate    (* lower-level state *)
  }.

  Inductive state :=
  | NoTxn (cur : GLog.diskset)
  (* No active transaction, MemLog.Synced or MemLog.Applying *)

  | ActiveTxn (old : GLog.diskset) (cur : diskstate)
  (* A transaction is in progress.
   * It started from the first memory and has evolved into the second.
   *)

  | FlushingTxn (new : GLog.diskset) (n : addr)
  (* A flushing is in progress
   *)
  .

  Definition rep xp F st ms :=
  let '(cm, mm) := (MSTxn ms, MSMem ms) in
  (match st with
    | NoTxn ds =>
      [[ Map.Empty cm ]] *
      GLog.rep xp F (GLog.Cached ds) mm
    | ActiveTxn ds cur =>
      [[ map_valid cm ds!! ]] *
      [[ map_replay cm ds!! cur ]] *
      GLog.rep xp F (GLog.Cached ds) mm
    | FlushingTxn ds n =>
      GLog.would_recover_any xp F n ds
  end)%pred.

  Definition memstate0 mm cs :=
    mk_memstate vmap0 (GLog.mk_memstate vmap0 nil (MLog.mk_memstate mm cs)).

  Definition intact xp F ds :=
    (exists ms,
      rep xp F (NoTxn ds) ms \/
      exists new, rep xp F (ActiveTxn ds new) ms)%pred.

  Definition recover_any xp F n ds :=
    (exists ms, rep xp F (FlushingTxn ds n) ms)%pred.

  Lemma active_intact : forall xp F old new ms,
    rep xp F (ActiveTxn old new) ms =p=> intact xp F old.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma notxn_intact : forall xp F old ms,
    rep xp F (NoTxn old) ms =p=> intact xp F old.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma flushing_any : forall xp F ds n ms,
    rep xp F (FlushingTxn ds n) ms =p=> recover_any xp F n ds.
  Proof.
    unfold recover_any; cancel.
  Qed.

  Lemma intact_any : forall xp F ds,
    intact xp F ds =p=> recover_any xp F 0 ds.
  Proof.
    unfold intact, recover_any, rep; cancel.
    apply GLog.cached_recover_any.
    apply GLog.cached_recover_any.
    Unshelve. all: eauto.
  Qed.

  Lemma active_notxn : forall xp F old new ms,
    rep xp F (ActiveTxn old new) ms =p=>
    rep xp F (NoTxn old) (mk_memstate vmap0 (MSMem ms)).
  Proof.
    unfold rep; cancel.
  Qed.


  Definition begin T (xp : log_xparams) ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    rx (mk_memstate vmap0 mm).

  Definition abort T (xp : log_xparams) ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    rx (mk_memstate vmap0 mm).

  Definition write T (xp : log_xparams) a v ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    rx (mk_memstate (Map.add a v cm) mm).

  Definition read T xp a ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    match Map.find a cm with
    | Some v =>  rx ^(ms, v)
    | None =>
        let^ (mm', v) <- GLog.read xp a mm;
        rx ^(mk_memstate cm mm', v)
    end.

  Definition read_raw T a ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    let^ (mm', r) <- GLog.read_raw a mm;
    rx ^(mk_memstate cm mm', r).

  Definition commit T xp ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    let^ (mm', r) <- GLog.submit xp (Map.elements cm) mm;
    rx ^(mk_memstate vmap0 mm', r).

  (* like abort, but use a better name for read-only transactions *)
  Definition commit_ro T (xp : log_xparams) ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    rx (mk_memstate vmap0 mm).

  Definition dwrite T (xp : log_xparams) a v ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    let cm' := Map.remove a cm in
    mm' <- GLog.dwrite xp a v mm;
    rx (mk_memstate cm' mm').

  Definition dsync T xp a ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    mm' <- GLog.dsync xp a mm;
    rx (mk_memstate cm mm').

  Definition sync T xp ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    mm' <- GLog.flushall xp mm;
    rx (mk_memstate cm mm').

  Definition recover T xp cs rx : prog T :=
    mm <- GLog.recover xp cs;
    rx (mk_memstate vmap0 mm).


  Local Hint Unfold rep map_replay: hoare_unfold.
  Arguments GLog.rep: simpl never.
  Hint Extern 0 (okToUnify (GLog.rep _ _ _ _) (GLog.rep _ _ _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; repeat match goal with
  | [ H : @eq memstate ?ms (mk_memstate _ _) |- _ ] =>
     is_var ms; destruct ms; inversion H; subst; simpl
  | [ |- Map.Empty vmap0 ] => apply Map.empty_1
  | [ |- map_valid vmap0 _ ] => apply map_valid_map0
  end; eauto.

  Hint Resolve KNoDup_map_elements.
  Hint Resolve MapProperties.eqke_equiv.


  Theorem read_raw_ok: forall xp ms a,
    {< F d vs,
    PRE
      rep xp (F * a |-> vs) (NoTxn d) ms
    POST RET:^(ms', r)
      rep xp (F * a |-> vs) (NoTxn d) ms' * [[ r = fst vs ]]
    CRASH
      exists ms', rep xp (F * a |-> vs) (NoTxn d) ms'
    >} read_raw a ms.
  Proof.
    unfold read_raw, rep.
    safestep.
    step.
    pimpl_crash; cancel.
    eassign (mk_memstate (MSTxn ms) ms'); simpl; eauto.
    simpl; auto.
  Qed.

  Theorem begin_ok: forall xp ms,
    {< F ds,
    PRE
      rep xp F (NoTxn ds) ms
    POST RET:r
      rep xp F (ActiveTxn ds ds!!) r
    CRASH
      exists ms', rep xp F (NoTxn ds) ms'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
  Qed.


  Theorem abort_ok : forall xp ms,
    {< F ds m,
    PRE
      rep xp F (ActiveTxn ds m) ms
    POST RET:r
      rep xp F (NoTxn ds) r
    CRASH
      exists ms', rep xp F (NoTxn ds) ms'
    >} abort xp ms.
  Proof.
    unfold abort.
    safestep.
    step; subst; simpl.
    apply Map.empty_1.
    pimpl_crash; norm.
    eassign (mk_memstate vmap0 (MSMem ms)); cancel.
    intuition.
  Qed.


  Theorem read_ok: forall xp ms a,
    {< F Fm ds m v,
    PRE
      rep xp F (ActiveTxn ds m) ms *
      [[[ m ::: Fm * a |-> v ]]]
    POST RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' * [[ r = fst v ]]
    CRASH
      exists ms', rep xp F (ActiveTxn ds m) ms'
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

    pimpl_crash; norm.
    eassign (mk_memstate (MSTxn ms) ms').
    cancel. intuition.
  Qed.


  Theorem write_ok : forall xp ms a v,
    {< F Fm ds m vs,
    PRE
      rep xp F (ActiveTxn ds m) ms * [[ a <> 0 ]] *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' *
      [[[ m' ::: (Fm * a |-> (v, nil)) ]]]
    CRASH
      exists m' ms', rep xp F (ActiveTxn ds m') ms'
    >} write xp a v ms.
  Proof.
    unfold write.
    hoare using dems.

    apply map_valid_add; eauto.
    erewrite <- replay_disk_length.
    eapply list2nmem_ptsto_bound; eauto.

    rewrite replay_disk_add.
    eapply list2nmem_updN; eauto.
  Qed.


  Set Regular Subst Tactic.

  Theorem dwrite_ok : forall xp ms a v,
    {< F Fm ds vs,
    PRE
      rep xp F (ActiveTxn ds ds!!) ms *
      [[[ ds!! ::: (Fm * a |-> vs) ]]]
    POST RET:ms' exists m,
      rep xp F (ActiveTxn (m, nil) m) ms' *
      [[[ m ::: (Fm * a |-> (v, vsmerge vs)) ]]]
    CRASH
      (exists n, recover_any xp F n ds) \/
      exists ms' m',
      rep xp F (ActiveTxn (m', nil) m') ms' *
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
    or_l; cancel.

    or_r; cancel.
    eassign (mk_memstate (Map.remove a (MSTxn ms)) a0); eauto.
    eapply map_valid_remove; autorewrite with lists; eauto.
    setoid_rewrite singular_latest at 2; simpl; auto.
    rewrite length_updN; auto.
    apply updN_replay_disk_remove_eq; eauto.
    eauto.
    Unshelve. eauto.
  Qed.


  Theorem dsync_ok : forall xp ms a,
    {< F Fm ds vs,
    PRE
      rep xp F (ActiveTxn ds ds!!) ms *
      [[[ ds!! ::: (Fm * a |-> vs) ]]]
    POST RET:ms' exists m,
      rep xp F (ActiveTxn (m, nil) m) ms' *
      [[[ m ::: (Fm * a |-> (fst vs, nil)) ]]]
    CRASH
      (exists n, recover_any xp F n ds) \/
      exists m' ms',
      rep xp F (ActiveTxn (m', nil) m') ms' *
        [[[ m' ::: (Fm * a |-> (fst vs, nil)) ]]]
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
    or_l; cancel.
    or_r; cancel.
    eassign (mk_memstate (MSTxn ms) a0); simpl; eauto.
    apply map_valid_updN; auto.
    setoid_rewrite singular_latest at 2; simpl; auto.
    rewrite <- replay_disk_vssync_comm.
    substl ds!! at 1; auto.
    eauto.
    Unshelve. eauto.
  Qed.


  Theorem sync_ok : forall xp ms,
    {< F ds,
    PRE
      rep xp F (NoTxn ds) ms
    POST RET:ms'
      rep xp F (NoTxn (ds!!, nil)) ms'
    CRASH exists n,
      recover_any xp F n ds
    >} sync xp ms.
  Proof.
    unfold sync, recover_any.
    hoare.
    Unshelve. eauto.
  Qed.


  Local Hint Resolve map_valid_log_valid length_elements_cardinal_gt map_empty_vmap0.

  Theorem commit_ok : forall xp ms,
    {< F ds m,
     PRE  rep xp F (ActiveTxn ds m) ms
     POST RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn (pushd m ds)) ms') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn ms) > (LogLen xp) ]] *
            rep xp F (NoTxn ds) ms')
     CRASH exists ms', rep xp F (NoTxn ds) ms'
    >} commit xp ms.
  Proof.
    unfold commit.
    step.
    step.

    eassign (mk_memstate vmap0 ms').
    step.
    auto.
  Qed.


  (* a pseudo-commit for read-only transactions *)
  Theorem commit_ro_ok : forall xp ms,
    {< F ds,
    PRE
      rep xp F (ActiveTxn ds ds!!) ms
    POST RET:r
      rep xp F (NoTxn ds) r
    CRASH
      exists ms', rep xp F (NoTxn ds) ms'
    >} commit_ro xp ms.
  Proof.
    intros.
    eapply pimpl_ok2.
    apply abort_ok.
    cancel.
    apply sep_star_comm.
  Qed.


  Definition recover_any_pred := GLog.recover_any_pred.

  Theorem recover_ok: forall xp F cs,
    {< ds n,
    PRE
      recover_any_pred xp F n ds (GLog.mk_memstate vmap0 nil (MLog.mk_memstate vmap0 cs))
    POST RET:ms' exists d n, [[ n <= length (snd ds) ]] *
      rep xp F (NoTxn (d, nil)) ms' *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
    CRASH
      recover_any_pred xp F n ds (GLog.mk_memstate vmap0 nil (MLog.mk_memstate vmap0 cs))
    >} recover xp cs.
  Proof.
    unfold recover, recover_any_pred, rep.
  Admitted.

(*
  Theorem recover_idem : forall xp cs F Fold Fnew,
    crash_xform (recover_any_pred xp cs F Fold Fnew) =p=>
      exists cs', recover_any_pred xp cs' (crash_xform F) Fold Fnew.
  Proof.
    intros; apply GLog.recover_idem.
  Qed.


  Theorem intact_recover_any_pred : forall xp ds (F FD : pred),
    FD (list2nmem (fst ds)) ->
    crash_xform (intact xp F ds) =p=>
    exists cs, recover_any_pred xp cs (crash_xform F) FD FD.
  Proof.
    unfold recover_any_pred, intact, rep; intros.
    xform_norm; rewrite GLog.cached_recover_any_pred; eauto; cancel.
  Qed.


  Theorem recover_any_any_pred : forall xp ds n (F FD1 FD2 : pred),
    FD1 (list2nmem (nthd n ds)) ->
    FD2 (list2nmem (nthd (S n) ds)) ->
    crash_xform (recover_any xp F n ds) =p=>
    exists cs, recover_any_pred xp cs (crash_xform F) FD1 FD2.
  Proof.
    unfold recover_any_pred, recover_any, rep; intros.
    xform_norm.
    rewrite GLog.would_recover_any_any_pred; eauto.
  Qed.

  Theorem recover_any_pred_rep : forall xp cs (F FD1 FD2: pred),
    recover_any_pred xp cs F FD1 FD2 =p=> exists d ms,
    rep xp F (NoTxn (d, nil)) ms *
    ( [[[ d ::: crash_xform FD1 ]]] \/ [[[ d ::: crash_xform FD2 ]]]).
  Proof.
    unfold recover_any_pred, GLog.recover_any_pred, MLog.recover_either_pred.
    unfold rep, GLog.rep, MLog.rep; intros.
    cancel.
    eassign (memstate0 dummy1 cs); eassign raw; simpl; auto.

    apply sep_star_or_distr in H0; destruct H0; destruct_lifts.
    cancel; or_l. cancel. eauto.
    cancel; or_r. cancel.
    auto.
    apply GLog.vmap_match_nil.
    apply GLog.dset_match_nil.
    pred_apply; cancel.
  Qed.
*)

  Hint Resolve active_intact flushing_any.
  Hint Extern 0 (okToUnify (intact _ _ _) (intact _ _ _)) => constructor : okToUnify.


  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.
  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (read_raw _ _) _) => apply read_raw_ok : prog.
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
    PRE   rep xp F (ActiveTxn ds m) ms *
          [[ i < length vs]] *
          [[[ m ::: Fm * arrayN a vs ]]]
    POST RET:^(ms', r)
          rep xp F (ActiveTxn ds m) ms' *
          [[ r = fst (selN vs i ($0, nil)) ]]
    CRASH exists ms',
          rep xp F (ActiveTxn ds m) ms'
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
    PRE   rep xp F (ActiveTxn ds m) ms *
          [[ i < length vs /\ a <> 0 ]] *
          [[[ m ::: Fm * arrayN a vs ]]]
    POST RET:ms' exists m',
          rep xp F (ActiveTxn ds m') ms' *
          [[[ m' ::: Fm * arrayN a (updN vs i (v, nil)) ]]]
    CRASH exists m' ms',
          rep xp F (ActiveTxn ds m') ms'
    >} write_array xp a i v ms.
  Proof.
    unfold write_array.
    hoare.

    subst; pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    subst; pred_apply.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _) _) => apply write_array_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ ?a) (rep _ _ _ ?a)) => constructor : okToUnify.


  Definition read_range T A xp a nr (vfold : A -> valu -> A) v0 ms rx : prog T :=
    let^ (ms, r) <- ForN i < nr
    Ghost [ F Fm crash ds m vs ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      rep xp F (ActiveTxn ds m) ms *
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
    Ghost [ F Fm crash ds vs ]
    Loopvar [ ms ]
    Continuation lrx
    Invariant
      exists m, rep xp F (ActiveTxn ds m) ms *
      [[[ m ::: (Fm * arrayN a (vsupsyn_range vs (firstn i l))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i $0) ms;
      lrx ^(ms)
    Rof ^(ms);
    rx ms.


  Theorem read_range_ok : forall A xp a nr vfold (v0 : A) ms,
    {< F Fm ds m vs,
    PRE
      rep xp F (ActiveTxn ds m) ms *
      [[ nr <= length vs ]] *
      [[[ m ::: (Fm * arrayN a vs) ]]]
    POST RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' *
      [[ r = fold_left vfold (firstn nr (map fst vs)) v0 ]]
    CRASH
      exists ms', rep xp F (ActiveTxn ds m) ms'
    >} read_range xp a nr vfold v0 ms.
  Proof.
    unfold read_range; intros.
    hoare.

    subst; pred_apply; cancel.
    eapply lt_le_trans; eauto.
    subst; denote (Map.elements (MSTxn a0)) as Hx; rewrite <- Hx.
    pred_apply; cancel.

    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; subst; auto.
    rewrite map_length; omega.
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
    PRE
      rep xp F (ActiveTxn ds m) ms *
      [[ a <> 0 /\ length l <= length vs ]] *
      [[[ m ::: (Fm * arrayN a vs) ]]]
    POST RET:ms'
      exists m', rep xp F (ActiveTxn ds m') ms' *
      [[[ m' ::: (Fm * arrayN a (vsupsyn_range vs l)) ]]]
    CRASH exists ms' m',
      rep xp F (ActiveTxn ds m') ms'
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
    Ghost [ F Fm crash ds m vs ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      rep xp F (ActiveTxn ds m) ms *
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
    PRE
      rep xp F (ActiveTxn ds m) ms *
      [[ nr <= length vs /\ cond v0 = false ]] *
      [[[ m ::: (Fm * arrayN a vs) ]]]
    POST RET:^(ms', r)
      rep xp F (ActiveTxn ds m) ms' *
      ( exists v, [[ r = Some v /\ cond v = true ]] \/
      [[ r = None /\ cond (fold_left vfold (firstn nr (map fst vs)) v0) = false ]])
    CRASH
      exists ms', rep xp F (ActiveTxn ds m) ms'
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
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    mm' <- GLog.dwrite_vecs xp avl mm;
    rx (mk_memstate vmap0 mm').

  Definition dsync_vecs T xp al ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
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
    PRE
      rep xp F (ActiveTxn ds ds!!) ms *
      [[ NoDup (map fst avl) ]] *
      [[[ ds!! ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]]
    POST RET:ms' exists m',
      rep xp F (ActiveTxn (m', nil) m') ms' *
      [[[ m' ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]]
    XCRASH
      (exists n, recover_any xp F n ds) \/
      exists ms' m',
      rep xp F (ActiveTxn (m', nil) m') ms' *
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
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    rewrite H0; xform_norm.
    or_l; apply crash_xform_pimpl.
    unfold recover_any, rep; cancel.

    or_r; xform_norm; cancel.
    eassign (mk_memstate vmap0 x); simpl; eauto.
    simpl; apply map_valid_map0.
    setoid_rewrite singular_latest at 2; simpl; auto.
    apply dwrite_vsupd_vecs_ok; eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem dsync_vecs_ok : forall xp ms al,
    {< F Fm ds vsl,
    PRE
      rep xp F (ActiveTxn ds ds!!) ms *
      [[[ ds!! ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]]
    POST RET:ms' exists m',
      rep xp F (ActiveTxn (m', nil) m') ms' *
      [[[ m' ::: Fm * listmatch (fun vs a => a |=> fst vs) vsl al ]]]
    XCRASH exists n,
      recover_any xp F n ds
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
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    rewrite H0.
    xform_norm; eauto.
  Qed.


  Hint Extern 1 ({{_}} progseq (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.

(*  Hint Extern 0 (okToUnify (recover_any_pred _ _ _ _ _) (recover_any_pred _ _ _ _ _)) => constructor : okToUnify. *)

End LOG.


(* rewrite rules for recover_either_pred *)
(*
Require Import RelationClasses.
Require Import Morphisms.

Instance recover_any_pred_proper_iff :
  Proper (eq ==> eq ==> piff ==> piff ==> piff ==> pimpl) LOG.recover_any_pred.
Proof.
  unfold Proper, respectful; intros.
  unfold LOG.recover_any_pred, GLog.recover_any_pred, MemLog.MLog.recover_either_pred.
  subst. cancel.
  rewrite sep_star_or_distr; or_l.
  cancel; eauto.
  rewrite H1; eauto.
  pred_apply; rewrite H2; eauto.

  rewrite sep_star_or_distr; or_r.
  cancel; eauto.
  rewrite H1; eauto.
  pred_apply; rewrite H3; eauto.

  exists ds; exists n; intuition.
  pred_apply; rewrite H2; auto.
  pred_apply; rewrite H3; eauto.
Qed.


Instance recover_any_pred_proper_eq :
  Proper (eq ==> eq ==> piff ==> eq ==> eq ==> pimpl) LOG.recover_any_pred.
Proof.
  unfold Proper, respectful; intros.
  unfold LOG.recover_any_pred, GLog.recover_any_pred, MemLog.MLog.recover_either_pred.
  subst. cancel.
  rewrite sep_star_or_distr; or_l.
  cancel; eauto.
  rewrite H1; eauto.

  rewrite sep_star_or_distr; or_r.
  cancel; eauto.
  rewrite H1; eauto.

  exists ds; exists n; intuition.
Qed.


Instance recover_any_pred_proper_pimpl :
  Proper (eq ==> eq ==> piff ==> pimpl ==> pimpl ==> pimpl) LOG.recover_any_pred.
Proof.
  unfold Proper, respectful; intros.
  unfold LOG.recover_any_pred, GLog.recover_any_pred, MemLog.MLog.recover_either_pred.
  subst. cancel.
  rewrite sep_star_or_distr; or_l.
  cancel; eauto.
  rewrite H1; eauto.
  pred_apply; rewrite H2; eauto.

  rewrite sep_star_or_distr; or_r.
  cancel; eauto.
  rewrite H1; eauto.
  pred_apply; rewrite H3; eauto.

  exists ds; exists n; intuition.
Qed.

*)

Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
