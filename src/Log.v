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

Import ListNotations.
Set Implicit Arguments.


Module LOG.

  Record memstate := mk_memstate {
    MSTxn   : valumap;         (* memory state for active txns *)
    MSMem   : MLog.memstate    (* lower-level state *)
  }.

  Inductive state :=
  | NoTxn (cur : diskstate)
  (* No active transaction, MemLog.Synced or MemLog.Applying *)

  | ActiveTxn (old : diskstate) (cur : diskstate)
  (* A transaction is in progress.
   * It started from the first memory and has evolved into the second.
     MemLog.Synced
   *)
  | ApplyingTxn (old : diskstate)
  (* special state when crash inside dwrite *)

  | CommittingTxn (old : diskstate) (cur : diskstate)
  (* A commit is in progress
     MemLog.Flushing or MemLog.Applying
   *)
  .

  Definition rep xp F st ms :=
  let '(cm, mm) := (MSTxn ms, MSMem ms) in
  (exists nr,
  match st with
    | NoTxn cur =>
      [[ Map.Empty cm ]] *
      MLog.rep xp F nr (MLog.Synced cur) mm
    | ActiveTxn old cur =>
      [[ MLog.map_valid cm old ]] *
      [[ MLog.map_replay cm old cur ]] *
      MLog.rep xp F nr (MLog.Synced old) mm
    | ApplyingTxn old =>
      MLog.rep xp F nr (MLog.Applying old) mm
    | CommittingTxn old cur =>
      [[ MLog.map_valid cm old ]] *
      [[ MLog.map_replay cm old cur ]] *
      ( MLog.rep xp F nr (MLog.Applying old) mm \/
        MLog.rep xp F nr (MLog.Flushing old (Map.elements cm)) mm)
  end)%pred.


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
        let^ (mm', v) <- MLog.read xp a mm;
        rx ^(mk_memstate cm mm', v)
    end.

  Definition commit T xp ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    If (bool_dec (Map.is_empty cm) true) {
      rx ^(ms, true)
    } else {
      let^ (mm', r) <- MLog.flush xp (Map.elements cm) mm;
      rx ^(mk_memstate vmap0 mm', r)
    }.

  Definition dwrite T (xp : log_xparams) a v ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    let cm' := Map.remove a cm in
    mm' <- MLog.dwrite xp a v mm;
    rx (mk_memstate cm' mm').

  Definition dsync T xp a ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    mm' <- MLog.dsync xp a mm;
    rx (mk_memstate cm mm').

  Definition recover T xp cs rx : prog T :=
    mm <- MLog.recover xp cs;
    rx (mk_memstate vmap0 mm).

  Local Hint Unfold rep MLog.map_replay: hoare_unfold.
  Arguments MLog.rep: simpl never.
  Hint Extern 0 (okToUnify (MLog.rep _ _ _ _ _) (MLog.rep _ _ _ _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; repeat match goal with
  | [ H : @eq memstate ?ms (mk_memstate _ _) |- _ ] =>
     is_var ms; destruct ms; inversion H; subst; simpl
  | [ |- Map.Empty vmap0 ] => apply Map.empty_1
  | [ |- MLog.map_valid vmap0 _ ] => apply MLog.map_valid_map0
  end; eauto.

  (* This is a agressive hint *)
  Theorem begin_ok: forall xp ms,
    {< F m,
    PRE
      rep xp F (NoTxn m) ms
    POST RET:r
      rep xp F (ActiveTxn m m) r
    CRASH
      exists ms', rep xp F (NoTxn m) ms' 
               \/ rep xp F (ActiveTxn m m) ms'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
  Qed.


  Theorem abort_ok : forall xp ms,
    {< F m1 m2,
    PRE
      rep xp F (ActiveTxn m1 m2) ms
    POST RET:r
      rep xp F (NoTxn m1) r
    CRASH
      exists ms', rep xp F (ActiveTxn m1 m2) ms'
               \/ rep xp F (NoTxn m1) ms'
    >} abort xp ms.
  Proof.
    unfold abort.
    hoare using dems.
  Qed.


  Theorem read_ok: forall xp ms a,
    {< F Fm m1 m2 v,
    PRE
      rep xp F (ActiveTxn m1 m2) ms *
      [[[ m2 ::: Fm * a |-> v ]]]
    POST RET:^(ms', r)
      rep xp F (ActiveTxn m1 m2) ms' * [[ r = fst v ]]
    CRASH
      exists ms', rep xp F (ActiveTxn m1 m2) ms'
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.
    cancel.
    step.

    eapply MLog.replay_disk_eq; eauto.
    instantiate (d := m1); pred_apply; cancel.
    pimpl_crash; cancel.

    cancel.
    2: step.
    eexists; subst.
    eapply MLog.ptsto_replay_disk_not_in; eauto.
    apply MapFacts.not_find_in_iff; eauto.

    pimpl_crash; norm.
    instantiate (ms'0 := mk_memstate (MSTxn ms) ms').
    cancel. intuition.
  Qed.


  Theorem write_ok : forall xp ms a v,
    {< F Fm m1 m2 vs,
    PRE
      rep xp F (ActiveTxn m1 m2) ms * [[ a <> 0 ]] *
      [[[ m2 ::: (Fm * a |-> vs) ]]]
    POST RET:ms'
      exists m', rep xp F (ActiveTxn m1 m') ms' *
      [[[ m' ::: (Fm * a |-> (v, nil)) ]]]
    CRASH
      exists m' ms', rep xp F (ActiveTxn m1 m') ms'
    >} write xp a v ms.
  Proof.
    unfold write.
    hoare using dems.

    apply MLog.map_valid_add; eauto.
    erewrite <- MLog.replay_disk_length.
    eapply list2nmem_ptsto_bound; eauto.

    rewrite MLog.replay_disk_add.
    eapply list2nmem_updN; eauto.
  Qed.


  Lemma map_valid_remove : forall a ms d1 d2,
    MLog.map_valid ms d1 ->
    length d1 = length d2 ->
    MLog.map_valid (Map.remove a ms) d2.
  Proof.
    unfold MLog.map_valid; intros.
    erewrite <- H0.
    eapply H.
    eapply Map.remove_3; eauto.
  Qed.


  Lemma replay_disk_remove_updN_eq : forall F m d a v,
    (F * a |-> v)%pred (list2nmem (MLog.replay_disk (Map.elements m) d)) ->
    MLog.replay_disk (Map.elements m) d =
    MLog.replay_disk (Map.elements (Map.remove a m)) (updN d a v).
  Proof.
    intros.
    eapply list_selN_ext with (default := ($0, nil)); intros.
    repeat rewrite MLog.replay_disk_length; rewrite length_updN; auto.
    rewrite MLog.replay_disk_updN_comm.

    destruct (Nat.eq_dec pos a); subst.
    rewrite selN_updN_eq; [ apply eq_sym | ].
    eapply list2nmem_sel; eauto.
    rewrite MLog.replay_disk_length in *; eauto.

    rewrite selN_updN_ne by auto.
    case_eq (Map.find pos m); intros.
    apply Map.find_2 in H1.
    rewrite MLog.replay_disk_length in *.
    repeat erewrite MLog.replay_disk_selN_MapsTo; eauto.
    apply Map.remove_2; eauto.

    apply MapFacts.not_find_in_iff in H1.
    setoid_rewrite MLog.replay_disk_selN_not_In; auto.
    apply not_in_remove_not_in; auto.

    rewrite In_map_fst_MapIn.
    apply Map.remove_1; auto.
  Qed.


  Lemma list2nmem_replay_disk_remove_updN_ptsto : forall F a vs vs' d ms,
    (F * a |-> vs)%pred (list2nmem (MLog.replay_disk (Map.elements ms) d)) ->
    (F * a |-> vs')%pred
      (list2nmem (MLog.replay_disk (Map.elements (Map.remove a ms)) (updN d a vs'))).
  Proof.
    intros.
    rewrite MLog.replay_disk_updN_comm.
    erewrite <- updN_twice.
    eapply list2nmem_updN.
    rewrite <- MLog.replay_disk_updN_comm.
    erewrite <- replay_disk_remove_updN_eq; eauto.

    rewrite In_map_fst_MapIn; apply Map.remove_1; auto.
    rewrite In_map_fst_MapIn; apply Map.remove_1; auto.
  Qed.


  Theorem dwrite_ok_twomem : forall xp ms a v,
    {< F Fm1 Fm2 m1 m2 vs1 vs2,
    PRE
      rep xp F (ActiveTxn m1 m2) ms *
      [[[ m1 ::: (Fm1 * a |-> vs1) ]]] *
      [[[ m2 ::: (Fm2 * a |-> vs2) ]]]
    POST RET:ms' exists m1' m2',
      rep xp F (ActiveTxn m1' m2') ms' *
      [[[ m1' ::: (Fm1 * a |-> (v, vsmerge vs1)) ]]] *
      [[[ m2' ::: (Fm2 * a |-> (v, vsmerge vs1)) ]]]
    CRASH
      exists m' m1' ms',
      rep xp F (ActiveTxn m1  m') ms' \/
      rep xp F (ActiveTxn m1' m') ms' *
        [[[ m1' ::: (Fm1 * a |-> (v, vsmerge vs1)) ]]] \/
      rep xp F (ApplyingTxn m1  ) ms'
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite.
    step.
    step; subst.

    eapply map_valid_remove; autorewrite with lists; eauto.
    eapply list2nmem_replay_disk_remove_updN_ptsto; eauto.

    (* crash conditions *)
    instantiate (ms'0 := mk_memstate vmap0 ms').
    or_r; or_r; cancel.

    instantiate (ms'1 := mk_memstate (MSTxn ms) ms').
    or_l; cancel.

    instantiate (ms'2 := mk_memstate (Map.remove a (MSTxn ms)) ms').
    or_r; or_l; cancel.
    eapply map_valid_remove; autorewrite with lists; eauto.
    Unshelve. all: eauto.
  Qed.


  Theorem dsync_ok_twomem : forall xp ms a,
    {< F Fm1 Fm2 m1 m2 vs1 vs2,
    PRE
      rep xp F (ActiveTxn m1 m2) ms *
      [[[ m1 ::: (Fm1 * a |-> vs1) ]]] *
      [[[ m2 ::: (Fm2 * a |-> vs2) ]]]
    POST RET:ms' exists m1' m2',
      rep xp F (ActiveTxn m1' m2') ms' *
      [[[ m1' ::: (Fm1 * a |-> (fst vs1, nil)) ]]] *
      [[[ m2' ::: (Fm2 * a |-> (fst vs2, nil)) ]]]
    CRASH
      exists m' m1' ms',
      rep xp F (ActiveTxn m1  m') ms' \/
      rep xp F (ActiveTxn m1' m') ms' *
        [[[ m1' ::: (Fm1 * a |-> (fst vs1, nil)) ]]]
    >} dsync xp a ms.
  Proof.
    unfold dsync.
    step.
    step; subst.
    apply MLog.map_valid_updN; auto.
    rewrite <- MLog.replay_disk_vssync_comm.
    unfold vssync; erewrite <- list2nmem_sel; eauto; simpl.
    eapply list2nmem_updN; eauto.

    (* crashes *)
    instantiate (ms'0 := mk_memstate (MSTxn ms) ms').
    or_l; cancel.
    instantiate (ms'1 := mk_memstate (MSTxn ms) ms').
    or_r; cancel.
    apply MLog.map_valid_updN; auto.
    Unshelve. eauto.
  Qed.


  Set Regular Subst Tactic.

  Lemma updN_replay_disk_remove_eq : forall m d a v,
    d = MLog.replay_disk (Map.elements m) d ->
    updN d a v = MLog.replay_disk (Map.elements (Map.remove a m)) (updN d a v).
  Proof.
    intros.
    eapply list_selN_ext with (default := ($0, nil)); intros.
    repeat rewrite MLog.replay_disk_length; rewrite length_updN; auto.
    rewrite MLog.replay_disk_updN_comm.
    rewrite length_updN in H0.

    destruct (Nat.eq_dec pos a); subst.
    repeat rewrite selN_updN_eq; auto.
    rewrite MLog.replay_disk_length in *; eauto.

    repeat rewrite selN_updN_ne by auto.
    rewrite H at 1.
    case_eq (Map.find pos m); intros.
    apply Map.find_2 in H1.
    repeat erewrite MLog.replay_disk_selN_MapsTo; eauto.
    apply Map.remove_2; eauto.

    apply MapFacts.not_find_in_iff in H1.
    setoid_rewrite MLog.replay_disk_selN_not_In; auto.
    apply not_in_remove_not_in; auto.

    rewrite In_map_fst_MapIn.
    apply Map.remove_1; auto.
  Qed.


  Theorem dwrite_ok : forall xp ms a v,
    {< F Fm m vs,
    PRE
      rep xp F (ActiveTxn m m) ms *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST RET:ms' exists m',
      rep xp F (ActiveTxn m' m') ms' *
      [[[ m' ::: (Fm * a |-> (v, vsmerge vs)) ]]]
    CRASH
      exists ms' m',
      rep xp F (ActiveTxn m  m) ms' \/
      rep xp F (ActiveTxn m' m') ms' *
          [[[ m' ::: (Fm * a |-> (v, vsmerge vs)) ]]] \/
      rep xp F (ApplyingTxn m) ms'
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite.
    step.
    step; subst.

    eapply map_valid_remove; autorewrite with lists; eauto.
    apply updN_replay_disk_remove_eq; eauto.

    (* crash conditions *)
    instantiate (ms'0 := mk_memstate vmap0 ms').
    or_r; or_r; cancel.

    instantiate (ms'1 := mk_memstate (MSTxn ms) ms').
    or_l; cancel.

    instantiate (ms'2 := mk_memstate (Map.remove a (MSTxn ms)) ms').
    or_r; or_l; cancel.
    eapply map_valid_remove; autorewrite with lists; eauto.
    apply updN_replay_disk_remove_eq; eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem dsync_ok : forall xp ms a,
    {< F Fm m vs,
    PRE
      rep xp F (ActiveTxn m m) ms *
      [[[ m ::: (Fm * a |-> vs) ]]]
    POST RET:ms' exists m',
      rep xp F (ActiveTxn m' m') ms' *
      [[[ m' ::: (Fm * a |-> (fst vs, nil)) ]]]
    CRASH
      exists m' ms',
      rep xp F (ActiveTxn m m) ms' \/
      rep xp F (ActiveTxn m' m') ms' *
        [[[ m' ::: (Fm * a |-> (fst vs, nil)) ]]]
    >} dsync xp a ms.
  Proof.
    unfold dsync.
    step.
    step; subst.
    apply MLog.map_valid_updN; auto.
    rewrite <- MLog.replay_disk_vssync_comm.
    substl m at 1; auto.

    (* crashes *)
    instantiate (ms'0 := mk_memstate (MSTxn ms) ms').
    or_l; cancel.
    instantiate (ms'1 := mk_memstate (MSTxn ms) ms').
    or_r; cancel.
    apply MLog.map_valid_updN; auto.
    rewrite <- MLog.replay_disk_vssync_comm.
    substl m at 1; auto.
    Unshelve. eauto.
  Qed.


  Lemma map_valid_log_valid : forall ms d,
    MLog.map_valid ms d ->
    MLog.log_valid (Map.elements ms) d.
  Proof.
    unfold MLog.map_valid, MLog.log_valid; intuition;
    apply KIn_exists_elt_InA in H0;
    destruct H0; simpl in H0;
    eapply H; eauto;
    apply Map.elements_2; eauto.
  Qed.

  Lemma length_elements_cardinal_gt : forall V (m : Map.t V) n,
    length (Map.elements m) > n ->
    Map.cardinal m > n.
  Proof.
    intros; rewrite Map.cardinal_1; auto.
  Qed.

  Lemma map_empty_vmap0 : Map.Empty vmap0.
  Proof.
    apply Map.empty_1.
  Qed.

  Local Hint Resolve map_valid_log_valid length_elements_cardinal_gt map_empty_vmap0.

  Theorem commit_ok : forall xp ms,
    {< F m1 m2,
     PRE  rep xp F (ActiveTxn m1 m2) ms
     POST RET:^(ms',r)
          ([[ r = true ]] *
            rep xp F (NoTxn m2) ms') \/
          ([[ r = false ]] *
            [[ Map.cardinal (MSTxn ms) > (LogLen xp) ]] *
            rep xp F (NoTxn m1) ms')
     CRASH  exists ms',
            rep xp F (NoTxn m1) ms' \/
            rep xp F (NoTxn m2) ms' \/
            rep xp F (CommittingTxn m1 m2) ms'
    >} commit xp ms.
  Proof.
    unfold commit.
    step.
    step.

    (* case 1 : nothing to flush *)
    or_l; cancel.
    rewrite MLog.replay_disk_is_empty; auto; cancel.
    apply MapFacts.is_empty_iff; auto.

    (* case 1 : did flush *)
    step.
    step.

    (* crashes *)
    5: instantiate (1 := mk_memstate (MSTxn ms) ms').
    6: instantiate (1 := mk_memstate (MSTxn ms) ms').
    all: try instantiate (1 := mk_memstate vmap0 ms').
    or_l; cancel.
    or_l; cancel.
    or_r; or_l; cancel.
    or_r; or_l; cancel.
    or_r; or_r; cancel.
    or_r; or_r; cancel.
  Qed.


  Theorem recover_ok: forall xp F cs,
    {< raw Fold Fnew,
    PRE
      BUFCACHE.rep cs raw *
      [[ crash_xform (F * MLog.recover_either_pred xp Fold Fnew)%pred raw ]]
    POST RET:ms' exists d',
      rep xp (crash_xform F) (NoTxn d') ms' *
      ([[[ d' ::: crash_xform Fold ]]] \/
       [[[ d' ::: crash_xform Fnew ]]])
    CRASH exists cs',
      BUFCACHE.rep cs' raw
    >} recover xp cs.
  Proof.
    unfold recover, rep.
    hoare.
  Qed.


  Definition intact xp F old :=
    (exists ms,
      rep xp F (NoTxn old) ms \/
      rep xp F (ApplyingTxn old) ms \/
      exists new, rep xp F (ActiveTxn old new) ms)%pred.

  Lemma active_txn_intact : forall xp F old new ms,
    rep xp F (ActiveTxn old new) ms =p=> intact xp F old.
  Proof.
    unfold intact; cancel.
  Qed.

  Lemma applying_txn_intact : forall xp F m ms,
    rep xp F (ApplyingTxn m) ms =p=> intact xp F m.
  Proof.
    unfold intact; cancel.
  Qed.

  Hint Resolve active_txn_intact applying_txn_intact.
  Hint Extern 0 (okToUnify (intact _ _ _) (intact _ _ _)) => constructor : okToUnify.


  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.
  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.


  Definition read_array T xp a i ms rx : prog T :=
    let^ (ms, r) <- read xp (a + i) ms;
    rx ^(ms, r).

  Definition write_array T xp a i v ms rx : prog T :=
    ms <- write xp (a + i) v ms;
    rx ms.


  Theorem read_array_ok : forall xp ms a i,
    {< F Fm m1 m2 vs,
    PRE   rep xp F (ActiveTxn m1 m2) ms *
          [[ i < length vs]] *
          [[[ m2 ::: Fm * arrayN a vs ]]]
    POST RET:^(ms', r)
          rep xp F (ActiveTxn m1 m2) ms' *
          [[ r = fst (selN vs i ($0, nil)) ]]
    CRASH exists ms',
          rep xp F (ActiveTxn m1 m2) ms'
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
    {< F Fm m1 m2 vs,
    PRE   rep xp F (ActiveTxn m1 m2) ms *
          [[ i < length vs /\ a <> 0 ]] *
          [[[ m2 ::: Fm * arrayN a vs ]]]
    POST RET:ms' exists m',
          rep xp F (ActiveTxn m1 m') ms' *
          [[[ m' ::: Fm * arrayN a (updN vs i (v, nil)) ]]]
    CRASH exists m' ms',
          rep xp F (ActiveTxn m1 m') ms'
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
    Ghost [ F Fm crash m1 m2 vs ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      rep xp F (ActiveTxn m1 m2) ms *
      [[[ m2 ::: (Fm * arrayN a vs) ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) v0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array xp a i ms;
      lrx ^(ms, vfold pf v)
    Rof ^(ms, v0);
    rx ^(ms, r).


  Definition write_range T xp a l ms rx : prog T :=
    let^ (ms) <- ForN i < length l
    Ghost [ F Fm crash m1 vs ]
    Loopvar [ ms ]
    Continuation lrx
    Invariant
      exists m2, rep xp F (ActiveTxn m1 m2) ms *
      [[[ m2 ::: (Fm * arrayN a (vsupsyn_range vs (firstn i l))) ]]]
    OnCrash crash
    Begin
      ms <- write_array xp a i (selN l i $0) ms;
      lrx ^(ms)
    Rof ^(ms);
    rx ms.


  Theorem read_range_ok : forall A xp a nr vfold (v0 : A) ms,
    {< F Fm m1 m2 vs,
    PRE
      rep xp F (ActiveTxn m1 m2) ms *
      [[ nr <= length vs ]] *
      [[[ m2 ::: (Fm * arrayN a vs) ]]]
    POST RET:^(ms', r)
      rep xp F (ActiveTxn m1 m2) ms' *
      [[ r = fold_left vfold (firstn nr (map fst vs)) v0 ]]
    CRASH
      exists ms', rep xp F (ActiveTxn m1 m2) ms'
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
    (F ✶ arrayN a vs)%pred (list2nmem (MLog.replay_disk (Map.elements ms) d)) ->
    a + i < length d.
  Proof.
    intros.
    apply list2nmem_arrayN_bound in H0; destruct H0; subst; simpl in *.
    inversion H.
    rewrite MLog.replay_disk_length in *.
    omega.
  Qed.

  Theorem write_range_ok : forall xp a l ms,
    {< F Fm m1 m2 vs,
    PRE
      rep xp F (ActiveTxn m1 m2) ms *
      [[ a <> 0 /\ length l <= length vs ]] *
      [[[ m2 ::: (Fm * arrayN a vs) ]]]
    POST RET:ms'
      exists m', rep xp F (ActiveTxn m1 m') ms' *
      [[[ m' ::: (Fm * arrayN a (vsupsyn_range vs l)) ]]]
    CRASH exists ms' m',
      rep xp F (ActiveTxn m1 m') ms'
    >} write_range xp a l ms.
  Proof.
    unfold write_range; intros.
    step.
    subst; pred_apply; cancel.

    step.
    apply MLog.map_valid_add; auto; try omega.
    eapply write_range_length_ok; eauto; omega.

    subst; rewrite MLog.replay_disk_add.
    apply vsupsyn_range_progress; auto.

    step.
    subst; pred_apply.
    erewrite firstn_oob; eauto.
    Unshelve. exact tt.
  Qed.


  (* like read_range, but stops when cond is true *)
  Definition read_cond T A xp a nr (vfold : A -> valu -> A) v0 (cond : A -> bool) ms rx : prog T :=
    let^ (ms, r) <- ForN i < nr
    Ghost [ F Fm crash m1 m2 vs ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      rep xp F (ActiveTxn m1 m2) ms *
      [[[ m2 ::: (Fm * arrayN a vs) ]]] * [[ cond pf = false ]] *
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
    {< F Fm m1 m2 vs,
    PRE
      rep xp F (ActiveTxn m1 m2) ms *
      [[ nr <= length vs /\ cond v0 = false ]] *
      [[[ m2 ::: (Fm * arrayN a vs) ]]]
    POST RET:^(ms', r)
      rep xp F (ActiveTxn m1 m2) ms' *
      ( exists v, [[ r = Some v /\ cond v = true ]] \/
      [[ r = None /\ cond (fold_left vfold (firstn nr (map fst vs)) v0) = false ]])
    CRASH
      exists ms', rep xp F (ActiveTxn m1 m2) ms'
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
    mm' <- MLog.dwrite_vecs xp avl mm;
    rx (mk_memstate vmap0 mm').

  Definition dsync_vecs T xp al ms rx : prog T :=
    let '(cm, mm) := (MSTxn ms, MSMem ms) in
    mm' <- MLog.dsync_vecs xp al mm;
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
    refine (_ (IHavl ovl m _ _ Hx)); [ intro | | pred_apply; cancel ].
    erewrite (@list2nmem_sel _ _ m n (p_cur, _)) by (pred_apply; cancel).
    erewrite <- MLog.vsupd_selN_not_in; eauto.
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

  Theorem dwrite_vecs_ok : forall xp ms avl,
    {< F Fm m ovl,
    PRE
      rep xp F (ActiveTxn m m) ms *
      [[ NoDup (map fst avl) ]] *
      [[[ m ::: Fm * listmatch (fun v e => (fst e) |-> v) ovl avl ]]]
    POST RET:ms' exists m',
      rep xp F (ActiveTxn m' m') ms' *
      [[[ m' ::: Fm * listmatch (fun v e => (fst e) |-> (snd e, vsmerge v)) ovl avl ]]]
    CRASH
      exists ms' m',
      rep xp F (ActiveTxn m  m) ms' \/
      rep xp F (ActiveTxn m' m') ms' *
          [[ exists n, m' = vsupd_vecs m (firstn n avl) ]] \/
      rep xp F (ApplyingTxn m) ms'
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs.
    step.
    eapply dwrite_ptsto_inbound; eauto.

    step; subst.
    apply MLog.map_valid_map0.
    apply dwrite_vsupd_vecs_ok; auto.

    (* crash conditions *)
    instantiate (ms'0 := mk_memstate vmap0 ms').
    or_r; or_r; cancel.

    instantiate (ms'1 := mk_memstate (MSTxn ms) ms').
    or_l; cancel.

    instantiate (ms'2 := mk_memstate vmap0 ms').
    or_r; or_l; cancel.
    apply MLog.map_valid_map0.
    eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem dsync_vecs_ok : forall xp ms al,
    {< F Fm m vsl,
    PRE
      rep xp F (ActiveTxn m m) ms *
      [[[ m ::: Fm * listmatch (fun vs a => a |-> vs) vsl al ]]]
    POST RET:ms' exists m',
      rep xp F (ActiveTxn m' m') ms' *
      [[[ m' ::: Fm * listmatch (fun vs a => a |-> (fst vs, nil)) vsl al ]]]
    CRASH
      exists m' ms',
      rep xp F (ActiveTxn m m) ms' \/
      rep xp F (ActiveTxn m' m') ms' *
          [[ exists n, m' = vssync_vecs m (firstn n al) ]]
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs.
    step.
    eapply listmatch_ptsto_list2nmem_inbound.
    pred_apply; rewrite listmatch_sym; eauto.

    step; subst.
    apply MLog.map_valid_vssync_vecs; auto.
    rewrite <- MLog.replay_disk_vssync_vecs_comm.
    f_equal; auto.
    apply dsync_vssync_vecs_ok; auto.

    (* crashes *)
    instantiate (ms'0 := mk_memstate (MSTxn ms) ms').
    or_l; cancel.
    instantiate (ms'1 := mk_memstate (MSTxn ms) ms').
    or_r; cancel.
    apply MLog.map_valid_vssync_vecs; auto.
    rewrite <- MLog.replay_disk_vssync_vecs_comm.
    f_equal; auto.
    eauto.
    Unshelve. eauto.
  Qed.



End LOG.


Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
