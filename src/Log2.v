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
Require Import DiskLog2.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MemLog.
Require Import MapUtils.

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


  Theorem dwrite_ok : forall xp ms a v,
    {< F Fm1 Fm2 m1 m2 vs1 vs2,
    PRE
      rep xp F (ActiveTxn m1 m2) ms * [[ a <> 0 ]] *
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
    CRASH exists raw' cs',
      BUFCACHE.rep cs' raw' *
      [[ (crash_xform F * MLog.recover_either_pred xp 
         (crash_xform Fold) (crash_xform Fnew))%pred raw' ]]
    >} recover xp cs.
  Proof.
    unfold rep.
    intros; eapply pimpl_ok2.
    apply MLog.recover_ok.
    cancel; eauto.
    step.
  Qed.


  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.
  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.


  Definition read_array T xp a i ms rx : prog T :=
    let^ (ms, r) <- read xp (a + i) ms;
    rx ^(ms, r).

  Definition write_array T xp a i v ms rx : prog T :=
    ms <- write xp (a + i) v ms;
    rx ms.


  Theorem read_array_ok : forall xp ms a i,
    {< mbase m vs F,
    PRE
      rep xp F (ActiveTxn mbase m) mscs *
      [[ exists F', (array a vs stride * F')%pred (list2mem m) ]] *
      [[ wordToNat i < length vs ]]
    POST RET:^(mscs,r)
      [[ r = sel vs i $0 ]] * rep xp F (ActiveTxn mbase m) mscs
    CRASH
      exists mscs', rep xp F (ActiveTxn mbase m) mscs'
    >} read_array xp a i stride mscs.
  Proof.
    unfold read_array.
    hoare.

    rewrite isolate_fwd with (i:=i) by auto.
    cancel.
  Qed.

  Theorem write_array_ok : forall xp a i stride v mscs,
    {< mbase m vs F F',
    PRE
      rep xp F (ActiveTxn mbase m) mscs *
      [[ (array a vs stride * F')%pred (list2mem m) ]] *
      [[ wordToNat i < length vs ]]
    POST RET:mscs
      exists m', rep xp F (ActiveTxn mbase m') mscs *
      [[ (array a (Array.upd vs i v) stride * F')%pred (list2mem m') ]]
    CRASH
      exists m' mscs', rep xp F (ActiveTxn mbase m') mscs'
    >} write_array xp a i stride v mscs.
  Proof.
    unfold write_array.
    hoare.

    rewrite isolate_fwd with (i:=i) by auto.
    cancel.

    rewrite <- isolate_bwd_upd by auto.
    cancel.

    Grab Existential Variables.
    exact $0.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _) _) => apply write_array_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ ?a) (rep _ _ _ ?a)) => constructor : okToUnify.

End LOG.


Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
