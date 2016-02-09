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

Module Map := FMapAVL.Make(Nat_as_OT).
Module MapFacts := WFacts_fun Nat_as_OT Map.
Module MapProperties := WProperties_fun Nat_as_OT Map.
Module MapOrdProperties := OrdProperties Map.

Import ListNotations.
Set Implicit Arguments.

Definition valumap := Map.t valu.

Record memstate := mk_memstate {
  MSOld   : valumap;   (* memory state for committed txns *)
  MSCur   : valumap;   (* memory state for active txns *)
  MSCache : cachestate    (* cache state *)
}.

Definition map0 := Map.empty valu.
Definition diskstate := list valu.


Inductive logstate :=
| NoTxn (cur : diskstate)
(* All transaction is committed, but might not be applied yet *)

| ActiveTxn (old : diskstate) (cur : diskstate)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. e.g. DiskLog.Synced
 *)

| FlushingTxn (old : diskstate) (cur : diskstate)
(* Current transaction is being flushed to the log, but not sync'ed or
 * committed yet. e.g. DiskLog.ExtendedUnsync or DiskLog.Extended *)

| NoTxnApplying (cur : diskstate)
(* Applying committed transactions to the disk.
   Block content might or might not be synced.
   Log might be truncated but not yet synced.
   e.g. DiskLog.Synced or DiskLog.Truncated
 *)
.



Module LOG.

  Definition replay_mem (log : DLog.contents) init : valumap :=
    fold_left (fun m e => Map.add (fst e) (snd e) m) log init.

  Definition replay_disk (log : DLog.contents) (m : diskstate) : diskstate:=
    fold_left (fun m' e => updN m' (fst e) (snd e)) log m.

  Definition map_replay ms old cur : rawpred :=
    ([[ cur = replay_disk (Map.elements ms) old ]])%pred.

  Definition map_empty ms : rawpred :=
    ([[ Map.Equal ms map0 ]])%pred.

  Definition map_keys (m : valumap) := map fst (Map.elements m).

  Definition map_merge (m1 m2 : valumap) :=
    replay_mem (Map.elements m2) m1.

  Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).

  Definition synced_data xp (d : diskstate) : rawpred :=
    arrayN (DataStart xp) (synced_list d).

  Definition nil_unless_in (keys: list addr) (l: list (list valu)) :=
    forall a, ~ In a keys -> selN l a nil = nil.

  Definition unsync_applying xp (ms : valumap) (old cur : diskstate) : rawpred :=
    (exists vs, [[ nil_unless_in (map_keys ms) vs /\ length vs = length old]] *
     arrayN (DataStart xp) (List.combine old vs) *
     map_replay ms old cur
    )%pred.

  Definition unsync_syncing xp (ms : valumap) (cur : diskstate) : rawpred :=
    (exists vs, [[ nil_unless_in (map_keys ms) vs /\ length vs = length cur ]] *
     arrayN (DataStart xp) (List.combine cur vs)
    )%pred.

  Definition entries_valid (ms : valumap) (m : diskstate) :=
     forall a v, Map.MapsTo a v ms -> a <> 0 /\ a < length m.

  Definition rep_inner xp st log raw oms cms :=
    (match st with
    | NoTxn cur =>
        map_replay oms raw cur *
        map_empty cms *
        synced_data xp raw *
        DLog.rep xp (DLog.Synced log)
    | ActiveTxn old cur =>
        map_replay oms raw old *
        map_replay cms old cur *
        synced_data xp raw *
        DLog.rep xp (DLog.Synced log)
    | FlushingTxn old cur =>
        map_replay oms raw old *
        map_replay cms old cur *
        synced_data xp raw *
        (DLog.rep xp (DLog.ExtendedUnsync log)
      \/ DLog.rep xp (DLog.Extended log (Map.elements cms)))
    | NoTxnApplying cur =>
        map_empty cms *
        (((DLog.rep xp (DLog.Synced log)) * (unsync_applying xp oms raw cur))
      \/ ((DLog.rep xp (DLog.Synced log)) * (unsync_syncing xp oms cur))
      \/ ((DLog.rep xp (DLog.Truncated log)) * (synced_data xp cur)))
    end)%pred.

  Definition rep xp st ms := 
    ( exists F d log raw, 
      let '(cs, oms, cms) := (MSCache ms, MSOld ms, MSCur ms) in
      BUFCACHE.rep cs d *
      [[ Map.Equal oms (replay_mem log map0) ]] *
      [[ entries_valid oms raw /\ entries_valid cms raw ]] *
      [[ (F * rep_inner xp st log raw oms cms)%pred d ]])%pred.

  Definition begin T (xp : log_xparams) ms rx : prog T :=
    let '(oms, cms, cs) := (MSOld ms, MSCur ms, MSCache ms) in
    rx (mk_memstate oms map0 cs).

  Definition abort T (xp : log_xparams) ms rx : prog T :=
    let '(oms, cms, cs) := (MSOld ms, MSCur ms, MSCache ms) in
    rx (mk_memstate oms map0 cs).

  Definition write T (xp : log_xparams) a v ms rx : prog T :=
    let '(oms, cms, cs) := (MSOld ms, MSCur ms, MSCache ms) in
    rx (mk_memstate oms (Map.add a v cms) cs).

  Definition read T xp a ms rx : prog T :=
    let '(oms, cms, cs) := (MSOld ms, MSCur ms, MSCache ms) in
    match Map.find a cms with
    | Some v =>   rx ^(ms, v)
    | None =>
      match Map.find a oms with
      | Some v => rx ^(ms, v)
      | None =>
        let^ (cs, v) <- BUFCACHE.read_array (DataStart xp) a cs;
        rx ^(mk_memstate oms cms cs, v)
      end
    end.

  Definition commit T xp ms rx : prog T :=
    let '(oms, cms, cs) := (MSOld ms, MSCur ms, MSCache ms) in
    If (bool_dec (Map.is_empty cms) true) {
      rx ^(ms, true)
    } else {
      let^ (cs, ok) <- DLog.extend xp (Map.elements cms) cs;
      If (bool_dec ok true) {
        rx ^(mk_memstate (map_merge oms cms) map0 cs, true)
      } else {
        ms <- abort xp (mk_memstate oms cms cs);
        rx ^(ms, false)
      }
    }.

  Definition apply T xp ms rx : prog T :=
    let '(oms, cms, cs) := (MSOld ms, MSCur ms, MSCache ms) in
    cs <- BUFCACHE.write_vecs (DataStart xp) (Map.elements oms) cs;
    cs <- BUFCACHE.sync_vecs (DataStart xp) (map_keys oms) cs;
    cs <- DLog.trunc xp cs;
    rx (mk_memstate map0 map0 cs).

  Lemma entries_valid_map0 : forall m,
    entries_valid map0 m.
  Proof.
    unfold entries_valid, map0; intuition; exfalso;
    apply MapFacts.empty_mapsto_iff in H; auto.
  Qed.

  Local Hint Resolve entries_valid_map0.


  Lemma mapeq_elements : forall V m1 m2,
    @Map.Equal V m1 m2 -> Map.elements m1 = Map.elements m2.
  Proof.
    intros.
    apply MapOrdProperties.elements_Equal_eqlistA in H.
    generalize dependent (Map.elements m2).
    generalize dependent (Map.elements m1).
    induction l.
    - intros. inversion H. reflexivity.
    - intros. destruct l0; inversion H. subst.
      inversion H3. destruct a; destruct p; simpl in *; subst.
      f_equal; eauto.
  Qed.

  Local Hint Unfold rep map_replay rep_inner map_empty: hoare_unfold.
  Arguments DLog.rep: simpl never.
  Hint Extern 0 (okToUnify (DLog.rep _ _) (DLog.rep _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; try match goal with
  | [ H : @eq memstate ?ms (mk_memstate _ _ _) |- _ ] =>
     destruct ms; inversion H; subst
  end; eauto.

  Theorem begin_ok: forall xp ms,
    {< m,
    PRE
      rep xp (NoTxn m) ms
    POST RET:r
      rep xp (ActiveTxn m m) r
    CRASH
      exists ms', rep xp (NoTxn m) ms' \/ rep xp (ActiveTxn m m) ms'
    >} begin xp ms.
  Proof.
    unfold begin.
    hoare using dems.
    pred_apply; cancel; cancel.
    or_l.
    repeat cancel; auto.
  Qed.


  Theorem abort_ok : forall xp ms,
    {< m1 m2,
    PRE
      rep xp (ActiveTxn m1 m2) ms
    POST RET:r
      rep xp (NoTxn m1) r
    CRASH
      exists ms', rep xp (ActiveTxn m1 m2) ms' \/ rep xp (NoTxn m1) ms'
    >} abort xp ms.
  Proof.
    unfold abort.
    hoare using dems.
    pred_apply; repeat cancel.
    pimpl_crash.
    or_l.
    repeat cancel; auto.
  Qed.

  Arguments DLog.rep : simpl never.

  Lemma replay_disk_length : forall l m,
    length (replay_disk l m) = length m.
  Proof.
    induction l; intros; simpl; auto.
    rewrite IHl.
    rewrite length_updN; auto.
  Qed.

  Hint Rewrite replay_disk_length : lists.

  Definition KIn V := InA (@Map.eq_key V).
  Definition KNoDup V := NoDupA (@Map.eq_key V).

  Lemma replay_disk_updN_comm : forall l d a v,
    ~ In a (map fst l)
    -> replay_disk l (updN d a v) = updN (replay_disk l d) a v.
  Proof.
    induction l; simpl; intuition; simpl in *.
    rewrite updN_comm by auto.
    apply IHl; auto.
  Qed.

  Lemma replay_disk_selN_other : forall l d a (def : valu),
    ~ In a (map fst l)
    -> NoDup (map fst l)
    -> selN (replay_disk l d) a def = selN d a def.
  Proof.
    induction l; simpl; intuition; simpl in *.
    inversion H0; subst; auto.
    rewrite replay_disk_updN_comm by auto.
    rewrite selN_updN_ne by auto.
    apply IHl; auto.
  Qed.

  Lemma in_map_fst_exists_snd : forall A B (l : list (A * B)) a,
    In a (map fst l) -> exists b, In (a, b) l.
  Proof.
    induction l; simpl; firstorder.
    destruct a; simpl in *; subst; eauto.
  Qed.

  Local Hint Resolve MapProperties.eqke_equiv.

  Lemma KNoDup_NoDup: forall V (l : list (addr * V)),
    KNoDup l -> NoDup (map fst l).
  Proof.
    induction l; simpl; intros; constructor.
    inversion H; subst.
    contradict H2.
    apply in_map_fst_exists_snd in H2; destruct H2.
    apply InA_alt.
    exists (fst a, x); intuition.
    destruct a; simpl in *.
    cbv; auto.
    inversion H; subst.
    apply IHl; auto.
  Qed.

  Lemma map_fst_nodup: forall (ms : valumap),
    NoDup (map fst (Map.elements ms)).
  Proof.
    intros.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.

  Lemma replay_disk_selN_In : forall l m a v def,
    In (a, v) l -> NoDup (map fst l) -> a < length m ->
    selN (replay_disk l m) a def = v.
  Proof.
    induction l; simpl; intros; auto.
    inversion H.
    inversion H0; subst.
    destruct a; intuition; simpl.
    inversion H2; subst.
    rewrite replay_disk_updN_comm by auto.
    rewrite selN_updN_eq; auto.
    erewrite replay_disk_length; auto.
    simpl in *.
    apply IHl; auto.
    rewrite length_updN; auto.
  Qed.

  Lemma replay_disk_selN_In_KNoDup : forall a v l m def,
    In (a, v) l -> KNoDup l -> a < length m ->
    selN (replay_disk l m) a def = v.
  Proof.
    intros.
    eapply replay_disk_selN_In; eauto.
    apply KNoDup_NoDup; auto.
  Qed.


  Lemma InA_eqke_In : forall V a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
  Proof.
    induction l; intros; auto; inversion H; subst.
    inversion H1.
    destruct a0; simpl in *; subst; auto.
    simpl. right.
    apply IHl; auto.
  Qed.

  Lemma replay_disk_selN_MapsTo : forall a v ms m def,
    Map.MapsTo a v ms -> a < length m ->
    selN (replay_disk (Map.elements ms) m) a def = v.
  Proof.
    intros.
    apply replay_disk_selN_In_KNoDup; auto.
    apply InA_eqke_In.
    apply MapFacts.elements_mapsto_iff; auto.
    apply Map.elements_3w.
  Qed.

  Lemma replay_disk_selN_not_In : forall a ms m def,
    ~ Map.In a ms
    -> selN (replay_disk (Map.elements ms) m) a def = selN m a def.
  Proof.
    intros.
    apply replay_disk_selN_other; auto.
    contradict H.
    erewrite MapFacts.elements_in_iff.
    apply in_map_fst_exists_snd in H; destruct H.
    eexists; apply In_InA; eauto.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.

  Lemma replay_disk_add : forall a v ds m,
    replay_disk (Map.elements (Map.add a v ds)) m = updN (replay_disk (Map.elements ds) m) a v.
  Proof.
    intros.
    eapply list_selN_ext.
    autorewrite with lists; auto.
    intros.
    destruct (eq_nat_dec pos a); subst; autorewrite with lists in *.
    rewrite selN_updN_eq by (autorewrite with lists in *; auto).
    apply replay_disk_selN_MapsTo; auto.
    apply Map.add_1; auto.

    rewrite selN_updN_ne by auto.
    case_eq (Map.find pos ds); intros; autorewrite with lists in *.
    (* [pos] is in the transaction *)
    apply replay_disk_selN_MapsTo; auto.
    apply Map.find_2 in H0.
    erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.add_2; auto.
    (* [pos] is not in the transaction *)
    repeat rewrite replay_disk_selN_not_In; auto.
    apply MapFacts.not_find_in_iff; auto.
    apply MapFacts.not_find_in_iff.
    rewrite MapFacts.add_neq_o by auto; auto.
    Unshelve.
    exact $0.
  Qed.


  Lemma entries_valid_replay : forall d ms1 ms2,
    entries_valid ms1 d ->
    entries_valid ms2 d ->
    entries_valid ms1 (replay_disk (Map.elements ms2) d).
  Proof.
    unfold entries_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.

  Lemma entries_valid_add : forall d a v ms,
    entries_valid ms d ->
    a < length d -> a <> 0 ->
    entries_valid (Map.add a v ms) d.
  Proof.
    unfold entries_valid; intros.
    destruct (addr_eq_dec a0 a); subst.
    eauto.
    eapply H.
    eapply Map.add_3; eauto.
  Qed.

  Theorem write_ok : forall xp ms a v,
    {< m1 m2 F v0,
    PRE
      rep xp (ActiveTxn m1 m2) ms * [[ a <> 0 ]] *
      [[[ m2 ::: (F * a |-> v0) ]]]
    POST RET:ms'
      exists m', rep xp (ActiveTxn m1 m') ms' *
      [[[ m' ::: (F * a |-> v) ]]]
    CRASH
      exists m' ms', rep xp (ActiveTxn m1 m') ms'
    >} write xp a v ms.
  Proof.
    unfold write.
    hoare using dems.
    repeat cancel.

    apply entries_valid_add; auto.
    hypmatch replay_disk as Hx.
    apply list2nmem_ptsto_bound in Hx.
    repeat rewrite replay_disk_length in Hx; auto.

    rewrite replay_disk_add.
    pred_apply; repeat cancel.
    eapply list2nmem_updN; eauto.
  Qed.

  Lemma replay_disk_eq : forall a v v' ms d,
    Map.find a ms = Some v ->
    (exists F, F * a |-> v')%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    v = v'.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel with (def := $0) in H0 as Hx.
    rewrite Hx.
    erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.find_2; auto.
    apply list2nmem_ptsto_bound in H0.
    repeat rewrite replay_disk_length in *; auto.
  Qed.

  Lemma replay_disk_eq_none : forall a v v' ms1 ms2 d,
    Map.find a ms1 = None ->
    Map.find a ms2 = Some v ->
    (exists F, F * a |-> v')%pred
      (list2nmem (replay_disk (Map.elements ms1) (replay_disk (Map.elements ms2) d))) ->
    v = v'.
  Proof.
    intros.
    destruct H1.
    eapply list2nmem_sel with (def := $0) in H1 as Hx.
    rewrite Hx.
    rewrite replay_disk_selN_not_In.
    erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.find_2; auto.
    apply list2nmem_ptsto_bound in H1.
    repeat rewrite replay_disk_length in *; auto.
    apply MapFacts.not_find_in_iff; auto.
  Qed.

  Lemma replay_disk_double_none_selN : forall a v ms1 ms2 d def,
    Map.find a ms1 = None ->
    Map.find a ms2 = None ->
    (exists F, F * a |-> v)%pred
      (list2nmem (replay_disk (Map.elements ms1) (replay_disk (Map.elements ms2) d))) ->
    selN d a def = v.
  Proof.
    intros.
    destruct H1.
    eapply list2nmem_sel in H1 as Hx.
    rewrite Hx.
    repeat rewrite replay_disk_selN_not_In; eauto;
    apply MapFacts.not_find_in_iff; auto.
  Qed.

  Lemma synced_data_double_replay_inb : forall a v c1 c2 d,
    (exists F, F * a |-> v)%pred (list2nmem (replay_disk c1 (replay_disk c2 d)))
    -> a < length (synced_list d).
  Proof.
    unfold synced_list; intros.
    destruct H.
    apply list2nmem_ptsto_bound in H.
    autorewrite with lists in *; auto.
  Qed.

  Theorem read_ok: forall xp ms a,
    {< m1 m2 v,
    PRE
      rep xp (ActiveTxn m1 m2) ms *
      [[[ m2 ::: exists F, (F * a |-> v) ]]]
    POST RET:^(ms', r)
      rep xp (ActiveTxn m1 m2) ms' * [[ r = v ]]
    CRASH
      exists ms', rep xp (ActiveTxn m1 m2) ms'
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.

    cancel.
    safestep; auto. eauto.
    repeat cancel; eauto. auto.
    cancel.
    eapply replay_disk_eq; eauto.
    pimpl_crash; cancel; eauto.

    cancel.
    cancel.
    safestep; auto; subst.  eauto. eauto. auto.
    repeat cancel.
    eapply replay_disk_eq_none; eauto.
    pimpl_crash; cancel; auto.

    cancel.
    cancel.
    unfold synced_data; cancel.
    subst; eapply synced_data_double_replay_inb; eauto.

    prestep.
    cancel; subst; auto. cancel.
    unfold synced_list; unfold pred_apply in *.
    rewrite selN_combine by (autorewrite with lists; auto); simpl.
    eapply replay_disk_double_none_selN; [ apply Heqo | apply Heqo0 | pred_apply; cancel].

    pimpl_crash.
    norm.
    cancel.
    instantiate ( 2 := mk_memstate (MSOld ms) (MSCur ms) cs').
    cancel.
    intuition; subst; simpl; eauto.
    pred_apply.
    repeat cancel.
  Qed.

  Definition would_recover_either xp old new :=
    (exists ms,
     rep xp (ActiveTxn old new) ms \/
     rep xp (NoTxn old) ms \/
     rep xp (NoTxn new) ms \/
     rep xp (FlushingTxn old new) ms)%pred.

  Local Hint Unfold would_recover_either : hoare_unfold.

  Lemma replay_disk_is_empty : forall d ms,
    Map.is_empty ms = true -> replay_disk (Map.elements ms) d = d.
  Proof.
    intros.
    apply Map.is_empty_2 in H.
    apply MapProperties.elements_Empty in H.
    rewrite H.
    simpl; auto.
  Qed.

  Lemma is_empty_eq_map0 : forall m,
    Map.is_empty m = true -> Map.Equal m map0.
  Proof.
    unfold map0; intros.
    apply Map.is_empty_2 in H.
    hnf; intros.
    rewrite MapFacts.empty_o.
    apply MapFacts.not_find_in_iff.
    cbv in *; intros.
    destruct H0; eapply H; eauto.
  Qed.

  Lemma replay_mem_map0 : forall m,
    Map.Equal (replay_mem (Map.elements m) map0) m.
  Proof.
    intros; hnf; intro.
    unfold replay_mem.
    rewrite <- Map.fold_1.
    rewrite MapProperties.fold_identity; auto.
  Qed.

  Local Hint Resolve MapFacts.Equal_refl.

  Lemma replay_mem_app' : forall l m,
    Map.Equal (replay_mem ((Map.elements m) ++ l) map0) (replay_mem l m).
  Proof.
    induction l using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite replay_mem_map0; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    rewrite <- IHl; auto.
  Qed.

  Lemma replay_mem_app : forall l2 l m,
    Map.Equal m (replay_mem l map0) ->
    Map.Equal (replay_mem (l ++ l2) map0) (replay_mem l2 m).
  Proof.
    induction l2 using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite H; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    rewrite <- IHl2; auto.
  Qed.

  Lemma map_add_comm : forall A k1 k2 (v1 v2 : A) m,
    k1 <> k2 ->
    Map.Equal (Map.add k1 v1 (Map.add k2 v2 m)) (Map.add k2 v2 (Map.add k1 v1 m)).
  Proof.
    intros; hnf; intro.
    destruct (eq_nat_dec y k1); destruct (eq_nat_dec y k2); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    setoid_rewrite MapFacts.add_eq_o at 2; auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.

  Lemma replay_mem_equal : forall l m1 m2,
    Map.Equal m1 m2 ->
    Map.Equal (replay_mem l m1) (replay_mem l m2).
  Proof.
    induction l; simpl; intros; auto.
    hnf; intro.
    apply IHl.
    apply MapFacts.add_m; auto.
  Qed.

  Lemma replay_mem_add : forall l k v m,
    ~ KIn (k, v) l -> KNoDup l ->
    Map.Equal (replay_mem l (Map.add k v m)) (Map.add k v (replay_mem l m)).
  Proof.
    induction l; simpl; intros; auto.
    destruct a; simpl.
    rewrite <- IHl.
    apply replay_mem_equal.
    apply map_add_comm.
    contradict H; inversion H0; subst.
    constructor; hnf; simpl; auto.
    contradict H.
    apply InA_cons.
    right; auto.
    inversion H0; auto.
  Qed.

  Lemma In_fst_KIn : forall V a (l : list (Map.key * V)),
    In (fst a) (map fst l) -> KIn a l.
  Proof.
    intros; destruct a; simpl in *.
    eapply in_selN_exists in H.
    do 2 destruct H.
    rewrite map_length in H.
    apply InA_alt.
    eexists; split.
    2: apply in_selN_map; eauto.
    rewrite H0.
    hnf; auto.
    Unshelve.
    all : eauto.
  Qed.


  Lemma In_map_fst_MapIn : forall elt k m,
    In k (map fst (Map.elements (elt:=elt) m)) <-> Map.In k m.
  Proof.
    intros; split; intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply MapFacts.elements_in_iff.
    exists x.
    apply In_InA; auto.
    apply MapFacts.elements_in_iff in H.
    destruct H.
    apply InA_alt in H.
    destruct H; intuition.
    hnf in H0; simpl in *; intuition; subst.
    destruct x0; simpl in *.
    generalize dependent (Map.elements m).
    induction l; intros; simpl; auto.
    inversion H1; intuition.
    destruct a; inversion H.
    tauto.
  Qed.


  Lemma In_replay_mem_mem0 : forall l k,
    KNoDup l ->
    In k (map fst (Map.elements (replay_mem l map0))) ->
    In k (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl in *.
    destruct (addr_eq_dec k0 k).
    left; auto.
    right.
    inversion H; subst.
    apply In_map_fst_MapIn in H0.
    rewrite replay_mem_add in H0 by auto.
    apply MapFacts.add_neq_in_iff in H0; auto.
    apply IHl; auto.
    apply In_map_fst_MapIn; auto.
  Qed.

  Lemma replay_disk_replay_mem : forall l d,
    KNoDup l ->
    replay_disk l d = replay_disk (Map.elements (elt:=valu) (replay_mem l map0)) d.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; inversion H; subst; simpl.
    rewrite IHl by auto.
    rewrite replay_disk_updN_comm.
    rewrite <- replay_disk_add.
    f_equal; apply eq_sym.
    apply mapeq_elements.
    apply replay_mem_add; auto.
    contradict H2.
    apply In_fst_KIn; simpl.
    apply In_replay_mem_mem0; auto.
  Qed.

  Lemma replay_disk_merge' : forall l1 l2 d,
    KNoDup l1 -> KNoDup l2 ->
    replay_disk l2 (replay_disk l1 d) =
    replay_disk (Map.elements (replay_mem l2 (replay_mem l1 map0))) d.
  Proof.
    induction l1; intros; simpl.
    induction l2; simpl; auto.
    inversion H0; subst.
    erewrite mapeq_elements.
    2: apply replay_mem_add; destruct a; auto.
    rewrite replay_disk_add.
    rewrite <- IHl2 by auto.
    apply replay_disk_updN_comm.
    contradict H3.
    apply In_fst_KIn; auto.

    induction l2; destruct a; simpl; auto.
    inversion H; simpl; subst.
    erewrite mapeq_elements.
    2: apply replay_mem_add; auto.
    rewrite replay_disk_add.
    rewrite replay_disk_updN_comm.
    f_equal.

    apply replay_disk_replay_mem; auto.
    contradict H3.
    apply In_fst_KIn; auto.

    destruct a0; simpl in *.
    inversion H; inversion H0; simpl; subst.
    rewrite replay_disk_updN_comm.
    rewrite IHl2 by auto.
    rewrite <- replay_disk_add.
    f_equal.
    apply eq_sym.
    apply mapeq_elements.
    apply replay_mem_add; auto.
    contradict H7.
    apply In_fst_KIn; simpl; auto.
  Qed.


  Lemma replay_disk_merge : forall m1 m2 d,
    replay_disk (Map.elements m2) (replay_disk (Map.elements m1) d) =
    replay_disk (Map.elements (map_merge m1 m2)) d.
  Proof.
    intros.
    unfold map_merge.
    setoid_rewrite mapeq_elements at 3.
    2: eapply replay_mem_equal with (m2 := m1); auto.
    rewrite replay_disk_merge' by (apply Map.elements_3w).
    f_equal.
    apply mapeq_elements.
    apply replay_mem_equal.
    apply replay_mem_map0.
  Qed.

  Lemma replay_mem_not_in' : forall l a v ms,
    KNoDup l ->
    ~ In a (map fst l) ->
    Map.MapsTo a v (replay_mem l ms) ->
    Map.MapsTo a v ms.
  Proof.
    induction l; intros; auto.
    destruct a; simpl in *; intuition.
    apply IHl; auto.
    inversion H; subst; auto.
    rewrite replay_mem_add in H1.
    apply Map.add_3 in H1; auto.
    inversion H; auto.
    inversion H; auto.
  Qed.

  Lemma replay_mem_not_in : forall a v ms m,
    Map.MapsTo a v (replay_mem (Map.elements m) ms) ->
    ~ Map.In a m ->
    Map.MapsTo a v ms.
  Proof.
    intros.
    eapply replay_mem_not_in'; eauto.
    apply Map.elements_3w.
    contradict H0.
    apply In_map_fst_MapIn; auto.
  Qed.


  Lemma entries_valid_replay_mem : forall d ms1 ms2,
    entries_valid ms1 d ->
    entries_valid ms2 d ->
    entries_valid (replay_mem (Map.elements ms1) ms2) d.
  Proof.
    unfold entries_valid; intros.
    destruct (MapFacts.In_dec ms1 a).
    apply MapFacts.in_find_iff in i.
    destruct (Map.find a ms1) eqn:X.
    eapply H.
    apply MapFacts.find_mapsto_iff; eauto.
    tauto.
    eapply H0.
    eapply replay_mem_not_in; eauto.
  Qed.

  Hint Extern 0 (okToUnify (synced_data ?a _) (synced_data ?a _)) => constructor : okToUnify.

  Theorem commit_ok: forall xp ms,
    {< m1 m2,
     PRE            rep xp (ActiveTxn m1 m2) ms
     POST RET:^(ms',r)
                    ([[ r = true ]] * rep xp (NoTxn m2) ms') \/
                    ([[ r = false ]] * rep xp (NoTxn m1) ms')
     CRASH          would_recover_either xp m1 m2
    >} commit xp ms.
  Proof.
    unfold commit.
    step using dems.
    step using dems.
    or_l.
    cancel; auto.
    apply replay_disk_is_empty; auto.
    apply is_empty_eq_map0; auto.

    hoare using dems.
    or_l.
    cancel; unfold map_merge.
    rewrite replay_mem_app; eauto.

    apply entries_valid_replay_mem; auto.
    apply replay_disk_merge.

    (* crashes *)
    cancel.
    or_l; norm.
    instantiate (ms0 := mk_memstate (MSOld ms) (MSCur ms) cs').
    cancel. intuition; simpl; eauto.
    pred_apply; cancel.

    or_r; or_r; or_r.
    norm. cancel.
    instantiate (ms1 := mk_memstate (MSOld ms) (MSCur ms) cs').
    cancel. intuition; simpl; eauto.
    pred_apply; cancel.
    instantiate ( 1 := F); cancel.
    or_l; auto.

    or_r; or_r; or_r.
    norm. cancel.
    instantiate (ms2 := mk_memstate (MSOld ms) (MSCur ms) cs').
    cancel. intuition; simpl; eauto.
    pred_apply; cancel.
    instantiate ( 1 := F); cancel.
    or_r; auto.

    or_r; or_r; or_l; norm.
    instantiate (ms3 := mk_memstate (map_merge (MSOld ms) (MSCur ms)) map0 cs').
    cancel. simpl; intuition; eauto.
    unfold map_merge.
    rewrite replay_mem_app; eauto.
    apply entries_valid_replay_mem; eauto.
    pred_apply; cancel.
    apply replay_disk_merge.
  Qed.


  Lemma entries_valid_Forall_fst_synced : forall d ms,
    entries_valid ms d ->
    Forall (fun e => fst e < length (synced_list d)) (Map.elements ms).
  Proof.
    unfold entries_valid, synced_list; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    destruct x; simpl.
    apply (H n w).
    apply Map.elements_2.
    apply In_InA; auto.
  Qed.
  Local Hint Resolve entries_valid_Forall_fst_synced.

  Lemma entries_valid_Forall_synced_map_fst : forall d ms,
    entries_valid ms d ->
    Forall (fun e => e < length (synced_list d)) (map fst (Map.elements ms)).
  Proof.
    unfold entries_valid, synced_list; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    apply In_map_fst_MapIn in H0.
    apply MapFacts.elements_in_iff in H0.
    destruct H0.
    eapply (H x).
    apply Map.elements_2; eauto.
  Qed.

  Lemma vssync_synced : forall l a,
    snd (selN l a ($0, nil)) = nil ->
    vssync l a = l.
  Proof.
    unfold vssync; induction l; intros; auto.
    destruct a0; simpl in *.
    destruct a; simpl in *.
    rewrite <- H; auto.
    f_equal.
    rewrite IHl; auto.
  Qed.

  Lemma vsupd_comm : forall l a1 v1 a2 v2,
    a1 <> a2 ->
    vsupd (vsupd l a1 v1) a2 v2 = vsupd (vsupd l a2 v2) a1 v1.
  Proof.
    unfold vsupd; intros.
    rewrite updN_comm by auto.
    repeat rewrite selN_updN_ne; auto.
  Qed.

  Lemma vsupd_vecs_vsupd_notin : forall av l a v,
    ~ In a (map fst av) ->
    vsupd_vecs (vsupd l a v) av = vsupd (vsupd_vecs l av) a v.
  Proof.
    induction av; simpl; intros; auto.
    destruct a; simpl in *; intuition.
    rewrite <- IHav by auto.
    rewrite vsupd_comm; auto.
  Qed.

  Lemma vssync_vsupd_eq : forall l a v,
    vssync (vsupd l a v) a = updN l a (v, nil).
  Proof.
    unfold vsupd, vssync, vsmerge; intros.
    rewrite updN_twice.
    destruct (lt_dec a (length l)).
    rewrite selN_updN_eq; simpl; auto.
    rewrite selN_oob.
    repeat rewrite updN_oob; auto.
    omega. omega.
    autorewrite with lists; omega.
  Qed.

  Lemma updN_vsupd_vecs_notin : forall av l a v,
    ~ In a (map fst av) ->
    updN (vsupd_vecs l av) a v = vsupd_vecs (updN l a v) av.
  Proof.
    induction av; simpl; intros; auto.
    destruct a; simpl in *; intuition.
    rewrite IHav by auto.
    unfold vsupd, vsmerge.
    rewrite updN_comm by auto.
    rewrite selN_updN_ne; auto.
  Qed.

  Lemma synced_list_updN : forall l a v,
    updN (synced_list l) a (v, nil) = synced_list (updN l a v).
  Proof.
    unfold synced_list; induction l; simpl; intros; auto.
    destruct a0; simpl; auto.
    rewrite IHl; auto.
  Qed.


  Lemma apply_synced_data_ok' : forall l d,
    NoDup (map fst l) ->
    vssync_vecs (vsupd_vecs (synced_list d) l) (map fst l) = synced_list (replay_disk l d).
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl.
    inversion H; subst.
    rewrite <- IHl by auto.

    rewrite vsupd_vecs_vsupd_notin by auto.
    rewrite vssync_vsupd_eq.
    rewrite updN_vsupd_vecs_notin by auto.
    rewrite synced_list_updN.
    auto.
  Qed.


  Lemma apply_synced_data_ok : forall xp m d,
    arrayN (DataStart xp) (vssync_vecs (vsupd_vecs (synced_list d) (Map.elements m)) (map_keys m))
    =p=> synced_data xp (replay_disk (Map.elements m) d).
  Proof.
    unfold synced_data; intros.
    apply arrayN_unify.
    apply apply_synced_data_ok'.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.

  Theorem apply_ok: forall xp ms,
    {< m,
    PRE
      rep xp (NoTxn m) ms
    POST RET:ms
      rep xp (NoTxn m) ms
    CRASH
      exists ms', rep xp (NoTxn m) ms' \/
                  rep xp (NoTxnApplying m) ms'
    >} apply xp ms.
  Proof.
    unfold apply; intros.
    step.
    unfold synced_data; cancel.

    step.
    rewrite vsupd_vecs_length.
    apply entries_valid_Forall_synced_map_fst; auto.

    step.
    step.
    rewrite apply_synced_data_ok; cancel.

    (* crash conditions *)
    
    
  Qed.
    
  
  
End LOG.




Module LOG.

  Definition header_type := Rec.RecF ([("length", Rec.WordF addrlen)]).
  Definition header := Rec.data header_type.
  Definition mk_header (len : nat) : header := ($ len, tt).

  Theorem header_sz_ok : Rec.len header_type <= valulen.
  Proof.
    rewrite valulen_is. apply leb_complete. compute. trivial.
  Qed.

  Theorem plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
  Proof.
    apply le_plus_minus_r; apply header_sz_ok.
  Qed.

  Definition header_to_valu (h : header) : valu.
    set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
    rewrite plus_minus_header in r.
    refine r.
  Defined.
  Arguments header_to_valu : simpl never.

  Definition valu_to_header (v : valu) : header.
    apply Rec.of_word.
    rewrite <- plus_minus_header in v.
    refine (split1 _ _ v).
  Defined.

  Definition header_valu_id : forall h,
    valu_to_header (header_to_valu h) = h.
  Proof.
    unfold valu_to_header, header_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- plus_minus_header.
    unfold zext.
    autorewrite with core.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.

  
  Definition addr_per_block := valulen / addrlen.
  Definition descriptor_type := Rec.ArrayF (Rec.WordF addrlen) addr_per_block.
  Definition descriptor := Rec.data descriptor_type.
  Theorem descriptor_sz_ok : valulen = Rec.len descriptor_type.
  Proof.
    simpl. unfold addr_per_block. rewrite valulen_is. vm_compute. reflexivity.
  Qed.

  Definition descriptor_to_valu (d : descriptor) : valu.
    rewrite descriptor_sz_ok.
    apply Rec.to_word; auto.
  Defined.
  Arguments descriptor_to_valu : simpl never.

  Definition valu_to_descriptor (v : valu) : descriptor.
    rewrite descriptor_sz_ok in v.
    apply Rec.of_word; auto.
  Defined.

  Theorem valu_descriptor_id : forall v,
    descriptor_to_valu (valu_to_descriptor v) = v.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Rec.to_of_id.
    rewrite <- descriptor_sz_ok.
    autorewrite with core.
    trivial.
  Qed.

  Theorem descriptor_valu_id : forall d,
    Rec.well_formed d -> valu_to_descriptor (descriptor_to_valu d) = d.
  Proof.
    unfold descriptor_to_valu, valu_to_descriptor.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite descriptor_sz_ok.
    autorewrite with core.
    apply Rec.of_to_id; auto.
  Qed.

  Theorem valu_to_descriptor_length : forall v,
    length (valu_to_descriptor v) = addr_per_block.
  Proof.
    unfold valu_to_descriptor.
    intros.
    pose proof (@Rec.of_word_length descriptor_type).
    unfold Rec.well_formed in H.
    simpl in H.
    apply H.
  Qed.
  Hint Resolve valu_to_descriptor_length.

  Lemma descriptor_to_valu_zeroes: forall l n,
    descriptor_to_valu (l ++ repeat $0 n) = descriptor_to_valu l.
  Proof.
    unfold descriptor_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite descriptor_sz_ok.
    autorewrite with core.
    apply Rec.to_word_append_zeroes.
  Qed.

  Definition indomain' (a : addr) (m : diskstate) := wordToNat a < length m.

  (* Check that the state is well-formed *)
  Definition valid_entries m (ms : memstate) :=
    forall a v, Map.MapsTo a v ms -> indomain' a m.

  Definition valid_size xp (ms : memstate) :=
    Map.cardinal ms <= wordToNat (LogLen xp).

  Theorem valid_entries_empty : forall m, valid_entries m ms_empty.
  Proof.
    unfold valid_entries; intros.
    apply MapFacts.empty_mapsto_iff in H. intuition.
  Qed.

  Theorem valid_size_empty : forall xp, valid_size xp ms_empty.
  Proof.
    unfold valid_size; intros.
    rewrite MapProperties.cardinal_1 by apply Map.empty_1. omega.
  Qed.

  Hint Resolve valid_entries_empty.
  Hint Resolve valid_size_empty.

  (* Replay the state in memory *)
  Definition replay' V (l : list (addr * V)) (m : list V) : list V :=
    fold_left (fun m' p => upd m' (fst p) (snd p)) l m.

  Definition replay (ms : memstate) (m : diskstate) : diskstate :=
    replay' (Map.elements ms) m.

  Theorem replay_empty : forall d, replay ms_empty d = d.
  Proof.
    unfold replay.
    rewrite MapProperties.elements_empty.
    reflexivity.
  Qed.

  Hint Rewrite replay_empty.

  Lemma replay'_upd : forall V l d a (v : V),
    upd (replay' l (upd d a v)) a v = upd (replay' l d) a v.
  Proof.
    induction l; simpl; intros.
    autorewrite with core; auto.
    destruct (weq a0 (fst a)); subst.
    - repeat rewrite upd_twice. auto.
    - rewrite upd_comm by auto. rewrite IHl. auto.
  Qed.

  Lemma replay'_upd_elim : forall V l d a (v : V),
    In a (map fst l)
    -> replay' l (upd d a v) = replay' l d.
  Proof.
    induction l; simpl; intuition.
    rewrite H0; autorewrite with core; auto.
    simpl; destruct (weq a a0); subst.
    rewrite upd_twice; auto.
    rewrite upd_comm by auto.
    erewrite IHl; eauto.
  Qed.

  Lemma replay'_upd_comm : forall V l d a (v : V),
    ~ In a (map fst l)
    -> replay' l (upd d a v) = upd (replay' l d) a v.
  Proof.
    induction l; simpl; intuition; simpl in *.
    rewrite upd_comm by auto.
    apply IHl; auto.
  Qed.

  Theorem replay_twice : forall m d, replay m (replay m d) = replay m d.
  Proof.
    unfold replay.
    intro m; generalize (Map.elements m); clear m.
    induction l; simpl; auto; intros.
    destruct (In_dec (@weq addrlen) (fst a) (map fst l)).
    repeat rewrite replay'_upd_elim by auto.
    apply IHl.
    rewrite <- replay'_upd_comm by auto.
    rewrite upd_twice.
    apply IHl.
  Qed.

  Definition avail_region start len : @pred addr (@weq addrlen) valuset :=
    (exists l, [[ length l = len ]] * array start l $1)%pred.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start len =p=>
       start |->? * avail_region (start ^+ $1) (len - 1).
  Proof.
    destruct len; intros; try omega.
    unfold avail_region.
    norm'l; unfold stars; simpl.
    destruct l; simpl in *; try congruence.
    cancel.
  Qed.

  Lemma avail_region_grow_all : forall fsxp m,
    valid_size fsxp m ->
    array (LogData fsxp)
      (List.combine (map snd (Map.elements (elt:=valu) m))
         (repeat [] (length (map snd (Map.elements (elt:=valu) m))))) $ (1) *
    avail_region (LogData fsxp ^+ $ (Map.cardinal (elt:=valu) m))
      (# (LogLen fsxp) - Map.cardinal (elt:=valu) m) =p=>
    avail_region (LogData fsxp) # (LogLen fsxp).
  Proof.
    unfold valid_size, avail_region.
    intros; norm; unfold stars; simpl.
    instantiate (a := (List.combine (map snd (Map.elements m))
                        (repeat [] (length (map snd (Map.elements m))))) ++ l).
    rewrite <- array_app.
    cancel.
    rewrite combine_length. autorewrite with core.
    rewrite Map.cardinal_1. auto.
    intuition.
    autorewrite with core. rewrite combine_length. autorewrite with core.
    rewrite Map.cardinal_1 in *. omega.
  Qed.

  Definition synced_list m: list valuset := List.combine m (repeat nil (length m)).

  Lemma length_synced_list : forall l,
    length (synced_list l) = length l.
  Proof.
    unfold synced_list; intros.
    rewrite combine_length. autorewrite with core. auto.
  Qed.

  Definition data_rep (xp: log_xparams) (m: list valuset) : @pred addr (@weq addrlen) valuset :=
    array (DataStart xp) m $1.

  (** On-disk representation of the log *)
  Definition log_rep xp m (ms : memstate) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest,
      (LogDescriptor xp) |=> (descriptor_to_valu (map fst (Map.elements ms) ++ rest)) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      array (LogData xp) (synced_list (map snd (Map.elements ms))) $1 *
      avail_region (LogData xp ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms))%pred.

  (* XXX DRY? *)
  Definition log_rep_unsynced xp m (ms : memstate) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_entries m ms ]] *
      [[ valid_size xp ms ]] *
      exists rest others,
      (LogDescriptor xp) |-> (descriptor_to_valu (map fst (Map.elements ms) ++ rest),
                              map descriptor_to_valu others) *
      [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]] *
      exists unsynced,
      array (LogData xp) (List.combine (map snd (Map.elements ms)) unsynced) $1 *
      [[ length unsynced = Map.cardinal ms ]] *
      avail_region (LogData xp ^+ $ (Map.cardinal ms))
                         (wordToNat (LogLen xp) - Map.cardinal ms) *
      [[ Forall (@Rec.well_formed descriptor_type) others ]])%pred.

  Definition log_rep_empty xp : @pred addr (@weq addrlen) valuset :=
     (exists rest,
      (LogDescriptor xp) |=> descriptor_to_valu rest *
      [[ @Rec.well_formed descriptor_type (rest) ]] *
      avail_region (LogData xp) (wordToNat (LogLen xp)))%pred.

  Definition cur_rep (old : diskstate) (ms : memstate) (cur : diskstate) : @pred addr (@weq addrlen) valuset :=
    [[ cur = replay ms old ]]%pred.

  Definition nil_unless_in (ms: list addr) (l: list (list valu)) :=
    forall a, ~ In a ms -> sel l a nil = nil.

  Definition equal_unless_in T (ms: list addr) (m1: list T) (m2: list T) (def: T) :=
    length m1 = length m2 /\ forall n, (~ goodSize addrlen n \/ ~ In ($ n) ms) -> selN m1 n def = selN m2 n def.

  Definition rep_inner xp (st: logstate) (ms: memstate) :=
    (* For now, support just one descriptor block, at the start of the log. *)
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
     (* The log shouldn't overflow past the end of disk *)
     [[ goodSize addrlen (# (LogData xp) + # (LogLen xp)) ]] *
    match st with
    | NoTransaction m =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * [[ Map.Equal ms ms_empty ]]
    * data_rep xp (synced_list m)
    * log_rep_empty xp

    | ActiveTxn old cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * data_rep xp (synced_list old) (* Transactions are always completely buffered in memory. *)
    * log_rep_empty xp
    * cur_rep old ms cur
    * [[ valid_entries old ms ]]

    | FlushedUnsyncTxn old cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * data_rep xp (synced_list old)
    * log_rep_unsynced xp old ms
    * cur_rep old ms cur

    | FlushedTxn old cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header 0))
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur

    | CommittedUnsyncTxn old cur =>
      (LogHeader xp) |-> (header_to_valu (mk_header (Map.cardinal ms)), header_to_valu (mk_header 0) :: nil)
    * data_rep xp (synced_list old)
    * log_rep xp old ms
    * cur_rep old ms cur

    | CommittedTxn cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header (Map.cardinal ms)))
    * exists old d, data_rep xp d
      (* If something's in the transaction, it doesn't matter what state it's in on disk *)
    * [[ equal_unless_in (map fst (Map.elements ms)) (synced_list old) d ($0, nil) ]]
    * log_rep xp old ms
    * cur_rep old ms cur

    | AppliedUnsyncTxn cur =>
      (LogHeader xp) |=> (header_to_valu (mk_header (Map.cardinal ms)))
    * exists old old_unflushed, data_rep xp (List.combine cur old_unflushed)
    * [[ length cur = length old_unflushed ]]
    * [[ nil_unless_in (map fst (Map.elements ms)) old_unflushed ]]
    * log_rep xp old ms
    * cur_rep old ms cur

    | AppliedTxn cur =>
      (LogHeader xp) |-> (header_to_valu (mk_header 0), header_to_valu (mk_header (Map.cardinal ms)) :: nil)
    * data_rep xp (synced_list cur)
    * exists old, log_rep xp old ms
    * cur_rep old ms cur

    end)%pred.

  Definition rep xp F st mscs := let '^(ms, cs) := mscs in (exists d,
    BUFCACHE.rep cs d * [[ (F * rep_inner xp st ms)%pred d ]])%pred.

  Ltac log_unfold := unfold rep, rep_inner, data_rep, cur_rep, log_rep, log_rep_empty, log_rep_unsynced, valid_size, synced_list.

  Lemma mapeq_elements : forall V m1 m2,
    @Map.Equal V m1 m2 -> Map.elements m1 = Map.elements m2.
  Proof.
    intros.
    apply MapOrdProperties.elements_Equal_eqlistA in H.
    generalize dependent (Map.elements m2).
    generalize dependent (Map.elements m1).
    induction l.
    - intros. inversion H. reflexivity.
    - intros. destruct l0; inversion H.
      inversion H3. destruct a; destruct p; simpl in *; subst.
      f_equal; eauto.
  Qed.

  Create HintDb mapeq.

  Lemma mapeq_replay_eq : forall m1 m2 l,
    Map.Equal m1 m2 -> replay m1 l = replay m2 l.
  Proof.
    unfold replay, replay'.
    intros.
    erewrite mapeq_elements; eauto.
  Qed.
  Hint Resolve mapeq_replay_eq : mapeq.

  Lemma valid_entries_mapeq : forall m1 m2 l,
    Map.Equal m1 m2 -> valid_entries l m1 -> valid_entries l m2.
  Proof.
    unfold valid_entries.
    intros.
    eapply MapFacts.Equal_mapsto_iff in H.
    eapply H0.
    eapply H; eauto.
  Qed.
  Hint Resolve valid_entries_mapeq : mapeq.

  Lemma mapeq_rep : forall xp s m1 m2,
    Map.Equal m2 m1 -> rep_inner xp s m1 =p=> rep_inner xp s m2.
  Proof.
    intros; log_unfold.
    apply MapFacts.Equal_sym in H.
    generalize H; intro He.
    apply mapeq_elements in He.
    repeat rewrite Map.cardinal_1.
    rewrite He.
    case s; cancel; eauto with mapeq.
  Qed.

  Definition init T xp cs rx : prog T :=
    cs <- BUFCACHE.write (LogHeader xp) (header_to_valu (mk_header 0)) cs;
    cs <- BUFCACHE.write (LogDescriptor xp) (descriptor_to_valu (repeat $0 addr_per_block)) cs;
    cs <- BUFCACHE.sync (LogHeader xp) cs;
    cs <- BUFCACHE.sync (LogDescriptor xp) cs;
    rx ^(ms_empty, cs).


  Hint Extern 0 (okToUnify (log_rep _ _ _) (log_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (cur_rep _ _ _) (cur_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (data_rep _ _) (data_rep _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (rep_inner _ _ _) (rep_inner _ _ _)) => constructor : okToUnify.

  (* XXX actually okay? *)
  Local Hint Extern 0 (okToUnify (array (DataStart _) _ _) (array (DataStart _) _ _)) => constructor : okToUnify.

  Definition log_uninitialized xp old :=
    ([[ wordToNat (LogLen xp) <= addr_per_block ]] *
     [[ goodSize addrlen (# (LogData xp) + # (LogLen xp)) ]] *
     data_rep xp (synced_list old) *
     avail_region (LogData xp) (wordToNat (LogLen xp)) *
     (LogDescriptor xp) |->? *
     (LogHeader xp) |->?)%pred.

  (* XXX remove once SepAuto and SepAuto2 are unified *)
  Hint Extern 0 (okToUnify (BUFCACHE.rep _ _) (BUFCACHE.rep _ _)) => constructor : okToUnify.

  Definition unifiable_array := @array valuset.

  Hint Extern 0 (okToUnify (unifiable_array _ _ _) (unifiable_array _ _ _)) => constructor : okToUnify.

  Theorem init_ok : forall xp cs,
    {< old d F,
    PRE
      BUFCACHE.rep cs d * [[ (F * log_uninitialized xp old)%pred d ]]
    POST RET:mscs
      rep xp F (NoTransaction old) mscs
    CRASH
      exists cs' d', BUFCACHE.rep cs' d' * [[ (F * log_uninitialized xp old)%pred d' ]]
    >} init xp cs.
  Proof.
    unfold init, log_uninitialized; log_unfold.
    hoare.
    rewrite Forall_forall; intuition.
  Qed.

  Hint Extern 1 ({{_}} progseq (init _ _) _) => apply init_ok : prog.

  Definition begin T (xp : log_xparams) (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    rx ^(ms_empty, cs).

  Theorem begin_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (NoTransaction m) mscs
    POST RET:r
      rep xp F (ActiveTxn m m) r
    CRASH
      exists mscs', rep xp F (NoTransaction m) mscs' \/ rep xp F (ActiveTxn m m) mscs'
    >} begin xp mscs.
  Proof.
    unfold begin; log_unfold.
    hoare.
    apply pimpl_or_r; left.
    cancel.
    eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (begin _ _) _) => apply begin_ok : prog.

  Definition abort T (xp : log_xparams) (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    rx ^(ms_empty, cs).

  Theorem abort_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs
    POST RET:r
      rep xp F (NoTransaction m1) r
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs' \/ rep xp F (NoTransaction m1) mscs'
    >} abort xp mscs.
  Proof.
    unfold abort; log_unfold.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (abort _ _) _) => apply abort_ok : prog.

  Ltac word2nat_clear := try clear_norm_goal; repeat match goal with
    | [ H : forall _, {{ _ }} _ |- _ ] => clear H
    | [ H : _ =p=> _ |- _ ] => clear H
    end.

  Lemma skipn_1_length': forall T (l: list T),
    length (match l with [] => [] | _ :: l' => l' end) = length l - 1.
  Proof.
    destruct l; simpl; omega.
  Qed.

  Hint Rewrite app_length firstn_length skipn_length combine_length map_length repeat_length length_upd
    skipn_1_length' : lengths.

  Ltac solve_lengths' :=
    repeat (progress (autorewrite with lengths; repeat rewrite Nat.min_l by solve_lengths'; repeat rewrite Nat.min_r by solve_lengths'));
    simpl; try word2nat_solve.

  Ltac solve_lengths_prepare :=
    intros; word2nat_clear; simpl;
    (* Stupidly, this is like 5x faster than [rewrite Map.cardinal_1 in *] ... *)
    repeat match goal with
    | [ H : context[Map.cardinal] |- _ ] => rewrite Map.cardinal_1 in H
    | [ |- context[Map.cardinal] ] => rewrite Map.cardinal_1
    end.

  Ltac solve_lengths_prepped :=
    try (match goal with
      | [ |- context[{{ _ }} _] ] => fail 1
      | [ |- _ =p=> _ ] => fail 1
      | _ => idtac
      end;
      word2nat_clear; word2nat_simpl; word2nat_rewrites; solve_lengths').

  Ltac solve_lengths := solve_lengths_prepare; solve_lengths_prepped.


  Definition KIn V := InA (@Map.eq_key V).
  Definition KNoDup V := NoDupA (@Map.eq_key V).

  Lemma replay'_sel_other : forall l d a (def : valu),
    ~ In a (map fst l)
    -> NoDup (map fst l)
    -> sel (replay' l d) a def = sel d a def.
  Proof.
    induction l; simpl; intuition; simpl in *.
    inversion H0; subst; auto.
    rewrite replay'_upd_comm by auto.
    rewrite sel_upd_ne by auto.
    apply IHl; auto.
  Qed.

  Lemma in_map_fst_exists_snd : forall A B (l : list (A * B)) a,
    In a (map fst l) -> exists b, In (a, b) l.
  Proof.
    induction l; simpl; firstorder.
    destruct a; simpl in *; subst; eauto.
  Qed.

  Local Hint Resolve MapProperties.eqke_equiv.

  Lemma KNoDup_NoDup: forall V (l : list (addr * V)),
    KNoDup l -> NoDup (map fst l).
  Proof.
    induction l; simpl; intros; constructor.
    inversion H; subst.
    contradict H2.
    apply in_map_fst_exists_snd in H2; destruct H2.
    apply InA_alt.
    exists (fst a, x); intuition.
    destruct a; simpl in *.
    cbv; auto.
    inversion H; subst.
    apply IHl; auto.
  Qed.

  Lemma map_fst_nodup: forall (ms : memstate),
    NoDup (map fst (Map.elements ms)).
  Proof.
    intros.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.

  Local Hint Resolve map_fst_nodup.

  Lemma replay_sel_other : forall a ms m def,
    ~ Map.In a ms
    -> selN (replay ms m) (wordToNat a) def = selN m (wordToNat a) def.
  Proof.
    intros.
    apply replay'_sel_other; auto.
    contradict H.
    erewrite MapFacts.elements_in_iff.
    apply in_map_fst_exists_snd in H; destruct H.
    eexists; apply In_InA; eauto.
  Qed.

  Lemma replay'_length : forall V (l:list (addr * V)) (m:list V),
    length (replay' l m) = length m.
  Proof.
    induction l; simpl; intros; auto.
    destruct (In_dec (@weq addrlen) (fst a) (map fst l)).
    rewrite replay'_upd_elim by auto.
    apply IHl; auto.
    rewrite replay'_upd_comm by auto.
    rewrite length_upd.
    apply IHl; auto.
  Qed.

  Hint Rewrite replay'_length : lengths.

  Lemma replay'_sel_in' : forall V l d a (v def : V),
    In (a, v) l -> NoDup (map fst l) -> # a < length d
    -> sel (replay' l d) a def = v.
  Proof.
    induction l; simpl; intros; auto.
    inversion H.
    inversion H0; subst.
    destruct a; intuition; simpl.
    inversion H2; subst.
    rewrite replay'_upd_comm by auto.
    rewrite sel_upd_eq; auto.
    erewrite replay'_length; auto.
    simpl in *.
    apply IHl; auto.
    rewrite length_upd; auto.
  Qed.

  Lemma replay'_sel_in : forall V a (v: V) l m def,
    KNoDup l -> In (a, v) l -> # a < length m
    -> sel (replay' l m) a def = v.
  Proof.
    intros.
    eapply replay'_sel_in'; eauto.
    apply KNoDup_NoDup; auto.
  Qed.


  Lemma InA_eqke_In : forall V a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
  Proof.
    induction l; intros; auto; inversion H; subst.
    inversion H1.
    destruct a0; simpl in *; subst; auto.
    simpl. right.
    apply IHl; auto.
  Qed.

  Lemma replay_sel_in : forall a v ms m def,
    # a < length m -> Map.MapsTo a v ms
    -> selN (replay ms m) (wordToNat a) def = v.
  Proof.
    intros.
    apply replay'_sel_in; auto.
    apply Map.elements_3w.
    apply InA_eqke_In.
    apply MapFacts.elements_mapsto_iff; auto.
  Qed.

  Lemma replay_length : forall ms m,
    length (replay ms m) = length m.
  Proof.
    intros.
    unfold replay.
    rewrite replay'_length; auto.
  Qed.

  Hint Rewrite replay_length : lengths.

  Lemma replay'_sel_invalid : forall V a (l : list (addr * V)) d def,
    ~ goodSize addrlen a
    -> selN (replay' l d) a def = selN d a def.
  Proof.
    intros; unfold goodSize in *.
    destruct (lt_dec a (length d)).

    unfold replay'.
    revert d l0.
    induction l; simpl; intros; auto.
    destruct a0; simpl.
    rewrite IHl.
    unfold upd; rewrite selN_updN_ne; auto.
    contradict H.
    word2nat_auto.
    rewrite length_upd; auto.
    repeat rewrite (selN_oob); auto; try omega.
    rewrite replay'_length; omega.
  Qed.

  Lemma replay_sel_invalid : forall a ms d def,
    ~ goodSize addrlen a
    -> selN (replay ms d) a def = selN d a def.
  Proof.
    unfold replay; intros.
    apply replay'_sel_invalid; auto.
  Qed.

  Lemma valid_entries_replay : forall m d,
    valid_entries d m ->
    valid_entries (replay m d) m.
  Proof.
    unfold valid_entries, indomain', replay. intros.
    apply H in H0.
    rewrite replay'_length; auto.
  Qed.

  Hint Resolve valid_entries_replay.

  Lemma replay_add : forall a v ms m,
    replay (Map.add a v ms) m = upd (replay ms m) a v.
  Proof.
    intros.
    (* Let's show that the lists are equal because [sel] at any index [pos] gives the same valu *)
    eapply list_selN_ext.
    autorewrite with core.
    solve_lengths.
    intros.
    destruct (lt_dec pos (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace pos with (wordToNat (natToWord addrlen (pos))) by word2nat_auto.
      destruct (weq ($ pos) a).
      + (* [pos] is [a], the address we're updating *)
        erewrite replay_sel_in.
        reflexivity.
        autorewrite with lengths in *.
        solve_lengths.
        instantiate (default := $0).
        subst.
        unfold upd.
        rewrite selN_updN_eq.
        apply Map.add_1.
        trivial.
        rewrite replay_length in *.
        word2nat_auto.

      + (* [pos] is another address *)
        unfold upd.
        rewrite selN_updN_ne by word2nat_auto.

        case_eq (Map.find $ pos ms).

        (* [pos] is in the transaction *)
        intros w Hf.
        autorewrite with lengths in *.
        erewrite replay_sel_in.
        reflexivity.
        solve_lengths.
        apply Map.find_2 in Hf.
        erewrite replay_sel_in.
        apply Map.add_2.
        unfold not in *; intros; solve [auto].
        eauto.
        solve_lengths.
        eauto.

        (* [pos] is not in the transaction *)
        Ltac wneq H := intro HeqContra; symmetry in HeqContra; apply H; auto.
        intro Hf; 
          repeat (erewrite replay_sel_other);
          try trivial;
          intro HIn; destruct HIn as [x HIn];
          try apply Map.add_3 in HIn;
          try apply Map.find_1 in HIn;
          try wneq n;
          replace (Map.find $ (pos) ms) with (Some x) in Hf; inversion Hf.
    - (* [pos] is an invalid address *)
      rewrite replay_sel_invalid by auto.
      unfold upd.
      rewrite selN_updN_ne by (
        generalize (wordToNat_bound a); intro Hb;
        omega).
      rewrite replay_sel_invalid by auto; trivial.
  Qed.

  Lemma valid_entries_add : forall a v ms m,
    valid_entries m ms -> indomain' a m -> valid_entries m (Map.add a v ms).
  Proof.
    unfold valid_entries in *.
    intros.
    destruct (weq a a0).
    subst; auto.
    eapply H.
    eapply Map.add_3; eauto.
  Qed.


  Lemma upd_prepend_length: forall l a v, length (upd_prepend l a v) = length l.
  Proof.
    intros; unfold upd_prepend.
    solve_lengths.
  Qed.
  Hint Rewrite upd_prepend_length : lengths.

  Definition write T (xp : log_xparams) a v (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    rx ^(Map.add a v ms, cs).

  Theorem write_ok : forall xp mscs a v,
    {< m1 m2 F F' v0,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs * [[ (F' * a |-> v0)%pred (list2mem m2) ]]
    POST RET:mscs
      exists m', rep xp F (ActiveTxn m1 m') mscs *
      [[ (F' * a |-> v)%pred (list2mem m') ]]
    CRASH
      exists m' mscs', rep xp F (ActiveTxn m1 m') mscs'
    >} write xp a v mscs.
  Proof.
    unfold write; log_unfold.
    hoare.

    apply valid_entries_add; eauto.
    unfold indomain'.
    erewrite <- replay_length.
    (* XXX probably want to make a version of [list2mem_ptsto_bounds] that takes two lists
       and a hypothesis that their lengths are equal *)
    eapply list2mem_ptsto_bounds; eauto.

    rewrite replay_add.
    eapply list2mem_upd; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _ _) _) => apply write_ok : prog.

  Definition read T (xp: log_xparams) a (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    match Map.find a ms with
    | Some v =>
      rx ^(^(ms, cs), v)
    | None =>
      let^ (cs, v) <- BUFCACHE.read_array (DataStart xp) a cs;
      rx ^(^(ms, cs), v)
    end.


  Theorem read_ok: forall xp mscs a,
    {< m1 m2 v F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs *
      [[ exists F, (F * a |-> v) (list2mem m2) ]]
    POST RET:^(mscs,r)
      rep xp F (ActiveTxn m1 m2) mscs *
      [[ r = v ]]
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs'
    >} read xp a mscs.
  Proof.
    unfold read; log_unfold.
    destruct mscs as [ms cs]; simpl; intros.

    case_eq (Map.find a ms); hoare.

    eapply list2mem_sel with (def := $0) in H1.
    apply Map.find_2 in H.
    eapply replay_sel_in in H.
    rewrite <- H.
    rewrite H1.
    reflexivity.
    unfold valid_entries in *.
    eauto.

    solve_lengths.
    unfold indomain' in *.
    eauto.

    unfold sel.
    rewrite combine_length; autorewrite_fast.
    apply list2mem_ptsto_bounds in H1.
    rewrite replay_length in *.
    eauto.

    eapply list2mem_sel with (def := $0) in H1.
    rewrite H1.
    unfold sel.
    rewrite replay_sel_other. trivial.
    intuition.
    subst.
    rewrite selN_combine.
    simpl.
    eauto.

    rewrite repeat_length.
    eauto.

    intro.
    hnf in H4.
    destruct H4.
    apply Map.find_1 in H4.
    congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _ _) _) => apply read_ok : prog.

  Definition flush_unsync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ old crash F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header 0)
          * data_rep xp (synced_list old)
          * exists rest, (LogDescriptor xp) |=> descriptor_to_valu rest
          * [[ @Rec.well_formed descriptor_type rest ]]
          * exists l', [[ length l' = # i ]]
          * array (LogData xp) (firstn (# i) (List.combine (map snd (Map.elements ms)) l')) $1
          * avail_region (LogData xp ^+ i) (# (LogLen xp) - # i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.write_array (LogData xp ^+ i) $0
        (sel (map snd (Map.elements ms)) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    cs <- BUFCACHE.write (LogDescriptor xp)
      (descriptor_to_valu (map fst (Map.elements ms))) cs;
    rx ^(ms, cs).

  Definition flush_sync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    cs <- BUFCACHE.sync (LogDescriptor xp) cs;
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ old crash F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header 0)
          * data_rep xp (synced_list old)
          * exists rest, (LogDescriptor xp) |=> descriptor_to_valu (map fst (Map.elements ms) ++ rest)
          * [[ @Rec.well_formed descriptor_type (map fst (Map.elements ms) ++ rest) ]]
          * array (LogData xp) (firstn (# i) (synced_list (map snd (Map.elements ms)))) $1
          * exists l', [[ length l' = Map.cardinal ms - # i ]]
          * array (LogData xp ^+ i) (List.combine (skipn (# i) (map snd (Map.elements ms))) l') $1
          * avail_region (LogData xp ^+ $ (Map.cardinal ms)) (# (LogLen xp) - Map.cardinal ms))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.sync_array (LogData xp ^+ i) $0 cs;
      lrx ^(cs)
    Rof ^(cs);
    rx ^(ms, cs).

  Definition flush T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    If (lt_dec (wordToNat (LogLen xp)) (Map.cardinal ms)) {
      rx ^(^(ms, cs), false)
    } else {
      (* Write... *)
      let^ (ms, cs) <- flush_unsync xp ^(ms, cs);
      (* ... and sync *)
      let^ (ms, cs) <- flush_sync xp ^(ms, cs);
      rx ^(^(ms, cs), true)
    }.

  Theorem firstn_map : forall A B n l (f: A -> B),
    firstn n (map f l) = map f (firstn n l).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    destruct l; simpl.
    reflexivity.
    f_equal.
    eauto.
  Qed.

  Lemma combine_one: forall A B (a: A) (b: B), [(a, b)] = List.combine [a] [b].
  Proof.
    intros; auto.
  Qed.

  Definition emp_star_r' : forall V AT AEQ P, P * (emp (V:=V) (AT:=AT) (AEQ:=AEQ)) =p=> P.
  Proof.
    cancel.
  Qed.

  Ltac word_assert P := let H := fresh in assert P as H by
      (word2nat_simpl; repeat rewrite wordToNat_natToWord_idempotent'; word2nat_solve); clear H.

  Ltac array_sort' :=
    eapply pimpl_trans; rewrite emp_star; [ apply pimpl_refl |];
    set_evars;
    repeat rewrite <- sep_star_assoc;
    subst_evars;
    match goal with
    | [ |- ?p =p=> ?p ] => fail 1
    | _ => idtac
    end;
    repeat match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      word_assert (a2 <= a1)%word;
      first [
        (* if two arrays start in the same place, try to prove one of them is empty and eliminate it *)
        word_assert (a1 = a2)%word;
        first [
          let H := fresh in assert (length l1 = 0) by solve_lengths;
          apply length_nil in H; try rewrite H; clear H; simpl; rewrite emp_star_r'
        | let H := fresh in assert (length l2 = 0) by solve_lengths;
          apply length_nil in H; try rewrite H; clear H; simpl; rewrite emp_star_r'
        | fail 2
        ]
      | (* otherwise, just swap *)
        rewrite (sep_star_assoc p (array a1 l1 s));
        rewrite (sep_star_comm (array a1 l1 s)); rewrite <- (sep_star_assoc p (array a2 l2 s))
      ]
    end;
    (* make sure we can prove it's sorted *)
    match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      (word_assert (a1 <= a2)%word; fail 1) || fail 2
    | _ => idtac
    end;
    eapply pimpl_trans; rewrite <- emp_star; [ apply pimpl_refl |].

  Ltac array_sort :=
    word2nat_clear; word2nat_auto; [ array_sort' | .. ].

  Lemma singular_array: forall T a (v: T),
    a |-> v <=p=> array a [v] $1.
  Proof.
    intros. split; cancel.
  Qed.

  Lemma equal_arrays: forall T (l1 l2: list T) a1 a2,
    a1 = a2 -> l1 = l2 -> array a1 l1 $1 =p=> array a2 l2 $1.
  Proof.
    cancel.
  Qed.

  Ltac rewrite_singular_array :=
    repeat match goal with
    | [ |- context[@ptsto addr (@weq addrlen) ?V ?a ?v] ] =>
      setoid_replace (@ptsto addr (@weq addrlen) V a v)%pred
      with (array a [v] $1) by (apply singular_array)
    end.

  Lemma make_unifiable: forall a l s,
    array a l s <=p=> unifiable_array a l s.
  Proof.
    split; cancel.
  Qed.

  Ltac array_cancel_trivial :=
    fold unifiable_array;
    match goal with
    | [ |- _ =p=> ?x * unifiable_array ?a ?l ?s ] => first [ is_evar x | is_var x ]; unfold unifiable_array; rewrite (make_unifiable a l s)
    | [ |- _ =p=> unifiable_array ?a ?l ?s * ?x ] => first [ is_evar x | is_var x ]; unfold unifiable_array; rewrite (make_unifiable a l s)
    end;
    solve [ cancel ].

  Ltac array_match :=
    unfold unifiable_array in *;
    match goal with (* early out *)
    | [ |- _ =p=> _ * array _ _ _ ] => idtac
    | [ |- _ =p=> _ * _ |-> _ ] => idtac
    | [ |- _ =p=> array _ _ _ ] => idtac
    end;
    solve_lengths_prepare;
    rewrite_singular_array;
    array_sort;
    set_evars;
    repeat (rewrite array_app; [ | solve_lengths_prepped ]); [ repeat rewrite <- app_assoc | .. ];
    try apply pimpl_refl;
    try (apply equal_arrays; [ solve_lengths_prepped | try reflexivity ]);
    subst_evars.

  Ltac try_arrays_lengths := try (array_cancel_trivial || array_match); solve_lengths_prepped.

  (* Slightly different from CPDT [equate] *)
  Ltac equate x y :=
    let tx := type of x in
    let ty := type of y in
    let H := fresh in
    assert (x = y) as H by reflexivity; clear H.

  Ltac split_pair_list_evar :=
    match goal with
    | [ |- context [ ?l ] ] =>
      is_evar l;
      match type of l with
      | list (?A * ?B) =>
        let l0 := fresh in
        let l1 := fresh in
        evar (l0 : list A); evar (l1 : list B);
        let l0' := eval unfold l0 in l0 in
        let l1' := eval unfold l1 in l1 in
        equate l (@List.combine A B l0' l1');
        clear l0; clear l1
      end
    end.

  Theorem combine_upd: forall A B i a b (va: A) (vb: B),
    List.combine (upd a i va) (upd b i vb) = upd (List.combine a b) i (va, vb).
  Proof.
    unfold upd; intros.
    apply combine_updN.
  Qed.

  Lemma updN_0_skip_1: forall A l (a: A),
    length l > 0 -> updN l 0 a = a :: skipn 1 l .
  Proof.
    intros; destruct l.
    simpl in H. omega.
    reflexivity.
  Qed.

  Lemma cons_app: forall A l (a: A),
    a :: l = [a] ++ l.
  Proof.
    auto.
  Qed.

  Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
    List.combine (map fst l) (map snd l) = l.
  Proof.
    induction l.
    auto.
    simpl; rewrite IHl; rewrite <- surjective_pairing; auto.
  Qed.

  Hint Rewrite firstn_combine_comm skipn_combine_comm selN_combine
    removeN_combine List.combine_split combine_nth combine_one updN_0_skip_1 skipn_selN : lists.
  Hint Rewrite <- combine_updN combine_upd combine_app : lists.

  Ltac split_pair_list_vars :=
    set_evars;
    repeat match goal with
    | [ H : list (?A * ?B) |- _ ] =>
      match goal with
      | |- context[ List.combine (map fst H) (map snd H) ] => fail 1
      | _ => idtac
      end;
      rewrite <- combine_map_fst_snd with (l := H)
    end;
    subst_evars.

  Ltac split_lists :=
    unfold upd_prepend, upd_sync;
    unfold sel, upd;
    repeat split_pair_list_evar;
    split_pair_list_vars;
    autorewrite with lists; [ f_equal | .. ].

  Ltac or_r := apply pimpl_or_r; right.
  Ltac or_l := apply pimpl_or_r; left.


  Theorem flush_unsync_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs *
      [[ let '^(ms, cs) := mscs in Map.cardinal ms <= wordToNat (LogLen xp) ]]
    POST RET:mscs
      rep xp F (FlushedUnsyncTxn m1 m2) mscs *
      [[ let '^(ms, cs) := mscs in Map.cardinal ms <= wordToNat (LogLen xp) ]]
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs' \/ rep xp F (FlushedUnsyncTxn m1 m2) mscs'
    >} flush_unsync xp mscs.
  Proof.
    unfold flush_unsync; log_unfold; unfold avail_region, log_rep_empty.
    destruct mscs as [ms cs].
    intros.
    solve_lengths_prepare.
    step_with ltac:(unfold avail_region) try_arrays_lengths.
    ring_simplify (# (LogData xp) + 0).
    word2nat_simpl.
    instantiate (1 := l).
    cancel.
    instantiate (1 := nil); auto.
    solve_lengths.
    step_with ltac:(unfold avail_region) try_arrays_lengths.
    step_with ltac:(unfold avail_region, upd_prepend) try_arrays_lengths.
    split_lists.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    f_equal.
    simpl.
    repeat f_equal.
    solve_lengths.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    simpl.
    instantiate (3 := l0 ++ [valuset_list (selN l1 0 ($0, nil))]).
    simpl.
    rewrite firstn_app_l by solve_lengths.
    repeat erewrite selN_map by solve_lengths.
    rewrite <- surjective_pairing.
    rewrite selN_app2.
    rewrite H21.
    rewrite Nat.sub_diag.
    reflexivity.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract solve_lengths.
    abstract (case_eq l1; intros; subst; word2nat_clear; simpl in *; solve_lengths).

    or_l. cancel.
    array_match.
    reflexivity.
    solve_lengths.
    or_l. cancel.
    array_match.
    reflexivity.
    solve_lengths.
    step_with ltac:(unfold avail_region) try_arrays_lengths.
    (* Annoyingly, [intuition] just incorrectly applies [Forall_nil] in one place, so we can't use [step] *)
    eapply pimpl_ok2; [ eauto with prog | ].
    intros; norm; [ cancel' | intuition idtac ].
    pred_apply; norm; [ cancel' | intuition idtac ].
    rewrite firstn_oob by solve_lengths.
    rewrite Map.cardinal_1.
    unfold valuset_list.
    instantiate (2 := l0).
    instantiate (2 := [d1]).
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - Map.cardinal ms).
    cancel.
    abstract solve_lengths.
    abstract solve_lengths.
    rewrite Forall_forall; intuition.
    abstract solve_lengths.
    abstract solve_lengths.
    intuition.
    abstract solve_lengths.
    or_l. cancel.
    rewrite firstn_oob by solve_lengths.
    array_match.
    reflexivity.
    abstract solve_lengths.

    or_r.
    norm; [ cancel' | intuition idtac ].
    pred_apply; norm; [ cancel' | intuition idtac ].
    rewrite firstn_oob by solve_lengths.
    rewrite Map.cardinal_1.
    unfold valuset_list.
    instantiate (2 := l0).
    instantiate (2 := [d1]).
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - Map.cardinal ms).
    cancel.
    eauto.
    abstract solve_lengths.
    solve_lengths.
    rewrite Forall_forall; intuition.
    abstract solve_lengths.
    abstract solve_lengths.
    intuition.

    Unshelve.
    all: auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush_unsync _ _) _) => apply flush_unsync_ok : prog.

  Theorem flush_sync_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (FlushedUnsyncTxn m1 m2) mscs *
      [[ let '^(ms, cs) := mscs in Map.cardinal ms <= wordToNat (LogLen xp) ]]
    POST RET:mscs
      rep xp F (FlushedTxn m1 m2) mscs *
      [[ let '^(ms, cs) := mscs in Map.cardinal ms <= wordToNat (LogLen xp) ]]
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs' \/
                    rep xp F (FlushedUnsyncTxn m1 m2) mscs'
    >} flush_sync xp mscs.
  Proof.
    unfold flush_sync; log_unfold; unfold avail_region.
    destruct mscs as [ms cs].
    intros.
    solve_lengths_prepare.
    step.
    step.

    ring_simplify (LogData xp ^+ $0).
    cancel; eauto.
    omega.

    step.
    instantiate (a5 := List.combine (skipn # m1 (map snd (Map.elements ms))) l4).
    cancel.
    solve_lengths.

    step.
    try_arrays_lengths.
    split_lists.
    rewrite skipn_skipn.
    rewrite (plus_comm 1).
    rewrite Nat.add_0_r.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    reflexivity.
    solve_lengths.
    erewrite firstn_plusone_selN.
    rewrite <- app_assoc.
    rewrite repeat_selN.
    reflexivity.

    solve_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.

    or_l. cancel.
    try_arrays_lengths.
    solve_lengths.

    or_l. cancel.
    try_arrays_lengths.
    unfold upd_sync; solve_lengths.
    unfold upd_sync; solve_lengths.
    unfold upd_sync; solve_lengths.

    step.
    try_arrays_lengths.
    rewrite firstn_oob by solve_lengths.
    eauto.
    solve_lengths.
    solve_lengths.
    solve_lengths.

    or_r. cancel.
    try_arrays_lengths.
    solve_lengths.
    solve_lengths.
    solve_lengths.

    or_l. cancel.
    try_arrays_lengths.
    solve_lengths.

    Unshelve.
    all: auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush_sync _ _) _) => apply flush_sync_ok : prog.

  Theorem flush_ok : forall xp mscs,
    {< m1 m2 F,
    PRE
      rep xp F (ActiveTxn m1 m2) mscs
    POST RET:^(mscs,r)
      ([[ r = true ]] * rep xp F (FlushedTxn m1 m2) mscs) \/
      ([[ r = false ]] * rep xp F (ActiveTxn m1 m2) mscs)
    CRASH
      exists mscs', rep xp F (ActiveTxn m1 m2) mscs' \/ rep xp F (FlushedUnsyncTxn m1 m2) mscs'
    >} flush xp mscs.
  Proof.
    unfold flush.
    hoare.
  Qed.

  Hint Extern 1 ({{_}} progseq (flush _ _) _) => apply flush_ok : prog.

  Lemma equal_unless_in_trans: forall T m a b c (def: T),
    equal_unless_in m a b def -> equal_unless_in m b c def -> equal_unless_in m a c def.
  Proof.
    unfold equal_unless_in; intuition.
    rewrite H2 by auto. apply H3; auto.
    rewrite H2 by auto. apply H3; auto.
  Qed.

  Lemma equal_unless_in_comm: forall T m a b (def: T),
    equal_unless_in m a b def -> equal_unless_in m b a def.
  Proof.
    unfold equal_unless_in; intuition. rewrite H1 by auto; reflexivity.
    rewrite H1 by auto; reflexivity.
  Qed.

  Lemma In_MapIn: forall V a (ms: Map.t V), In a (map fst (Map.elements ms)) <-> Map.In a ms.
    intuition.
    apply MapFacts.elements_in_iff.
    apply in_map_iff in H.
    destruct H.
    intuition; subst.
    eexists.
    apply InA_alt.
    eexists.
    intuition; eauto.
    constructor; simpl; auto.

    apply MapFacts.elements_in_iff in H.
    apply in_map_iff.
    destruct H.
    apply InA_alt in H.
    destruct H.
    intuition.
    eexists.
    intuition; eauto.
    destruct x0; inversion H0; auto.
  Qed.

  Lemma equal_unless_in_replay_eq: forall ms a b def,
    replay ms a = replay ms b <-> equal_unless_in (map fst (Map.elements ms)) a b def.
  Proof.
    unfold equal_unless_in, sel.
    intuition.
    {
    erewrite <- replay_length with (m := a).
    erewrite <- replay_length with (m := b).
    f_equal; eauto.
    }
    {
      erewrite <- replay_sel_invalid with (d := a).
      erewrite <- replay_sel_invalid with (d := b).
      f_equal; eauto.
      word2nat_auto.
      word2nat_auto.
    }
    {
    destruct (lt_dec n (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace n with (wordToNat (natToWord addrlen (n))) by word2nat_auto.
      erewrite <- replay_sel_other.
      erewrite <- replay_sel_other with (m := b).
      f_equal; eauto.
      intro Hi; apply In_MapIn in Hi; tauto.
      intro Hi; apply In_MapIn in Hi; tauto.
    - erewrite <- replay_sel_invalid with (d := a).
      erewrite <- replay_sel_invalid with (d := b).
      f_equal; eauto.
      word2nat_auto.
      word2nat_auto.
    }
    {
    eapply list_selN_ext.
    repeat rewrite replay_length; auto.
    intros.
    destruct (lt_dec pos (pow2 addrlen)).
    - (* [pos] is a valid address *)
      replace pos with (wordToNat (natToWord addrlen (pos))) by word2nat_auto.
      case_eq (Map.find $ pos ms).
      + intros w Hf. apply Map.find_2 in Hf. apply replay_sel_in.
        autorewrite with lengths in *.
        solve_lengths.
        erewrite replay_sel_in; eauto.
        autorewrite with lengths in *.
        solve_lengths.
      + intros Hf. repeat erewrite replay_sel_other.
        apply H1.
        right.
        word2nat_rewrites; try word2nat_solve.
        intro HIn.
        apply MapFacts.not_find_in_iff in Hf.
        apply In_MapIn in HIn. tauto.
        apply MapFacts.not_find_in_iff; auto.
        apply MapFacts.not_find_in_iff; auto.
    - repeat rewrite replay_sel_invalid by auto.
      apply H1.
      left.
      word2nat_auto.
    }
  Qed.

  Lemma f_equal_unless_in: forall A B (f: A -> B) l a b def def',
    equal_unless_in l a b def -> equal_unless_in l (map f a) (map f b) def'.
  Proof.
    unfold equal_unless_in; split.
    repeat rewrite map_length; intuition.
    intros.
    destruct H.
    destruct (lt_dec n (length b)).
    repeat rewrite selN_map with (default' := def) by congruence.
    f_equal. intuition.
    repeat rewrite selN_oob by (rewrite map_length; omega); trivial.
  Qed.

  Lemma equal_unless_in_replay_eq': forall ms (a b: list valuset) def,
    equal_unless_in (map fst (Map.elements ms)) a b def -> replay ms (map fst a) = replay ms (map fst b).
  Proof.
    intros.
    apply equal_unless_in_replay_eq with (def := fst def).
    eapply f_equal_unless_in; eauto.
  Qed.

  Lemma combine_repeat_map: forall A B (v: B) (l: list A),
    List.combine l (repeat v (length l)) = map (fun x => (x, v)) l.
  Proof.
    induction l; simpl; auto.
    fold repeat; rewrite IHl; auto.
  Qed.

  Lemma equal_unless_in_replay_eq'': forall ms (a b: list valu) def,
    replay ms a = replay ms b -> equal_unless_in (map fst (Map.elements ms))
            (List.combine a (repeat (@nil valu) (length a))) 
            (List.combine b (repeat (@nil valu) (length b))) def.
  Proof.
    intros.
    repeat rewrite combine_repeat_map.
    eapply f_equal_unless_in.
    apply equal_unless_in_replay_eq with (def := fst def); auto.
  Qed.


  Lemma map_fst_combine: forall A B (a: list A) (b: list B),
    length a = length b -> map fst (List.combine a b) = a.
  Proof.
    unfold map, List.combine; induction a; intros; auto.
    destruct b; try discriminate; simpl in *.
    rewrite IHa; [ auto | congruence ].
  Qed.

  Lemma map_snd_combine: forall A B (a: list A) (b: list B),
    length a = length b -> map snd (List.combine a b) = b.
  Proof.
    unfold map, List.combine.
    induction a; destruct b; simpl; auto; try discriminate.
    intros; rewrite IHa; eauto.
  Qed.


  Hint Resolve equal_unless_in_trans equal_unless_in_comm equal_unless_in_replay_eq equal_unless_in_replay_eq'' : replay.

  Lemma valid_entries_replay' : forall l l' ms def,
    equal_unless_in (map fst (Map.elements ms))
                    (List.combine l (repeat (@nil valu) (length l))) l' def
    -> valid_entries l ms
    -> valid_entries (replay' (Map.elements ms) (map fst l')) ms.
  Proof.
    intros.
    pose proof (equal_unless_in_replay_eq' _ H) as Heq.
    unfold replay in Heq; rewrite <- Heq; clear Heq.
    rewrite map_fst_combine by solve_lengths.
    eapply (@valid_entries_replay ms l); auto.
  Qed.

  Lemma nil_combine_nil_unless_in : forall A (l : list A) l' msa def,
    equal_unless_in msa (List.combine l (repeat (@nil valu) (length l))) l' def
    -> nil_unless_in msa (map snd l').
  Proof.
    unfold equal_unless_in, nil_unless_in; intros.
    destruct H; unfold sel.
    pose proof (H1 (# a)) as Hx; intuition.
    destruct (lt_dec (# a) (length l')).
    erewrite selN_map with (default' := def); eauto.
    rewrite <- H3.
    destruct def; erewrite selN_combine by solve_lengths; simpl.
    rewrite repeat_selN; auto.
    rewrite combine_length_eq in H by solve_lengths.
    rewrite H; auto.
    word2nat_auto.
    rewrite selN_oob; solve_lengths.
  Qed.

  Lemma nil_unless_in_bwd : forall n l ms,
    nil_unless_in (skipn n ms) l
    -> nil_unless_in ms l.
  Proof.
    unfold nil_unless_in, sel, upd; intros.
    apply H.
    contradict H0.
    eapply in_skipn_in; eauto.
  Qed.

  Lemma valid_entries_addr_valid : forall (i : addr) m l def,
    (i < $ (Map.cardinal m))%word
    -> valid_entries l m
    -> # (sel (map fst (Map.elements m)) i def) < length l.
  Proof.
    intros.
    eapply H0.
    apply MapFacts.elements_mapsto_iff.
    apply In_InA.
    apply MapProperties.eqke_equiv.
    apply in_selN_map.
    solve_lengths.
    Grab Existential Variables.
    exact $0.
  Qed.

  Lemma helper_valid_entries_addr_valid : forall i ls log (l l' : list valuset) ms def,
    valid_entries log ms
    -> (i < $ (Map.cardinal ms))%word
    -> equal_unless_in ls log (map fst l') $0
    -> # (sel (map fst (Map.elements ms)) i def) < length l'.
  Proof.
    unfold equal_unless_in, valid_entries; intros.
    destruct H1.
    rewrite map_length in H1.
    rewrite <- H1.
    apply valid_entries_addr_valid; auto.
  Qed.

  Lemma fold_left_skipn_S : forall A B l (f : A -> B -> A) i a def,
    i < length l
    -> fold_left f (skipn (S i) l) (f a (selN l i def))
     = fold_left f (skipn i l) a.
  Proof.
    induction l; simpl; intros; auto.
    inversion H.
    destruct i.
    simpl; auto.
    apply IHl.
    omega.
  Qed.

  Lemma replay_skipn_progress : forall i (log : list (addr * valu)) l,
    i < length log
    -> replay' (skipn (S i) log) (upd l (selN (map fst log) i $0) (selN (map snd log) i $0)) 
     = replay' (skipn i log) l.
  Proof.
    intros.
    repeat erewrite selN_map with (default' := ($0, $0)); eauto.
    unfold replay'.
    remember (fun m' p => upd m' (fst p) (snd p)) as f.
    replace (upd l (fst (selN log i ($0, $0))) (snd (selN log i ($0, $0))))
        with (f l (selN log i ($0, $0)) ).
    rewrite fold_left_skipn_S; auto.
    subst; auto.
  Qed.

  Lemma fst_upd_prepend : forall vs a v,
    map fst (upd_prepend vs a v) = upd (map fst vs) a v.
  Proof.
    unfold upd_prepend; intros.
    rewrite map_upd; auto.
  Qed.


  Lemma equal_unless_in_bwd : forall A n l l' (def : A) ms,
    equal_unless_in (skipn n ms) l l' def
    -> equal_unless_in ms l l' def.
  Proof.
    unfold equal_unless_in, sel, upd; intros.
    destruct H.
    split; auto;intuition.
    apply H0. right.
    contradict H2.
    eapply in_skipn_in; eauto.
  Qed.

  Lemma valid_entries_replay'_rev : forall l m,
    valid_entries (replay' (Map.elements m) l) m
    -> valid_entries l m.
  Proof.
    unfold valid_entries, indomain'; intros.
    apply H in H0.
    rewrite replay'_length in H0; auto.
  Qed.

  Lemma replay'_sel_fst_eq_snd : forall V n (log : list (addr * V)) l ad vd,
    KNoDup log
    -> n < length log
    -> # (selN (map fst log) n ad) < length l
    -> sel (replay' log l) (selN (map fst log) n ad) vd
                          = selN (map snd log) n vd.
  Proof.
    intros.
    erewrite replay'_sel_in; eauto.
    apply in_selN_map; auto.
  Qed.

  Lemma equal_unless_in_S : forall (n : addr) (log : list (addr * valu)) l l' def m,
    equal_unless_in (skipn (# n) (map fst log)) (replay' log l) l' def
    -> (n < $ (Map.cardinal m))%word
    -> valid_entries (replay' log l) m
    -> log = Map.elements m
    -> equal_unless_in (skipn (S (# n)) (map fst log)) (replay' log l)
       (upd l' (selN (map fst log) (# n) $0) (selN (map snd log) (# n) def)) def.
  Proof.
    unfold equal_unless_in, upd, sel; intros.
    assert (length l = length l') as Heq.
    rewrite replay'_length in H; apply H.

    destruct H; split; intros.
    rewrite replay'_length; rewrite length_updN; auto.

    destruct (Nat.eq_dec n0 (# (selN (map fst log) (# n) $0))); subst.
    rewrite selN_updN_eq.
    apply replay'_sel_fst_eq_snd.
    apply Map.elements_3w.
    solve_lengths.
    apply valid_entries_addr_valid; auto.
    apply valid_entries_replay'_rev; auto.

    rewrite <- Heq.
    apply valid_entries_addr_valid; auto.
    apply valid_entries_replay'_rev; auto.

    rewrite selN_updN_ne by auto.
    apply H3.
    destruct (lt_dec n0 (pow2 addrlen)); inversion H4; auto.
    right; contradict H2.
    eapply in_skipn_S; auto.
    apply wordToNat_neq_inj.
    rewrite wordToNat_natToWord_idempotent'; eauto.
  Qed.

  Lemma nil_unless_in_prepend : forall l d a v,
    nil_unless_in l (map snd d) -> In a l
    -> nil_unless_in l (map snd (upd_prepend d a v)).
  Proof.
    unfold nil_unless_in, upd_prepend; intros.
    destruct (weq a a0); try congruence.
    destruct (lt_dec (# a0) (length d)).
    erewrite sel_map.
    rewrite sel_upd_ne by auto.
    erewrite <- H by eauto.
    erewrite sel_map; eauto.
    rewrite length_upd; eauto.
    unfold sel; rewrite selN_oob; eauto.
    solve_lengths.
    Grab Existential Variables.
    exact ($0, nil).
  Qed.

  Ltac solve_equal_unless_in_length :=
    repeat match goal with
    | [ H : equal_unless_in _ ?l1 ?l2 _ |- _ ] =>
      let Hx := fresh in
      unfold equal_unless_in in H; destruct H as [Hx ?];
      autorewrite with lengths in Hx;
      try rewrite Nat.min_id in Hx
    | [ |- length _ = length _ ] => progress autorewrite with lengths
    | [ H : length ?a = length ?b |- context [length ?a ] ] => rewrite H
    end; auto.

  Lemma equal_unless_in_replay' : forall (ms : memstate) l l' def,
    equal_unless_in (map fst (Map.elements ms)) (replay' (Map.elements ms) l) l' def
    -> equal_unless_in (map fst (Map.elements ms)) l l' def.
  Proof.
    intros.
    apply equal_unless_in_replay_eq.
    rewrite <- replay_twice.
    apply <- equal_unless_in_replay_eq; eauto.
  Qed.

  Lemma pair_selN_map : forall A B (l : list (A * B)) n ad bd,
    (selN (map fst l) n ad, selN (map snd l) n bd) = selN l n (ad, bd).
  Proof.
    induction l; destruct n; simpl; firstorder.
    destruct a; auto.
  Qed.

  Lemma equal_unless_in_combine : forall A B log (l : list (A * B)) a b ad bd,
    equal_unless_in log a (map fst l) ad
    -> equal_unless_in log b (map snd l) bd
    -> equal_unless_in log (List.combine a b) l (ad, bd).
  Proof.
    unfold equal_unless_in; intros.
    assert (length a = length b).
    rewrite map_length in *; solve_lengths.

    destruct H; destruct H0.
    split; intros.
    rewrite map_length in *.
    rewrite combine_length_eq; auto; solve_lengths.

    rewrite selN_combine by auto.
    rewrite H2 by auto.
    rewrite H3 by auto.
    apply pair_selN_map.
  Qed.

  Lemma equal_unless_in_split : forall A B log (l : list (A * B)) a b def,
    equal_unless_in log (List.combine a b) l def
    -> length a = length b
    -> equal_unless_in log a (map fst l) (fst def) /\
       equal_unless_in log b (map snd l) (snd def).
  Proof.
    unfold equal_unless_in; intros.
    destruct H.
    rewrite combine_length_eq in H by auto.
    split; split; try solve_lengths.

    destruct (lt_dec n (length l)).
    erewrite selN_map by auto.
    rewrite <- H1 by auto.
    destruct def.
    rewrite selN_combine by auto.
    simpl; auto.
    rewrite selN_oob by omega.
    rewrite selN_oob; auto.
    rewrite map_length; omega.

    destruct (lt_dec n (length l)).
    erewrite selN_map by auto.
    rewrite <- H1 by auto.
    destruct def.
    rewrite selN_combine by auto.
    simpl; auto.
    rewrite selN_oob by omega.
    rewrite selN_oob; auto.
    rewrite map_length; omega.
  Qed.

  Lemma nil_unless_in_equal_unless_in : forall log n l,
    nil_unless_in log l
    -> n = length l
    -> goodSizeEq addrlen n
    -> equal_unless_in log (repeat nil n) l nil.
  Proof.
    unfold nil_unless_in, equal_unless_in; intros.
    split; solve_lengths.
    destruct (lt_dec n0 n).

    rewrite repeat_selN by auto.
    destruct (lt_dec n0 (pow2 addrlen)).
    intuition.
    erewrite <- H at 1; eauto.
    unfold sel.
    rewrite wordToNat_natToWord_idempotent'; auto.

    intuition; unfold goodSize, goodSizeEq in *; omega.
    repeat rewrite selN_oob; solve_lengths.
  Qed.

  Lemma equal_unless_in_trans_nil : forall log l (l1 : list valuset) l2,
    equal_unless_in log (List.combine l (repeat nil (length l))) l1 ($0, nil)
    -> equal_unless_in log (map fst l1) (map fst l2) $0
    -> nil_unless_in log (map snd l2)
    -> goodSizeEq addrlen (length l)
    -> equal_unless_in log (List.combine l (repeat nil (length l))) l2 ($0, nil).
  Proof.
    intros.
    apply equal_unless_in_split in H; destruct H; simpl in *.
    eapply equal_unless_in_combine.
    eapply equal_unless_in_trans; eauto.
    apply nil_unless_in_equal_unless_in; auto.
    solve_equal_unless_in_length.
    solve_lengths.
  Qed.

  Lemma equal_unless_in_upd_in : forall (n : addr) log l l' def m,
    equal_unless_in (map fst log) l l' def
    -> (n < $ (Map.cardinal m))%word
    -> valid_entries l m
    -> log = Map.elements m
    -> goodSizeEq addrlen (length l')
    -> equal_unless_in (map fst log) l
       (upd l' (selN (map fst log) (# n) $0) (selN (map snd log) (# n) def)) def.
  Proof.
    unfold equal_unless_in, upd, sel; intros.
    destruct H; split; intros.
    rewrite length_updN; auto.

    destruct (Nat.eq_dec n0 (# (selN (map fst log) (# n) $0))); subst.
    intuition.
    rewrite H4 by auto.
    destruct (lt_dec # (selN (map fst (Map.elements m)) (# n) $0) (length l'));
    unfold goodSize, goodSizeEq, Map.key in *.
    contradict H2; omega.
    rewrite selN_oob by omega.
    rewrite selN_oob; auto.
    rewrite length_updN; omega.

    contradict H2.
    rewrite natToWord_wordToNat.
    apply in_selN;  solve_lengths.

    rewrite selN_updN_ne by auto.
    apply H4; auto.
  Qed.

  Lemma equal_unless_in_trans_upd_in : forall (n : addr) log l (l1 : list valuset) l2 m,
    equal_unless_in (map fst log) (List.combine l (repeat nil (length l))) l1 ($0, nil)
    -> equal_unless_in (skipn (# n) (map fst log)) (replay' log (map fst l1)) l2 $0
    -> (n < $ (Map.cardinal m))%word
    -> valid_entries l m
    -> log = Map.elements m
    -> goodSizeEq addrlen (length l2)
    -> equal_unless_in (map fst log) l
       (upd l2 (selN (map fst log) (# n) $0) (selN (map snd log) (# n) $0)) $0.
  Proof.
    intros.
    apply equal_unless_in_split in H; destruct H; simpl in *.
    eapply equal_unless_in_bwd in H0; eauto.
    subst; eapply equal_unless_in_replay' in H0.
    eapply equal_unless_in_upd_in; eauto.
    eapply equal_unless_in_trans; eauto.
    solve_lengths.
  Qed.

  Lemma replay'_terminate_replay : forall (m : memstate) l (l1 : list valuset) l2 (bound : addr),
    equal_unless_in (map fst (Map.elements m)) (List.combine l (repeat nil (length l))) l1 ($0, nil)
    -> replay' (skipn # (natToWord addrlen (Map.cardinal m)) (Map.elements m)) l2
       = replay' (Map.elements m) (map fst l1)
    -> Map.cardinal m <= # bound
    -> l2 = replay m l.
  Proof.
    intros.
    rewrite skipn_oob in H0; simpl in H0.
    rewrite H0.
    apply equal_unless_in_split in H; destruct H.
    apply equal_unless_in_replay_eq in H.
    rewrite H; auto.
    solve_lengths.
    erewrite wordToNat_natToWord_bound; eauto.
    solve_lengths.
  Qed.

  Lemma replay_unsync_crash : forall (m m' : memstate) l (l1 : list valuset) l2,
    equal_unless_in (map fst (Map.elements m)) (List.combine l (repeat nil (length l))) l1 ($0, nil)
    -> replay' (Map.elements m) (map fst l1) = replay m' l2
    -> replay m l = replay m' l2.
  Proof.
    intros.
    apply equal_unless_in_split in H; destruct H.
    apply equal_unless_in_replay_eq in H.
    rewrite H; auto.
    solve_lengths.
  Qed.

  Definition apply_unsync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ cur F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal ms))
          * log_rep xp cur ms
          * exists d, data_rep xp d
          * [[ replay' (skipn (wordToNat i) (Map.elements ms)) (map fst d) = cur ]]
          * [[ equal_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur (map fst d) $0 ]]
          * [[ nil_unless_in (map fst (Map.elements ms)) (map snd d) ]])%pred d' ]]
    OnCrash
      exists mscs', rep xp F (CommittedTxn cur) mscs'
    Begin
      cs <- BUFCACHE.write_array (DataStart xp)
        (sel (map fst (Map.elements ms)) i $0) (sel (map snd (Map.elements ms)) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx ^(ms, cs).

  Theorem apply_unsync_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (CommittedTxn m) mscs
    POST RET:mscs
      rep xp F (AppliedUnsyncTxn m) mscs
    CRASH
      exists mscs', rep xp F (CommittedTxn m) mscs'
    >} apply_unsync xp mscs.
  Proof.
    unfold apply_unsync; log_unfold.

    step.
    eapply valid_entries_replay'; eauto.
    apply equal_unless_in_replay_eq.
    pose proof (replay_twice) as Hx; unfold replay at 2 in Hx.
    rewrite Hx; auto.
    eapply nil_combine_nil_unless_in; eauto.

    step.
    eapply helper_valid_entries_addr_valid; eauto.

    step.
    rewrite fst_upd_prepend.
    erewrite wordToNat_plusone by eauto.
    rewrite replay_skipn_progress; auto.
    abstract solve_lengths.

    rewrite fst_upd_prepend.
    erewrite wordToNat_plusone by eauto.
    eapply equal_unless_in_S; eauto.

    apply nil_unless_in_prepend; auto.
    apply in_sel.
    abstract solve_lengths.

    cancel; auto.
    eapply equal_unless_in_trans_nil; eauto.
    eapply equal_unless_in_replay'.
    eapply equal_unless_in_bwd; eauto.
    hypmatch (array (DataStart xp) l2) as Hx.
    setoid_rewrite array_max_length_pimpl with (l := l2) in Hx.
    destruct_lift Hx; replace (length l) with (length l2); auto.
    abstract solve_equal_unless_in_length.

    cancel; auto.
    apply equal_unless_in_combine.
    rewrite fst_upd_prepend.
    eapply equal_unless_in_trans_upd_in; eauto.
    hypmatch (array (DataStart xp) l2) as Hx.
    setoid_rewrite array_max_length_pimpl with (l := l2) in Hx.
    destruct_lift Hx; rewrite map_length; auto.

    apply nil_unless_in_equal_unless_in.
    apply nil_unless_in_prepend; auto.
    apply in_sel; solve_lengths.
    rewrite map_length; rewrite upd_prepend_length.
    abstract solve_equal_unless_in_length.
    hypmatch (array (DataStart xp) l2) as Hx.
    setoid_rewrite array_max_length_pimpl with (l := l2) in Hx.
    destruct_lift Hx; replace (length l) with (length l2); auto.
    abstract solve_equal_unless_in_length.

    step.
    apply equal_arrays; auto.
    rewrite <- combine_map_fst_snd at 1.
    f_equal.
    eapply replay'_terminate_replay; eauto.
    abstract solve_equal_unless_in_length.

    eapply replay_unsync_crash; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply_unsync _ _) _) => apply apply_unsync_ok : prog.

  Definition apply_sync T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (cs) <- For i < $ (Map.cardinal ms)
    Ghost [ cur F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal ms))
          * log_rep xp cur ms
          * exists cur_unflushed, data_rep xp (List.combine cur cur_unflushed)
          * [[ length cur = length cur_unflushed ]]
          * [[ nil_unless_in (skipn (wordToNat i) (map fst (Map.elements ms))) cur_unflushed ]])%pred d' ]]
    OnCrash
      exists mscs', rep xp F (AppliedUnsyncTxn cur) mscs'
    Begin
      cs <- BUFCACHE.sync_array (DataStart xp) (sel (map fst (Map.elements ms)) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    cs <- BUFCACHE.write (LogHeader xp) (header_to_valu (mk_header 0)) cs;
    rx ^(ms, cs).

  Lemma nil_unless_in_S : forall n l ms,
    nil_unless_in (skipn n ms) l
    -> nil_unless_in (skipn (S n) ms) (upd l (selN ms n $0) nil).
  Proof.
    unfold nil_unless_in, upd, sel; intros.
    destruct (Nat.eq_dec (# (selN ms n $0)) (# a)).
    rewrite e; rewrite selN_updN_eq_default; auto.
    rewrite selN_updN_ne; auto.
    apply H. contradict H0.
    eapply in_skipn_S; eauto.
    apply wordToNat_neq_inj; eauto.
  Qed.

  Lemma helper_upd_sync_pimpl : forall m d l ms s a,
    length (replay m d) = length l
    -> array s (upd_sync (List.combine (replay m d) l) (sel ms a $0) ($0, nil)) $1
    =p=> array s (List.combine (replay m d) (upd l (sel ms a $0) nil)) $1.
  Proof.
    intros.
    apply equal_arrays; auto; unfold upd_sync.
    rewrite <- combine_upd; f_equal.
    eapply selN_eq_updN_eq; unfold sel.
    rewrite selN_combine; simpl; eauto.
  Qed.

  Lemma repeat_selN_is : forall A l (a def : A),
    (forall i, selN l i def = a)
    -> l = repeat a (length l).
  Proof.
    induction l; intros; auto.
    erewrite <- (H 0). simpl.
    unfold repeat; fold repeat.
    f_equal.
    pose proof (H 0); simpl in H0; subst.
    eapply IHl with (def := def); intro.
    rewrite <- (H (S i)).
    simpl; auto.
  Qed.

  Lemma nil_unless_in_oob' : forall n l n' ms,
    nil_unless_in (skipn n ms) l
    -> goodSizeEq addrlen (length l)
    -> n = length ms
    -> n' = length l
    -> l = repeat nil n'.
  Proof.
    intros; subst.
    rewrite skipn_oob in H by auto.
    unfold nil_unless_in, sel in *.
    apply repeat_selN_is with (def := nil); intro.
    destruct (lt_dec i (pow2 addrlen)).
    erewrite <- (H (natToWord addrlen i)) at 2; auto.
    f_equal.
    erewrite wordToNat_natToWord_idempotent'; eauto.
    rewrite selN_oob; auto.
    unfold goodSizeEq in H0.
    omega.
  Qed.

  Lemma nil_unless_in_oob : forall n l n' ms F xp l' d m ,
    nil_unless_in (skipn n ms) l
    -> n = length ms
    -> n' = length l
    -> (F * array xp (List.combine (replay l' d) l) $ (1))%pred m
    -> length (replay l' d) = length l
    -> l = repeat nil n'.
  Proof.
    intros.
    eapply nil_unless_in_oob'; eauto.
    rewrite array_max_length_pimpl in H2.
    destruct_lift H2.
    erewrite <- combine_length_eq2; eauto.
  Qed.

  Theorem apply_sync_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (AppliedUnsyncTxn m) mscs
    POST RET:mscs
      rep xp F (AppliedTxn m) mscs
    CRASH
      exists mscs', rep xp F (AppliedUnsyncTxn m) mscs' \/ rep xp F (AppliedTxn m) mscs'
    >} apply_sync xp mscs.
  Proof.
    unfold apply_sync; log_unfold.
    step.
    step.

    (* address passed to [sync_array] is in-bounds *)
    rewrite combine_length_eq by auto.
    apply valid_entries_addr_valid; auto.

    (* updating the (List.combine cur cur_unflushed) *)
    (* cannot [step], it will unify length _ = length _ *)
    eapply pimpl_ok2; eauto with prog; intros; cancel.
    apply helper_upd_sync_pimpl; auto.
    rewrite length_upd; auto.

    (* nil_unless_in for one less item *)
    erewrite wordToNat_plusone; eauto.
    apply nil_unless_in_S; auto.

    (* crash condition *)
    or_l; cancel; auto.
    eapply nil_unless_in_bwd; eauto.

    or_l; cancel; auto.
    cancel.
    apply helper_upd_sync_pimpl; auto.
    rewrite length_upd; auto.
    eapply nil_unless_in_bwd.
    eapply nil_unless_in_S; eauto.

    step.
    step.

    apply equal_arrays; auto; f_equal.
    eapply nil_unless_in_oob; eauto.
    abstract solve_lengths.

    or_l; cancel; auto.
    eapply nil_unless_in_bwd; eauto.

    or_r; cancel; auto.
    cancel.
    apply equal_arrays; auto; f_equal.
    eapply nil_unless_in_oob; eauto.
    abstract solve_lengths.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply_sync _ _) _) => apply apply_sync_ok : prog.

  Lemma helper_apply_goodSize : forall F xp d ms m,
    (F * rep_inner xp (AppliedUnsyncTxn (replay ms d)) ms)%pred m
    -> goodSizeEq addrlen (length d).
  Proof.
    log_unfold; intros.
    setoid_rewrite array_max_length_pimpl in H.
    destruct_lift H.
    erewrite <- replay_length.
    erewrite <- combine_length_eq; eauto.
  Qed.

  Definition apply T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    let^ (ms, cs) <- apply_unsync xp ^(ms, cs);
    let^ (ms, cs) <- apply_sync xp ^(ms, cs);
    cs <- BUFCACHE.sync (LogHeader xp) cs;
    rx ^(ms_empty, cs).

  Theorem apply_ok: forall xp mscs,
    {< m F,
    PRE
      rep xp F (CommittedTxn m) mscs
    POST RET:mscs
      rep xp F (NoTransaction m) mscs
    CRASH
      exists mscs', rep xp F (CommittedTxn m) mscs' \/
                    rep xp F (AppliedTxn m) mscs' \/
                    rep xp F (NoTransaction m) mscs'
    >} apply xp mscs.
  Proof.
    unfold apply.
    step; try cancel.
    step; try solve [ cancel ].

    unfold rep_inner.
    step.
    step.
    log_unfold.
    cancel.
    rewrite <- avail_region_grow_all by eauto.
    cancel; eauto.

    unfold rep_inner.
    cancel.
    or_r; or_r.
    cancel.
    log_unfold.
    cancel.
    rewrite <- avail_region_grow_all by eauto.
    cancel; eauto.
    apply MapFacts.Equal_refl.

    or_l.
    cancel.
    log_unfold.
    cancel; auto.

    apply equal_unless_in_combine.
    rewrite map_fst_combine by auto.
    apply equal_unless_in_replay_eq.
    rewrite replay_twice; auto.

    rewrite map_snd_combine by auto.
    apply nil_unless_in_equal_unless_in; auto.
    erewrite <- replay_length; eauto.
    eapply helper_apply_goodSize; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (apply _ _) _) => apply apply_ok : prog.

  Definition commit T xp (mscs : memstate_cachestate) rx : prog T :=
    let '^(ms, cs) := mscs in
    If (bool_dec (Map.is_empty ms) true) {
      rx ^(^(ms, cs), true)
    } else {
      let^ (mscs, ok) <- flush xp ^(ms, cs);
      let '^(ms, cs) := mscs in
      If (bool_dec ok true) {
        cs <- BUFCACHE.write (LogHeader xp) (header_to_valu (mk_header (Map.cardinal ms))) cs;
        cs <- BUFCACHE.sync (LogHeader xp) cs;
        let^ (ms, cs) <- apply xp ^(ms, cs);
        rx ^(^(ms, cs), true)
      } else {
        let^ (ms, cs) <- abort xp ^(ms, cs);
        rx ^(^(ms, cs), false)
      }
    }.

  Definition would_recover_old' xp old :=
    (exists ms, rep_inner xp (NoTransaction old) ms \/
     (exists cur, rep_inner xp (ActiveTxn old cur) ms))%pred.

  Definition would_recover_old xp F old :=
    (exists cs d, BUFCACHE.rep cs d * [[ (F * would_recover_old' xp old)%pred d ]])%pred.

  Definition would_recover_either' xp old cur :=
    (exists ms,
      rep_inner xp (NoTransaction old) ms \/
      (exists x, rep_inner xp (ActiveTxn old x) ms) \/
      rep_inner xp (CommittedTxn old) ms \/
      rep_inner xp (AppliedTxn old) ms \/
      rep_inner xp (FlushedUnsyncTxn old cur) ms \/
      rep_inner xp (CommittedUnsyncTxn old cur) ms \/
      rep_inner xp (CommittedTxn cur) ms \/
      rep_inner xp (AppliedTxn cur) ms \/
      rep_inner xp (NoTransaction cur) ms)%pred.

  Definition would_recover_either_pred' xp old curpred :=
    (exists ms,
      rep_inner xp (NoTransaction old) ms \/
      (exists x, rep_inner xp (ActiveTxn old x) ms) \/
      rep_inner xp (CommittedTxn old) ms \/
      rep_inner xp (AppliedTxn old) ms \/
      (exists cur, rep_inner xp (FlushedUnsyncTxn old cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (CommittedUnsyncTxn old cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (CommittedTxn cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (AppliedTxn cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (NoTransaction cur) ms * [[ curpred (list2mem cur) ]]))%pred.

  Definition would_recover_either xp F old cur :=
    (exists cs d, BUFCACHE.rep cs d * [[ (F * would_recover_either' xp old cur)%pred d ]])%pred.

  Definition would_recover_either_pred xp F old curpred :=
    (exists cs d, BUFCACHE.rep cs d * [[ (F * would_recover_either_pred' xp old curpred)%pred d ]])%pred.

  Hint Extern 0 (okToUnify (would_recover_old _ _ _) (would_recover_old _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (SepAuto.okToUnify (would_recover_old _ _ _) (would_recover_old _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (would_recover_either _ _ _ _) (would_recover_either _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (SepAuto.okToUnify (would_recover_either _ _ _ _) (would_recover_either _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (would_recover_either_pred _ _ _ _) (would_recover_either_pred _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (SepAuto.okToUnify (would_recover_either_pred _ _ _ _) (would_recover_either_pred _ _ _ _)) => constructor : okToUnify.

  Theorem commit_ok: forall xp mscs,
    {< m1 m2 F,
     PRE            rep xp F (ActiveTxn m1 m2) mscs
     POST RET:^(mscs,r)
                    ([[ r = true ]] * rep xp F (NoTransaction m2) mscs) \/
                    ([[ r = false ]] * rep xp F (NoTransaction m1) mscs)
     CRASH          would_recover_either xp F m1 m2
    >} commit xp mscs.
  Proof.
    unfold commit, would_recover_either, would_recover_either'.
    hoare_with log_unfold ltac:(eauto with replay).
    + or_l.
      cancel_with ltac:(eauto with replay).
      apply Map.is_empty_2 in H10.
      unfold replay, replay'.
      destruct (MapProperties.elements_Empty m) as [He ?].
      rewrite He by auto.
      auto.
      apply Map.is_empty_2 in H10.
      pose proof (@Map.empty_1 valu).
      unfold ms_empty.
      hnf. intros.
      hnf in H10.
      eapply eq_trans.
      apply MapFacts.not_find_in_iff.
      intro Hi.
      hnf in Hi.
      destruct Hi as [v ?].
      eapply H10; eauto.
      apply eq_sym.
      apply MapFacts.not_find_in_iff.
      intro Hi.
      hnf in Hi.
      destruct Hi as [v ?].
      eapply H; eauto.
    + or_r; or_r; or_r; or_r; or_r; or_r.
      or_l. cancel. cancel.
      eauto with replay.
      eauto.
      congruence.
    + or_r; or_r; or_r; or_r; or_r; or_r; or_r.
      or_l. cancel. cancel.
      rewrite H18. cancel.
      eauto.
      congruence.
    + repeat or_r. cancel.
      rewrite H18. cancel.
      eauto.
    + or_r. or_l.
      unfold avail_region.
      cancel.
      array_match.
      reflexivity.
      solve_lengths.
    + or_r; or_r; or_r; or_r.
      or_l. cancel. cancel.
      solve_lengths.
  Qed.

  Hint Extern 1 ({{_}} progseq (commit _ _) _) => apply commit_ok : prog.

  Definition read_log T (xp : log_xparams) cs rx : prog T :=
    let^ (cs, d) <- BUFCACHE.read (LogDescriptor xp) cs;
    let desc := valu_to_descriptor d in
    let^ (cs, h) <- BUFCACHE.read (LogHeader xp) cs;
    let len := (valu_to_header h) :-> "length" in
    let^ (cs, log) <- For i < len
    Ghost [ cur log_on_disk F ]
    Loopvar [ cs log_prefix ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * (LogHeader xp) |=> header_to_valu (mk_header (Map.cardinal log_on_disk))
          * exists old d, data_rep xp d
          * cur_rep old log_on_disk cur
          * log_rep xp old log_on_disk
            (* If something's in the transaction, it doesn't matter what state it's in on disk *)
          * [[ equal_unless_in (map fst (Map.elements log_on_disk)) (synced_list old) d ($0, nil) ]]
          * [[ log_prefix = firstn (wordToNat i) (Map.elements log_on_disk) ]])%pred d' ]]
    OnCrash
      exists mscs, rep xp F (CommittedTxn cur) mscs
    Begin
      let^ (cs, v) <- BUFCACHE.read_array (LogData xp) i cs;
      lrx ^(cs, log_prefix ++ [(sel desc i $0, v)])
    Rof ^(cs, []);
    rx ^(MapProperties.of_list log, cs).

  Theorem read_log_ok: forall xp cs,
    {< m ms F,
    PRE
      rep xp F (CommittedTxn m) ^(ms, cs)
    POST RET:^(r,cs)
      [[ Map.Equal r ms ]] * rep xp F (CommittedTxn m) ^(ms, cs)
    CRASH
      exists mscs', rep xp F (CommittedTxn m) mscs'
    >} read_log xp cs.
  Proof.
    unfold read_log; log_unfold.
    hoare.
    instantiate (1 := (List.combine (map snd (Map.elements (elt:=valu) m))
     (repeat [] (length (map snd (Map.elements (elt:=valu) m)))))).
    autorewrite_fast. cancel.
    rewrite header_valu_id in *.
    rec_simpl.
    simpl in H.
    solve_lengths.
    eauto with replay.
    rewrite header_valu_id in *.
    rec_simpl.
    assert (# m1 < length (Map.elements m)).
    solve_lengths.
    replace (# (m1 ^+ $ 1)) with (# m1 + 1).
    erewrite firstn_plusone_selN'.
    eauto.
    rewrite descriptor_valu_id.
    unfold sel.
    rewrite selN_app1 by solve_lengths.
    autorewrite with lists.
    repeat erewrite selN_map by auto.
    simpl.
    rewrite <- surjective_pairing.
    auto.
    solve_lengths.
    unfold Rec.well_formed; simpl.
    intuition.
    auto.
    word2nat_clear.
    word2nat_auto.
    cancel.
    eauto with replay.
    eauto.
    rewrite header_valu_id.
    rewrite firstn_oob.
    apply MapProperties.of_list_3.
    rec_simpl.
    simpl.
    solve_lengths.
    eauto with replay.
    cancel.
    auto.
    Unshelve.
    repeat constructor. exact $0.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_log _ _) _) => apply read_log_ok : prog.

  Definition recover T (xp: log_xparams) cs rx : prog T :=
    let^ (ms, cs) <- read_log xp cs;
    let^ (ms, cs) <- apply xp ^(ms, cs);
    rx ^(ms, cs).

  Lemma crash_invariant_synced_array: forall l start stride,
    crash_xform (array start (List.combine l (repeat nil (length l))) stride) =p=>
    array start (List.combine l (repeat nil (length l))) stride.
  Proof.
    unfold array.
    induction l; intros; simpl; auto.
    autorewrite with crash_xform.
    cancel.
    auto.
  Qed.
  Hint Rewrite crash_invariant_synced_array : crash_xform.

  Definition possible_crash_list (l: list valuset) (l': list valu) :=
    length l = length l' /\ forall i, i < length l -> In (selN l' i $0) (valuset_list (selN l i ($0, nil))).

  Lemma crash_xform_array: forall l start stride,
    crash_xform (array start l stride) =p=>
      exists l', [[ possible_crash_list l l' ]] * array start (List.combine l' (repeat nil (length l'))) stride.
  Proof.
    unfold array, possible_crash_list.
    induction l; intros.
    cancel.
    instantiate (a := nil).
    simpl; auto.
    auto.
    autorewrite with crash_xform.
    rewrite IHl.
    cancel; [ instantiate (a := w :: l0) | .. ]; simpl; auto; fold repeat; try cancel;
      destruct i; simpl; auto;
      destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_invariant_avail_region: forall start len,
    crash_xform (avail_region start len) =p=> avail_region start len.
  Proof.
    unfold avail_region.
    intros.
    autorewrite with crash_xform.
    norm'l.
    unfold stars; simpl.
    autorewrite with crash_xform.
    rewrite crash_xform_array.
    unfold possible_crash_list.
    cancel.
    solve_lengths.
  Qed.
  Hint Rewrite crash_invariant_avail_region : crash_xform.

  Lemma valid_entries_lengths_eq : forall l1 l2 m,
    length l1 = length l2 -> valid_entries l1 m -> valid_entries l2 m.
  Proof.
    unfold valid_entries, indomain'.
    intuition.
    rewrite <- H; eauto.
  Qed.

  Lemma possible_crash_equal_unless_in : forall l0 l1 l2 (m: memstate),
    equal_unless_in (map fst (Map.elements m)) (List.combine l0 (repeat [] (length l0))) l1 ($0, nil) ->
    possible_crash_list l1 l2 ->
    equal_unless_in (map fst (Map.elements m)) l0 l2 $0.
  Proof.
    unfold equal_unless_in, possible_crash_list.
    intros.
    assert (length l0 = length l1).
    autorewrite with lengths in *.
    rewrite Nat.min_r in * by auto.
    intuition.
    split.
    intuition.
    intros.
    destruct (lt_dec n (length l0)).
    destruct H.
    destruct H0.
    specialize (H3 n).
    specialize (H4 n).
    autorewrite with lists in *.
    rewrite repeat_selN in * by auto.
    rewrite <- H3 in H4.
    simpl in H4.
    elim H4; intuition.
    intuition.
    solve_lengths.
    repeat rewrite selN_oob by omega.
    auto.
  Qed.

  Ltac word_discriminate :=
    match goal with [ H: $ _ = $ _ |- _ ] => solve [
      apply natToWord_discriminate in H; [ contradiction | rewrite valulen_is; apply leb_complete; compute; trivial]
    ] end.

  Ltac cancel_pred_crash :=
    eapply pred_apply_crash_xform; eauto;
    autorewrite with crash_xform;
    cancel; subst; cancel.

  Lemma equal_unless_in_refl : forall A ms l d,
    @equal_unless_in A ms l l d.
  Proof.
    unfold equal_unless_in; intuition.
  Qed.
  Hint Resolve equal_unless_in_refl : replay.

  Lemma would_recover_old'_either' : forall xp old,
    would_recover_old' xp old =p=> would_recover_either' xp old old.
  Proof.
    unfold would_recover_old', would_recover_either'.
    cancel.
  Qed.

  Lemma would_recover_old_either : forall xp F old,
    would_recover_old xp F old =p=> would_recover_either xp F old old.
  Proof.
    unfold would_recover_old, would_recover_either.
    cancel.
    apply would_recover_old'_either'.
  Qed.

  Lemma would_recover_old'_either_pred' : forall xp old p,
    would_recover_old' xp old =p=> would_recover_either_pred' xp old p.
  Proof.
    unfold would_recover_old', would_recover_either_pred'.
    cancel.
  Qed.

  Lemma would_recover_old_either_pred : forall xp F old p,
    would_recover_old xp F old =p=> would_recover_either_pred xp F old p.
  Proof.
    unfold would_recover_old, would_recover_either_pred.
    cancel.
    apply would_recover_old'_either_pred'.
  Qed.

  Lemma would_recover_either'_pred'_diskIs : forall xp old new,
    would_recover_either' xp old new =p=> would_recover_either_pred' xp old (diskIs (list2mem new)).
  Proof.
    unfold would_recover_either', would_recover_either_pred'.
    (* split up manually because the automated search takes too long to find the 8th OR *)
    intros; norm; intuition; unfold stars; simpl.
    cancel.
    cancel.
    cancel.
    cancel.
    do 4 or_r. or_l. cancel.
    do 5 or_r. or_l. cancel.
    do 6 or_r. or_l. cancel.
    do 7 or_r. or_l. cancel.
    repeat or_r. cancel.
  Qed.

  Lemma would_recover_either_pred_diskIs : forall xp F old new,
    would_recover_either xp F old new =p=> would_recover_either_pred xp F old (diskIs (list2mem new)).
  Proof.
    unfold would_recover_either, would_recover_either_pred.
    cancel.
    rewrite would_recover_either'_pred'_diskIs.
    cancel.
  Qed.

  Lemma would_recover_either_pred'_diskIs_rev : forall xp old new,
    goodSizeEq addrlen (length new) ->
    would_recover_either_pred' xp old (diskIs (list2mem new)) =p=>
    would_recover_either' xp old new.
  Proof.
    unfold would_recover_either_pred', would_recover_either'.
    intros; norm; intuition; unfold stars; simpl; unfold diskIs in *.
    - cancel.
    - cancel.
    - cancel.
    - cancel.
    - do 4 or_r. or_l.
      unfold rep_inner, data_rep, cur_rep.
      setoid_rewrite array_max_length_pimpl at 1.
      cancel.
      eapply list2mem_inj; eauto.
      rewrite replay_length. rewrite length_synced_list in *. auto.
    - do 5 or_r. or_l.
      unfold rep_inner, data_rep, cur_rep.
      setoid_rewrite array_max_length_pimpl at 1.
      cancel.
      eapply list2mem_inj; eauto.
      rewrite replay_length. rewrite length_synced_list in *. auto.
    - do 6 or_r. or_l.
      unfold rep_inner, data_rep, cur_rep.
      setoid_rewrite array_max_length_pimpl at 1.
      cancel.
      unfold equal_unless_in in *; intuition.
      eapply list2mem_inj; eauto.
      rewrite replay_length. rewrite length_synced_list in *. rewrite H0 in *. auto.
    - do 7 or_r. or_l.
      unfold rep_inner, data_rep, cur_rep.
      setoid_rewrite array_max_length_pimpl at 1.
      cancel.
      replace (replay m d) with (new); try cancel.
      eapply list2mem_inj; eauto.
      rewrite length_synced_list in *. rewrite replay_length in *. auto.
      eapply list2mem_inj; eauto.
      rewrite length_synced_list in *. rewrite replay_length in *. auto.
    - repeat or_r.
      unfold rep_inner, data_rep, cur_rep.
      setoid_rewrite array_max_length_pimpl at 1.
      cancel.
      replace (a) with (new); try cancel.
      eapply list2mem_inj; eauto.
      rewrite length_synced_list in *. auto.
      eauto.
  Qed.

  Lemma would_recover_either_pred_diskIs_rev : forall xp F old new,
    goodSizeEq addrlen (length new) ->
    would_recover_either_pred xp F old (diskIs (list2mem new)) =p=>
    would_recover_either xp F old new.
  Proof.
    unfold would_recover_either_pred, would_recover_either.
    intros; cancel.
    apply would_recover_either_pred'_diskIs_rev; auto.
  Qed.

  Lemma would_recover_either'_pred'_pimpl : forall xp old new p,
    would_recover_either' xp old new * [[ p (list2mem new) ]] =p=> would_recover_either_pred' xp old p.
  Proof.
    unfold would_recover_either', would_recover_either_pred'.
    (* split up manually because the automated search takes too long to find the 8th OR *)
    intros; norm; intuition; unfold stars; simpl.
    cancel.
    cancel.
    cancel.
    cancel.
    do 4 or_r. or_l. cancel.
    do 5 or_r. or_l. cancel.
    do 6 or_r. or_l. cancel.
    do 7 or_r. or_l. cancel.
    repeat or_r. cancel.
  Qed.

  Lemma would_recover_either_pred_pimpl : forall xp F old new p,
    would_recover_either xp F old new * [[ p (list2mem new) ]] =p=> would_recover_either_pred xp F old p.
  Proof.
    unfold would_recover_either, would_recover_either_pred.
    cancel.
    rewrite <- would_recover_either'_pred'_pimpl.
    cancel.
  Qed.

  Lemma notxn_would_recover_old : forall xp F old mscs,
    rep xp F (NoTransaction old) mscs =p=> would_recover_old xp F old.
  Proof.
    unfold would_recover_old, would_recover_old'.
    cancel. cancel.
  Qed.

  Lemma activetxn_would_recover_old : forall xp F old new mscs,
    rep xp F (ActiveTxn old new) mscs =p=> would_recover_old xp F old.
  Proof.
    unfold would_recover_old, would_recover_old'.
    cancel. cancel.
  Qed.

  Lemma notxn_bounded_length : forall xp F old mscs,
    rep xp F (NoTransaction old) mscs =p=>
    rep xp F (NoTransaction old) mscs * [[ goodSizeEq addrlen (length old) ]].
  Proof.
    unfold rep; cancel.
    unfold rep_inner, data_rep, synced_list in H0.
    assert (goodSizeEq addrlen (length (List.combine old (repeat (@nil valu) (length old))))).
    eapply array_max_length_F with (start:=DataStart _).
    pred_apply' H0. cancel.
    rewrite combine_length in *.
    rewrite repeat_length in *.
    rewrite Nat.min_idempotent in *.
    auto.
  Qed.

  (**
   * [after_crash_pred'] is similar to [would_recover_either_pred'] but describes
   * states after a crash (i.e., after [crash_xform]).  This is a smaller set of
   * different states that we have to consider.
   *)
  Definition after_crash_pred' xp old curpred :=
    (exists ms,
      rep_inner xp (NoTransaction old) ms \/
      rep_inner xp (CommittedTxn old) ms \/
      (exists cur, rep_inner xp (CommittedTxn cur) ms * [[ curpred (list2mem cur) ]]) \/
      (exists cur, rep_inner xp (NoTransaction cur) ms * [[ curpred (list2mem cur) ]]))%pred.

  Lemma crash_xform_would_recover_either_pred' : forall fsxp old curpred,
    crash_xform (would_recover_either_pred' fsxp old curpred) =p=>
    after_crash_pred' fsxp old curpred.
  Proof.
    intros.
    unfold would_recover_either_pred', after_crash_pred'.
    autorewrite with crash_xform.
    repeat setoid_rewrite crash_xform_or_dist.
    setoid_rewrite crash_xform_exists_comm.
    norm'l; unfold stars; simpl.
    rewrite sep_star_comm. rewrite star_emp_pimpl.
    repeat apply pimpl_or_l; unfold rep_inner at 1;
      unfold data_rep, log_rep, log_rep_empty, log_rep_unsynced, synced_list, cur_rep.

    - (* NoTransaction old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. cancel.

      or_l.
      unfold rep_inner, data_rep, log_rep_empty. cancel.
      eauto.

    - (* ActiveTxn old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. cancel.

      or_l.
      unfold rep_inner, data_rep, log_rep_empty. cancel.
      eapply MapFacts.Equal_refl.

    - (* CommittedTxn old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. rewrite crash_xform_array. cancel.

      or_r. or_l.
      unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
      cancel; auto.
      unfold possible_crash_list in *.
      unfold equal_unless_in in H7.
      intuition.
      autorewrite with lengths in H1.
      rewrite Nat.min_l in H1 by auto.
      eapply valid_entries_lengths_eq; [ | eauto ]. congruence.
      eapply equal_unless_in_replay_eq.
      eapply possible_crash_equal_unless_in; eauto.

    - (* AppliedTxn old *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. intuition.

      + (* Header change applied too *)
        cancel.
        or_l.
        unfold rep_inner, data_rep, log_rep_empty. cancel.
        apply avail_region_grow_all; auto.
        eapply MapFacts.Equal_refl.

      + (* Header change was lost *)
        cancel.
        or_r. or_l.
        unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
        cancel. cancel.
        rewrite replay_twice; auto.

    - (* FlushedUnsyncTxn old new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      rewrite crash_xform_array. norm'r; [ | intuition ].
      or_l.
      log_unfold. unfold avail_region, valid_size in *.
      norm'l.
      match goal with
      | [ H : possible_crash_list _ _ |- _ ] =>
        unfold possible_crash_list in H; destruct H as [H ?];
        autorewrite with lengths in H; rewrite Nat.min_r in H by solve_lengths
      end.
      norm'r; [ cancel' | intuition idtac ].
      rewrite valu_descriptor_id.
      cancel; rewrite array_app by solve_lengths; cancel.
      apply MapFacts.Equal_refl.
      auto.
      rewrite Forall_forall; intuition.
      solve_lengths.
      apply MapFacts.Equal_refl.
      auto.
      rewrite Forall_forall; intuition.
      solve_lengths.

    - (* CommittedUnsyncTxn old new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. intuition.

      + (* Commit bit applied *)
        cancel.
        or_r. or_r. or_l.
        unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
        cancel. cancel.

      + (* Commit bit lost *)
        cancel.
        or_l.
        unfold rep_inner, data_rep, log_rep_empty. cancel.
        apply avail_region_grow_all; auto.
        eapply MapFacts.Equal_refl.

    - (* CommittedTxn new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. rewrite crash_xform_array. cancel.

      or_r. or_r. or_l.
      unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
      cancel.
      cancel.
      unfold possible_crash_list in *.
      unfold equal_unless_in in H8.
      intuition.
      autorewrite with lengths in H1.
      rewrite Nat.min_l in H1 by auto.
      eapply valid_entries_lengths_eq; [ | eauto ]. congruence.
      assert (replay m l = replay m l2).
      eapply equal_unless_in_replay_eq.
      eapply possible_crash_equal_unless_in; eauto.
      congruence.

    - (* AppliedTxn new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. intuition.

      + (* Header change applied too *)
        autorewrite with crash_xform. norm'l; unfold stars; simpl.
        autorewrite with crash_xform. cancel.

        or_r. or_r. or_r.
        unfold rep_inner, data_rep, log_rep_empty. cancel.
        apply avail_region_grow_all; auto.
        eapply MapFacts.Equal_refl.

      + (* Header change was lost *)
        autorewrite with crash_xform. norm'l; unfold stars; simpl.
        autorewrite with crash_xform. cancel.

        or_r. or_r. or_l.
        unfold rep_inner, data_rep, log_rep, synced_list, cur_rep.
        cancel. cancel.
        rewrite replay_twice; eauto.

    - (* NoTransaction new *)
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. norm'l; unfold stars; simpl.
      autorewrite with crash_xform. cancel.

      or_r. or_r. or_r.
      unfold rep_inner, data_rep, log_rep_empty. cancel.
      eapply MapFacts.Equal_refl.

  Qed.

  Hint Rewrite crash_xform_would_recover_either_pred' : crash_xform.

  Lemma after_crash_pred'_would_recover_either_pred' : forall fsxp old curpred,
    after_crash_pred' fsxp old curpred =p=>
    would_recover_either_pred' fsxp old curpred.
  Proof.
    unfold after_crash_pred', would_recover_either_pred'.
    intros; norm'l; unfold stars; simpl.
    rewrite sep_star_comm. rewrite star_emp_pimpl.
    repeat apply pimpl_or_l.
    cancel.
    cancel.
    cancel.
    (* the automated search takes too long to get to the 8th OR branch.. *)
    norm; unfold stars; simpl; auto.
    repeat or_r. cancel.
  Qed.


  Theorem recover_ok: forall xp cs,
    {< m1 m2pred F,
    PRE
      exists d, BUFCACHE.rep cs d *
      [[ crash_xform (F * would_recover_either_pred' xp m1 m2pred)%pred d ]]
    POST RET:mscs
      rep xp (crash_xform F) (NoTransaction m1) mscs \/
      exists m2,
      rep xp (crash_xform F) (NoTransaction m2) mscs * [[ m2pred (list2mem m2) ]]
    CRASH
      would_recover_either_pred xp (crash_xform F) m1 m2pred
    >} recover xp cs.
  Proof.
    unfold recover, would_recover_either_pred.
    intros.
    eapply pimpl_ok2; eauto with prog.
    intros. norm'l. unfold stars; simpl.

    (* We need to split up all of the possible [rep] preconditions, because
     * this will decide what disk image to use for instantiating our evars.
     * We convert [crash_xform would_recover_either_pred'] into [after_crash_pred'],
     * which has fewer distinct states.
     *)

    (* XXX an odd setoid_rewrite issue: can't rewrite the top-level term? *)
    apply crash_xform_sep_star_dist in H4.
    autorewrite with crash_xform in H4.
    unfold after_crash_pred' in H4.
    destruct_lift H4.
    repeat ( apply sep_star_or_distr in H; apply pimpl_or_apply in H; destruct H;
      destruct_lift H ).

    - (* NoTransaction old *)
      cancel. instantiate (1:=ms_empty).
      unfold rep_inner, data_rep, synced_list.
      cancel.
      unfold log_rep_empty, log_rep, cur_rep.
      rewrite MapProperties.cardinal_1 by apply Map.empty_1.
      rewrite Nat.sub_0_r. ring_simplify (LogData xp ^+ $0).
      cancel.

      autorewrite with core.

      step.
      rewrite mapeq_rep.
      cancel.
      auto.
      step.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'; cancel.
      autorewrite with core; cancel. cancel.
      unfold would_recover_either_pred'; cancel.

    - (* CommittedTxn old *)
      cancel.
      step.
      rewrite mapeq_rep.
      cancel.
      auto.
      step.

      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'; cancel. cancel.
      cancel.
      unfold would_recover_either_pred'; cancel.

    - (* CommittedTxn new *)
      cancel.
      step.
      rewrite mapeq_rep.
      cancel.
      auto.
      step.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'. norm; unfold stars; simpl; auto. repeat or_r. cancel.
      (* [cancel] takes forever here *)
      repeat (apply pimpl_or_r; right).
      cancel.
      intuition.
      cancel.
      unfold would_recover_either_pred'; cancel.

    - (* NoTransaction new *)
      cancel. instantiate (1:=ms_empty).
      unfold rep_inner, data_rep, synced_list.
      cancel.
      unfold log_rep_empty, log_rep, cur_rep.
      rewrite MapProperties.cardinal_1 by apply Map.empty_1.
      rewrite Nat.sub_0_r. ring_simplify (LogData xp ^+ $0).
      cancel.

      autorewrite with core.
      step.
      rewrite mapeq_rep.
      cancel.
      auto.
      step.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'; cancel. cancel.
      unfold would_recover_either_pred'. norm; unfold stars; simpl; auto. repeat or_r. cancel.
      repeat (apply pimpl_or_r; right).
      cancel.
      autorewrite with core; cancel.
      unfold would_recover_either_pred'; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (recover _ _) _) => apply recover_ok : prog.

  Definition read_array T xp a i stride mscs rx : prog T :=
    let^ (mscs, r) <- read xp (a ^+ i ^* stride) mscs;
    rx ^(mscs, r).

  Definition write_array T xp a i stride v mscs rx : prog T :=
    mscs <- write xp (a ^+ i ^* stride) v mscs;
    rx mscs.

  Theorem read_array_ok : forall xp mscs a i stride,
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

  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _ _) _) => apply write_array_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ ?a) (rep _ _ _ ?a)) => constructor : okToUnify.

  (* XXX remove once SepAuto and SepAuto2 are unified *)
  Hint Extern 0 (SepAuto.okToUnify (rep _ _ _ ?a) (rep _ _ _ ?a)) => constructor : okToUnify.

End LOG.



Global Opaque LOG.begin.
Global Opaque LOG.abort.
Global Opaque LOG.write.
Global Opaque LOG.write_array.
Arguments LOG.rep : simpl never.
