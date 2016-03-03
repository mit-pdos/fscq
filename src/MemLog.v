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
Definition map0 := Map.empty valu.
Definition diskstate := list valu.

Definition KIn V := InA (@Map.eq_key V).
Definition KNoDup V := NoDupA (@Map.eq_key V).

Module MLog.

  Record memstate := mk_memstate {
    MSInLog : valumap;      (* memory state for committed (but unapplied) txns *)
    MSCache : cachestate    (* cache state *)
  }.

  Inductive logstate :=
  | Synced (d : diskstate)
  (* Synced state: both log and disk content are synced *)

  | Flushing (d : diskstate) (ents : DLog.contents)
  (* A transaction is being flushed to the log, but not sync'ed yet
   * e.g. DiskLog.ExtendedUnsync or DiskLog.Extended *)

  | Applying (d : diskstate)
  (* In the process of applying the log to real disk locations.
     Block content might or might not be synced.
     Log might be truncated but not yet synced.
     e.g. DiskLog.Synced or DiskLog.Truncated
   *)
  .

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

  Definition equal_unless_in (keys: list addr) (l1 l2: list valuset) :=
    length l1 = length l2 /\
    forall a,  ~ In a keys -> selN l1 a ($0, nil) = selN l2 a ($0, nil).

  Definition unsync_applying xp (ms : valumap) (old : diskstate) : rawpred :=
    (exists vs, [[ equal_unless_in (map_keys ms) (synced_list old) vs ]] *
     arrayN (DataStart xp) vs
    )%pred.

  Definition unsync_syncing xp (ms : valumap) (cur : diskstate) : rawpred :=
    (exists vs, [[ nil_unless_in (map_keys ms) vs /\ length vs = length cur ]] *
     arrayN (DataStart xp) (List.combine cur vs)
    )%pred.

  Definition map_valid (ms : valumap) (m : diskstate) :=
     forall a v, Map.MapsTo a v ms -> a <> 0 /\ a < length m.

  Definition log_valid (ents : DLog.contents) (m : diskstate) :=
     KNoDup ents /\ forall a v, KIn (a, v) ents -> a <> 0 /\ a < length m.

  Definition rep_inner xp na st ms :=
    ( exists log d0,
      [[ Map.Equal ms (replay_mem log map0) ]] *
      [[ goodSize addrlen (length d0) /\ map_valid ms d0 ]] *
    match st with
    | Synced d =>
        map_replay ms d0 d *
        synced_data xp d0 *
        DLog.rep xp (DLog.Synced na log)
    | Flushing d ents =>
        [[ log_valid ents d ]] *
        map_replay ms d0 d *
        synced_data xp d0 *
        (DLog.rep xp (DLog.ExtendedUnsync log)
      \/ DLog.rep xp (DLog.Extended log ents))
    | Applying d =>
        map_replay ms d0 d *
        (((DLog.rep xp (DLog.Synced na log)) *
          (unsync_applying xp ms d0))
      \/ ((DLog.rep xp (DLog.Synced na log)) *
          (unsync_syncing xp ms d))
      \/ ((DLog.rep xp (DLog.Truncated log)) *
          (synced_data xp d)))
    end)%pred.

  Definition rep xp F na st ms := 
    ( exists d, BUFCACHE.rep (MSCache ms) d *
      [[ (F * rep_inner xp na st (MSInLog ms))%pred d ]])%pred.

  Definition read T xp a ms rx : prog T :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    match Map.find a oms with
    | Some v => rx ^(ms, v)
    | None =>
        let^ (cs, v) <- BUFCACHE.read_array (DataStart xp) a cs;
        rx ^(mk_memstate oms cs, v)
    end.

  Definition flush_noapply T xp ents ms rx : prog T :=  
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    let^ (cs, ok) <- DLog.extend xp ents cs;
    If (bool_dec ok true) {
      rx ^(mk_memstate (replay_mem ents oms) cs, true)
    } else {
      rx ^(mk_memstate oms cs, false)
    }.

  Definition apply T xp ms rx : prog T :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    cs <- BUFCACHE.write_vecs (DataStart xp) (Map.elements oms) cs;
    cs <- BUFCACHE.sync_vecs (DataStart xp) (map_keys oms) cs;
    cs <- DLog.trunc xp cs;
    rx (mk_memstate map0 cs).

  Definition flush T xp ents ms rx : prog T :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    let^ (cs, na) <- DLog.avail xp cs;
    let ms := (mk_memstate oms cs) in
    ms' <- IfRx irx (lt_dec na (length ents)) {
      ms <- apply xp ms;
      irx ms
    } else {
      irx ms
    };
    r <- flush_noapply xp ents ms';
    rx r.


  Lemma map_valid_map0 : forall m,
    map_valid map0 m.
  Proof.
    unfold map_valid, map0; intuition; exfalso;
    apply MapFacts.empty_mapsto_iff in H; auto.
  Qed.



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

  Arguments DLog.rep: simpl never.
  Hint Extern 0 (okToUnify (DLog.rep _ _) (DLog.rep _ _)) => constructor : okToUnify.

  (* destruct memstate *)
  Ltac dems := eauto; try match goal with
  | [ H : @eq memstate ?ms (mk_memstate _ _ _) |- _ ] =>
     destruct ms; inversion H; subst
  end; eauto.

  Lemma replay_disk_length : forall l m,
    length (replay_disk l m) = length m.
  Proof.
    induction l; intros; simpl; auto.
    rewrite IHl.
    rewrite length_updN; auto.
  Qed.

  Hint Rewrite replay_disk_length : lists.

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


  Lemma map_valid_replay : forall d ms1 ms2,
    map_valid ms1 d ->
    map_valid ms2 d ->
    map_valid ms1 (replay_disk (Map.elements ms2) d).
  Proof.
    unfold map_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.

  Lemma map_valid_add : forall d a v ms,
    map_valid ms d ->
    a < length d -> a <> 0 ->
    map_valid (Map.add a v ms) d.
  Proof.
    unfold map_valid; intros.
    destruct (addr_eq_dec a0 a); subst.
    eauto.
    eapply H.
    eapply Map.add_3; eauto.
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

  Lemma replay_disk_none_selN : forall a v ms d def,
    Map.find a ms = None ->
    (exists F, F * a |-> v)%pred
      (list2nmem (replay_disk (Map.elements ms) d)) ->
    selN d a def = v.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel in H0 as Hx.
    rewrite Hx.
    rewrite replay_disk_selN_not_In; eauto;
    apply MapFacts.not_find_in_iff; auto.
  Qed.

  Lemma synced_data_replay_inb : forall a v c1 d,
    (exists F, F * a |-> v)%pred (list2nmem (replay_disk c1 d))
    -> a < length (synced_list d).
  Proof.
    unfold synced_list; intros.
    destruct H.
    apply list2nmem_ptsto_bound in H.
    autorewrite with lists in *; auto.
  Qed.

  Section UnfoldProof1.
  Local Hint Unfold rep map_replay rep_inner map_empty: hoare_unfold.

  Hint Extern 0 (okToUnify (synced_data ?a _) (synced_data ?a _)) => constructor : okToUnify.

  Theorem read_ok: forall xp ms a,
    {< F d na v,
    PRE
      rep xp F na (Synced d) ms *
      [[[ d ::: exists F', (F' * a |-> v) ]]]
    POST RET:^(ms', r)
      rep xp F na (Synced d) ms' * [[ r = v ]]
    CRASH
      exists ms', rep xp F na (Synced d) ms'
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.

    cancel.
    safestep; auto.  eauto. eauto. eauto.
    cancel. subst.
    eapply replay_disk_eq; eauto.
    pimpl_crash; cancel; auto. cancel.

    cancel.
    unfold synced_data; cancel.
    subst; eapply synced_data_replay_inb; eauto.

    prestep.
    cancel; subst; auto.
    unfold synced_list; unfold pred_apply in *.
    rewrite selN_combine by (autorewrite with lists; auto); simpl.
    eapply replay_disk_none_selN; eauto.

    pimpl_crash.
    norm.
    cancel.
    instantiate ( 2 := mk_memstate (MSInLog ms) cs').
    cancel.
    intuition; subst; simpl; eauto.
    pred_apply; cancel.
  Qed.

  End UnfoldProof1.

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

  Lemma replay_disk_replay_mem0 : forall l d,
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

    apply replay_disk_replay_mem0; auto.
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


  Lemma map_valid_replay_mem : forall d ms1 ms2,
    map_valid ms1 d ->
    map_valid ms2 d ->
    map_valid (replay_mem (Map.elements ms1) ms2) d.
  Proof.
    unfold map_valid; intros.
    destruct (MapFacts.In_dec ms1 a).
    apply MapFacts.in_find_iff in i.
    destruct (Map.find a ms1) eqn:X.
    eapply H.
    apply MapFacts.find_mapsto_iff; eauto.
    tauto.
    eapply H0.
    eapply replay_mem_not_in; eauto.
  Qed.

  Lemma map_add_repeat : forall V a (v : V) m,
    Map.Equal (Map.add a v (Map.add a v m)) (Map.add a v m).
  Proof.
    intros; hnf; intros.
    destruct (eq_nat_dec y a); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.add_neq_o by auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.

  Lemma map_merge_repeat' : forall l m,
    KNoDup l ->
    Map.Equal (replay_mem l (replay_mem l m)) (replay_mem l m).
  Proof.
    induction l; intros; auto.
    destruct a; inversion H; simpl; subst.
    rewrite replay_mem_add by auto.
    rewrite IHl by auto.
    setoid_rewrite replay_mem_add; auto.
    apply map_add_repeat.
  Qed.

  Lemma map_merge_repeat : forall a b,
    Map.Equal (map_merge (map_merge a b) b) (map_merge a b).
  Proof.
    unfold map_merge; intros.
    apply map_merge_repeat'.
    apply Map.elements_3w.
  Qed.

  Local Hint Resolve Map.is_empty_1 Map.is_empty_2.

  Lemma eq_key_dec : forall V (a b : Map.key * V),
    {Map.eq_key a b} + {~ Map.eq_key a b}.
  Proof.
    intros; destruct a, b.
    destruct (addr_eq_dec k k0); subst.
    left; hnf; auto.
    right; hnf. tauto.
  Qed.


  Lemma map_valid_replay_mem' : forall ents d ms,
    log_valid ents d ->
    map_valid ms d ->
    map_valid (replay_mem ents ms) d.
  Proof.
    unfold map_valid, log_valid; intros.
    destruct (InA_dec (@eq_key_dec valu) (a, v) ents).
    eapply H; eauto.
    eapply H0.
    eapply replay_mem_not_in'; eauto.
    apply H.
    contradict n.
    apply In_fst_KIn; auto.
  Qed.

  Lemma log_valid_replay : forall ents d ms,
    map_valid ms d ->
    log_valid ents (replay_disk (Map.elements ms) d) ->
    log_valid ents d.
  Proof.
    unfold log_valid, map_valid; intros.
    split; intros.
    apply H0.
    rewrite replay_disk_length in H0.
    eapply H0; eauto.
  Qed.

  Lemma replay_disk_replay_mem : forall l m d,
    log_valid l (replay_disk (Map.elements m) d) ->
    replay_disk l (replay_disk (Map.elements m) d) =
    replay_disk (Map.elements (replay_mem l m)) d.
  Proof.
    unfold log_valid; induction l; intros; intuition; auto.
    destruct a; inversion H0; subst; simpl.
    rewrite replay_disk_updN_comm.
    rewrite IHl.
    setoid_rewrite mapeq_elements at 2.
    2: apply replay_mem_add; auto.
    rewrite replay_disk_add; auto.
    split; auto; intros.
    eapply H1.
    apply InA_cons_tl; eauto.
    contradict H3.
    apply In_fst_KIn; auto.
  Qed.

  Lemma log_valid_entries_valid : forall ents d l raw,
    goodSize addrlen (length raw) ->
    d = replay_disk l raw ->
    log_valid ents d -> DLog.entries_valid ents.
  Proof.
    unfold log_valid, DLog.entries_valid; intuition.
    rewrite Forall_forall.
    intros; destruct x.
    unfold PaddedLog.entry_valid, PaddedLog.addr_valid; intuition.
    eapply H3; eauto; simpl.
    apply In_fst_KIn.
    eapply in_map; eauto.

    simpl; subst.
    rewrite replay_disk_length in *.
    eapply goodSize_trans; [ | apply H].
    apply Nat.lt_le_incl.
    eapply H3.
    apply In_fst_KIn.
    eapply in_map; eauto.
  Qed.

  Lemma log_valid_nodup : forall l d,
    log_valid l d -> KNoDup l.
  Proof.
    unfold log_valid; intuition.
  Qed.
  Local Hint Resolve log_valid_nodup.

  Local Hint Resolve KNoDup_NoDup Map.elements_3w.

  Section UnfoldProof2.
  Local Hint Unfold rep map_replay rep_inner map_empty: hoare_unfold.
  Hint Extern 0 (okToUnify (synced_data ?a _) (synced_data ?a _)) => constructor : okToUnify.

  Theorem flush_noapply_ok: forall xp ents ms,
    {< F d na na',
     PRE  rep xp F na (Synced d) ms *
          [[ log_valid ents d ]] *
          [[ na' = (na - (DLog.rounded (length ents))) ]]
     POST RET:^(ms',r)
          ([[ r = true ]]  *  rep xp F na' (Synced (replay_disk ents d)) ms') \/
          ([[ r = false /\ length ents > na ]]
                           *  rep xp F na  (Synced d) ms')
     CRASH  exists ms',
            rep xp F na (Synced d) ms' \/
            rep xp F na' (Synced (replay_disk ents d)) ms' \/
            rep xp F na (Flushing d ents) ms'
    >} flush_noapply xp ents ms.
  Proof.
    unfold flush_noapply.
    step using dems.
    eapply log_valid_entries_valid; eauto.
    hoare using dems.

    or_l.
    cancel; unfold map_merge.
    rewrite replay_mem_app; eauto.
    apply map_valid_replay_mem'; auto.
    eapply log_valid_replay; eauto.
    apply replay_disk_replay_mem; auto.

    (* crashes *)
    or_l; norm.
    Show Existentials.
    instantiate (ms' := mk_memstate (MSInLog ms) cs').
    cancel. intuition; simpl; eauto.
    pred_apply; cancel.

    or_r; or_r.
    norm. cancel.
    instantiate (ms'0 := mk_memstate (MSInLog ms) cs').
    cancel. intuition; simpl; eauto.
    pred_apply; cancel; eauto.
    or_l; auto.

    or_r; or_r.
    norm. cancel.
    instantiate (ms'1 := mk_memstate (MSInLog ms) cs').
    cancel. intuition; simpl; eauto.
    pred_apply; cancel; eauto.
    or_r; auto.

    or_r; or_l; norm.
    instantiate (ms'2 := mk_memstate (replay_mem ents (MSInLog ms)) cs').
    cancel. simpl; intuition; eauto.
    pred_apply; cancel.
    rewrite replay_mem_app; eauto.
    apply map_valid_replay_mem'.
    eapply log_valid_replay; eauto. auto.
    apply replay_disk_replay_mem; auto.
  Qed.

  End UnfoldProof2.


  Lemma map_valid_Forall_fst_synced : forall d ms,
    map_valid ms d ->
    Forall (fun e => fst e < length (synced_list d)) (Map.elements ms).
  Proof.
    unfold map_valid, synced_list; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    destruct x; simpl.
    apply (H n w).
    apply Map.elements_2.
    apply In_InA; auto.
  Qed.
  Local Hint Resolve map_valid_Forall_fst_synced.

  Lemma map_valid_Forall_synced_map_fst : forall d ms,
    map_valid ms d ->
    Forall (fun e => e < length (synced_list d)) (map fst (Map.elements ms)).
  Proof.
    unfold map_valid, synced_list; intros.
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

  Lemma map_merge_id: forall m,
    Map.Equal (map_merge m m) m.
  Proof.
    unfold map_merge, replay_mem; intros.
    rewrite <- Map.fold_1.
    apply MapProperties.fold_rec_nodep; auto.
    intros.
    rewrite H0.
    apply MapFacts.Equal_mapsto_iff; intros.

    destruct (eq_nat_dec k0 k); subst; split; intros.
    apply MapFacts.add_mapsto_iff in H1; intuition; subst; auto.
    apply MapFacts.add_mapsto_iff; left; intuition.
    eapply MapFacts.MapsTo_fun; eauto.
    eapply Map.add_3; eauto.
    eapply Map.add_2; eauto.
  Qed.

  Lemma map_snd_synced_list_eq : forall a b,
    length a = length b ->
    map snd (synced_list a) = map snd (synced_list b).
  Proof.
    unfold synced_list; intros.
    repeat rewrite map_snd_combine; autorewrite with lists; auto.
  Qed.

  Lemma map_snd_vsupd_vecs_not_in : forall l d a v,
    ~ In a (map fst l) ->
    NoDup (map fst l) ->
    map snd (vsupd_vecs (synced_list (updN d a v)) l) = map snd (vsupd_vecs (synced_list d) l).
  Proof.
    induction l; simpl; intros.
    erewrite map_snd_synced_list_eq; eauto.
    autorewrite with lists; auto.

    destruct a; intuition; simpl in *.
    inversion H0; subst.
    setoid_rewrite vsupd_vecs_vsupd_notin; auto.
    unfold vsupd.
    repeat rewrite map_snd_updN.
    f_equal.
    apply IHl; auto.
    f_equal; f_equal; f_equal.
    rewrite <- synced_list_updN.
    rewrite <- updN_vsupd_vecs_notin by auto.
    rewrite selN_updN_ne; auto.
  Qed.

  Lemma apply_unsync_syncing_ok': forall l d n,
    NoDup (map fst l) ->
    vssync_vecs (vsupd_vecs (synced_list d) l) (firstn n (map fst l))
      = List.combine (replay_disk l d) (map snd (vsupd_vecs (synced_list d) (skipn n l))).
  Proof.
    induction l; intros; simpl.
    rewrite firstn_nil, skipn_nil; simpl.
    unfold synced_list.
    rewrite map_snd_combine; autorewrite with lists; auto.

    destruct a; simpl.
    inversion H; subst.
    destruct n; simpl.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite map_snd_updN.
    rewrite replay_disk_updN_comm by auto.
    rewrite combine_updN.
    f_equal.
    replace l with (skipn 0 l) at 3 by auto.
    rewrite <- IHl; auto; omega.

    erewrite <- map_snd_vsupd_vecs_not_in.
    rewrite <- IHl; auto.
    rewrite vsupd_vecs_vsupd_notin by auto.
    rewrite vssync_vsupd_eq.
    rewrite updN_vsupd_vecs_notin by auto.
    rewrite synced_list_updN; auto.
    contradict H2.
    eapply in_skipn_in.
    rewrite skipn_map_comm; eauto.
    rewrite <- skipn_map_comm.
    apply NoDup_skipn; auto.
  Qed.

  Lemma nil_unless_in_synced_list : forall l d,
    NoDup (map fst l) ->
    nil_unless_in (map fst l) (map snd (vsupd_vecs (synced_list d) l)).
  Proof.
    unfold nil_unless_in; induction l; simpl; intros; auto.
    unfold synced_list.
    rewrite map_snd_combine; autorewrite with lists; auto.
    destruct (lt_dec a (length d)).
    rewrite repeat_selN; auto.
    rewrite selN_oob; auto.
    autorewrite with lists; omega.

    destruct a; intuition; simpl in *.
    inversion H; subst.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite map_snd_updN.
    rewrite selN_updN_ne by auto.
    rewrite IHl; auto.
  Qed.

  Lemma nil_unless_in_synced_list_skipN : forall n l d,
    NoDup (map fst l) ->
    nil_unless_in (map fst l) (map snd (vsupd_vecs (synced_list d) (skipn n l))).
  Proof.
    induction n; intros; auto.
    apply nil_unless_in_synced_list; auto.
    destruct l; simpl; auto.
    unfold synced_list, nil_unless_in; intros.
    rewrite map_snd_combine; autorewrite with lists; auto.
    destruct (lt_dec a (length d)).
    rewrite repeat_selN; auto.
    rewrite selN_oob; auto.
    autorewrite with lists; omega.

    unfold nil_unless_in; intros.
    inversion H; subst.
    apply IHn; auto.
    contradict H0.
    apply in_cons; auto.
  Qed.

  Lemma apply_unsync_syncing_ok : forall xp m d n,
    arrayN (DataStart xp) (vssync_vecs (vsupd_vecs (synced_list d) (Map.elements m)) (firstn n (map_keys m)))
       =p=> unsync_syncing xp m (replay_disk (Map.elements m) d).
  Proof.
    unfold unsync_syncing; cancel.
    apply arrayN_unify.
    apply apply_unsync_syncing_ok'.
    apply KNoDup_NoDup.
    apply Map.elements_3w.

    apply nil_unless_in_synced_list_skipN.
    apply KNoDup_NoDup.
    apply Map.elements_3w.

    autorewrite with lists.
    rewrite vsupd_vecs_length.
    unfold synced_list.
    rewrite combine_length_eq; autorewrite with lists; auto.
  Qed.

  Lemma vsupd_length : forall vsl a v,
    length (vsupd vsl a v) = length vsl.
  Proof.
    unfold vsupd; intros.
    rewrite length_updN; auto.
  Qed.


  Lemma apply_unsync_applying_ok' : forall l d n,
    NoDup (map fst l) ->
    equal_unless_in (map fst l) d (vsupd_vecs d (firstn n l)).
  Proof.
    unfold equal_unless_in; induction l; intros; simpl.
    rewrite firstn_nil; simpl; intuition.
    split; intuition;
    destruct n; simpl; auto;
    destruct a; inversion H; simpl in *; intuition; subst.

    rewrite vsupd_vecs_vsupd_notin.
    rewrite vsupd_length, vsupd_vecs_length; auto.
    rewrite <- firstn_map_comm.
    contradict H2.
    eapply in_firstn_in; eauto.

    pose proof (IHl d n H5) as [Hx Hy].
    rewrite Hy by auto.
    rewrite vsupd_vecs_vsupd_notin.
    unfold vsupd; rewrite selN_updN_ne; auto.
    rewrite <- firstn_map_comm.
    contradict H4.
    eapply in_firstn_in; eauto.
  Qed.

  Lemma apply_unsync_applying_ok : forall xp m d n,
    arrayN (DataStart xp) (vsupd_vecs (synced_list d) (firstn n (Map.elements m)))
       =p=> unsync_applying xp m d.
  Proof.
    unfold unsync_applying, map_replay; cancel.
    apply apply_unsync_applying_ok'.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.

  Lemma map_valid_replay_disk : forall l m d,
    map_valid m d ->
    map_valid m (replay_disk l d).
  Proof.
    unfold map_valid; induction d; intros.
    rewrite replay_disk_length; eauto.
    split.
    apply (H a0 v); auto.
    rewrite replay_disk_length.
    apply (H a0 v); auto.
  Qed.


  Section UnfoldProof3.
  Local Hint Unfold rep map_replay rep_inner map_empty: hoare_unfold.
  Hint Extern 0 (okToUnify (synced_data ?a _) (synced_data ?a _)) => constructor : okToUnify.

  Theorem apply_ok: forall xp ms,
    {< F d na,
    PRE
      rep xp F na (Synced d) ms
    POST RET:ms'
      rep xp F (LogLen xp) (Synced d) ms'
    CRASH
      exists ms', rep xp F (LogLen xp) (Synced d) ms' \/
                  rep xp F na (Synced d) ms' \/
                  rep xp F na (Applying d) ms'
    >} apply xp ms.
  Proof.
    unfold apply; intros.
    step.
    unfold synced_data; cancel.
    step.
    rewrite vsupd_vecs_length.
    apply map_valid_Forall_synced_map_fst; auto.
    step.
    step.
    rewrite apply_synced_data_ok; cancel.
    rewrite replay_disk_length; auto.
    apply map_valid_map0.

    (* crash conditions *)
    or_r; or_l. norm.
    instantiate (2 := mk_memstate (MSInLog ms) cs).
    cancel.
    intuition; simpl; eauto.
    pred_apply; norm.
    instantiate (d2 := replay_disk (Map.elements (MSInLog ms)) d0).
    cancel.

    rewrite apply_synced_data_ok; cancel.
    intuition.
    rewrite replay_disk_length; auto.
    apply map_valid_replay; auto.

    rewrite replay_disk_merge.
    setoid_rewrite mapeq_elements at 2; eauto.
    apply map_merge_id.

    (* truncated *)
    or_r; or_r. norm.
    instantiate (2 := mk_memstate (MSInLog ms) cs).
    cancel.
    intuition; simpl; eauto.
    pred_apply; cancel; eauto.
    or_r; or_r; cancel.
    rewrite apply_synced_data_ok; cancel.

    (* synced nil *)
    or_l. norm.
    instantiate (2 := mk_memstate map0 cs).
    cancel. intuition.
    pred_apply; norm.
    instantiate (log0 := nil).
    instantiate (d2 := replay_disk (Map.elements (MSInLog ms)) d0).
    cancel.
    rewrite apply_synced_data_ok; cancel.
    intuition.
    rewrite replay_disk_length; eauto.
    apply map_valid_map0.

    (* unsync_syncing *)
    or_r; or_r. norm.
    instantiate (2 := mk_memstate (MSInLog ms) cs').
    cancel.
    intuition; simpl; eauto.
    pred_apply; cancel; eauto.
    or_r; or_l; cancel.
    apply apply_unsync_syncing_ok.

    (* unsync_applying *)
    or_r; or_r. norm.
    instantiate (2 := mk_memstate (MSInLog ms) cs').
    cancel.
    intuition; simpl; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
    apply apply_unsync_applying_ok.
  Qed.

  End UnfoldProof3.


  Hint Extern 1 ({{_}} progseq (apply _ _) _) => apply apply_ok : prog.
  Hint Extern 1 ({{_}} progseq (flush_noapply _ _ _) _) => apply flush_noapply_ok : prog.
  Hint Extern 0 (okToUnify (synced_data ?a _) (synced_data ?a _)) => constructor : okToUnify.

  Theorem flush_ok: forall xp ents ms,
    {< F d na n1 n2,
     PRE  rep xp F na (Synced d) ms *
          [[ log_valid ents d ]] *
          [[ n1 = (na - (DLog.rounded (length ents))) ]] *
          [[ n2 = ((LogLen xp) - (DLog.rounded (length ents))) ]]
     POST RET:^(ms',r)
          ([[ r = true ]] * 
             (rep xp F n1 (Synced (replay_disk ents d)) ms') \/
             (rep xp F n2 (Synced (replay_disk ents d)) ms'))
          \/
          ([[ r = false /\ length ents > na ]] *
             (rep xp F na          (Synced d) ms') \/
             (rep xp F (LogLen xp) (Synced d) ms'))
     CRASH  exists ms',
            rep xp F (LogLen xp) (Synced d) ms' \/
            rep xp F na  (Synced d) ms' \/
            rep xp F n1  (Synced (replay_disk ents d)) ms' \/
            rep xp F n2  (Synced (replay_disk ents d)) ms' \/
            rep xp F na  (Flushing d ents) ms' \/
            rep xp F na  (Applying d) ms'
    >} flush xp ents ms.
  Proof.
    unfold flush; intros.

    (* Be careful: only unfold rep in the preconditon,
       otherwise the goal will get messy as there are too many
       disjuctions in post/crash conditons *)
    prestep.
    unfold rep at 1, rep_inner at 1.
    cancel.
    step.

    (* case 1: apply happens *)
    prestep.
    unfold rep at 1, rep_inner at 1.
    cancel; auto.
    instantiate (2 := F); cancel.
    step.
    step.

    (* crashes *)
    cancel; or_l; cancel.
    cancel; or_r; or_r; or_r; or_l; cancel.
    cancel; or_r; or_r; or_r; or_r; or_l; cancel.
    cancel.
    or_l; cancel.
    or_r; or_l; cancel.
    or_r; or_r; or_r; or_r; cancel.

    (* case 2: no apply *)
    prestep.
    unfold rep at 1, rep_inner at 1.
    cancel; auto.
    instantiate (1 := d); cancel. auto.
    step.

    (* crashes *)
    cancel.
    or_r; or_l; cancel.
    or_r; or_r; or_l; cancel.
    or_r; or_r; or_r; or_r; or_l; cancel.

    pimpl_crash; cancel.
    or_r; or_l.
    instantiate (ms' := mk_memstate (MSInLog ms) cs').
    unfold rep, rep_inner; cancel; auto.
  Qed.


  Definition recover_either_pred xp d ents :=
    (exists na ms,
      rep_inner xp na (Synced d) ms \/
      rep_inner xp na (Synced (replay_disk ents d)) ms \/
      rep_inner xp na (Flushing d ents) ms \/
      rep_inner xp na (Applying d) ms)%pred.

  Definition after_crash_pred xp d ents :=
    (exists na ms,
      rep_inner xp na (Synced d) ms \/
      rep_inner xp na (Synced (replay_disk ents d)) ms)%pred.


  Lemma crash_xform_synced_data : forall xp d,
    crash_xform (synced_data xp d) =p=> synced_data xp d.
  Proof.
    unfold synced_data, synced_list; intros.
    apply crash_xform_arrayN_combine_nils.
  Qed.

  Lemma map_valid_equal : forall d m1 m2,
    Map.Equal m1 m2 -> map_valid m1 d -> map_valid m2 d.
  Proof.
    induction d; unfold map_valid; simpl; intros; split;
    eapply H0; rewrite H; eauto.
  Qed.

  Lemma synced_after_crash_ok : forall xp na d m ents,
    crash_xform (rep_inner xp na (Synced d) m) =p=>
    after_crash_pred xp d ents.
  Proof.
    unfold after_crash_pred, rep_inner, map_replay; intros.
    xform.
    rewrite crash_xform_synced_data.
    rewrite DLog.xform_rep_synced.
    cancel; or_l.
    cancel.
    eapply map_valid_equal; eauto.
    erewrite mapeq_elements; eauto.
  Qed.

  Lemma synced_replay_after_crash_ok : forall xp na d m ents,
    crash_xform (rep_inner xp na (Synced (replay_disk ents d)) m) =p=>
    after_crash_pred xp d ents.
  Proof.
    unfold after_crash_pred, rep_inner, map_replay; intros.
    xform.
    rewrite crash_xform_synced_data.
    rewrite DLog.xform_rep_synced.
    cancel; or_r.
    cancel.
    eapply map_valid_equal; eauto.
    erewrite mapeq_elements; eauto.
    rewrite H; auto.
  Qed.

  Lemma flushing_after_crash_ok : forall xp na d m ents,
    crash_xform (rep_inner xp na (Flushing d ents) m) =p=>
    after_crash_pred xp d ents.
  Proof.
    unfold after_crash_pred, rep_inner, map_replay; intros.
    xform.
    rewrite crash_xform_synced_data.
    rewrite DLog.xform_rep_extended.
    rewrite DLog.xform_rep_extended_unsync.
    cancel.

    or_l; cancel.
    eapply map_valid_equal; eauto.
    erewrite mapeq_elements; eauto.

    or_l; cancel.
    eapply map_valid_equal; eauto.
    erewrite mapeq_elements; eauto.

    or_r; cancel.
    eapply map_valid_equal.
    apply MapFacts.Equal_sym.
    apply replay_mem_app; auto.
    apply map_valid_replay_mem'.
    eapply log_valid_replay; eauto.
    eapply map_valid_equal; eauto.

    setoid_rewrite mapeq_elements at 2.
    2: apply replay_mem_app; eauto.
    apply replay_disk_replay_mem; auto.
  Qed.

  Lemma replay_disk_updN_absorb : forall l a v d,
    In a (map fst l) -> KNoDup l ->
    replay_disk l (updN d a v) = replay_disk l d.
  Proof.
    induction l; intros; simpl; auto.
    inversion H.
    destruct a; simpl in *; intuition; subst.
    rewrite updN_twice; auto.
    inversion H0; subst.
    setoid_rewrite <- IHl at 2; eauto.
    rewrite updN_comm; auto.
    contradict H3; subst.
    apply In_fst_KIn; auto.
  Qed.

  Lemma replay_disk_twice : forall l d,
    KNoDup l ->
    replay_disk l (replay_disk l d) = replay_disk l d.
  Proof.
    induction l; simpl; intros; auto.
    destruct a; inversion H; subst; simpl.
    rewrite <- replay_disk_updN_comm.
    rewrite IHl; auto.
    rewrite updN_twice; auto.
    contradict H2.
    apply In_fst_KIn; auto.
  Qed.

  Lemma equal_unless_in_length_eq : forall a b l,
    equal_unless_in l a b -> length b = length a.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.

  Lemma possible_crash_list_length_eq : forall a b,
    possible_crash_list a b -> length b = length a.
  Proof.
    unfold possible_crash_list; firstorder.
  Qed.

  Lemma length_synced_list : forall l,
    length (synced_list l) = length l.
  Proof.
    unfold synced_list; simpl; intros.
    rewrite combine_length_eq; auto.
    rewrite repeat_length; auto.
  Qed.

  Lemma length_eq_map_valid : forall m a b,
    map_valid m a -> length b = length a -> map_valid m b.
  Proof.
    unfold map_valid; firstorder.
  Qed.

  Hint Rewrite length_synced_list selN_combine repeat_selN' Nat.min_id : lists.

  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints lists)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with lists .. ]).

  Ltac simplen' := repeat match goal with
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : context[Nat.min ?a ?a] |- _ ] => rewrite Nat.min_id in H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : equal_unless_in _ _ _ |- _ ] => apply equal_unless_in_length_eq in H
    | [H : possible_crash_list _ _ |- _ ] => apply possible_crash_list_length_eq in H
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac simplen :=  auto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with lists); simpl; eauto; try omega.


  Ltac map_rewrites :=
    match goal with
    | [ H : Map.Equal (replay_mem ?x ?y) _ |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal (MapFacts.Equal_sym H))
    | [ H : Map.Equal _ (replay_mem ?x ?y) |- map_valid (replay_mem ?x ?y) ?l ] =>
        eapply (map_valid_equal H)
    | [ H : Map.Equal _  (replay_mem ?x ?y)
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements (MapFacts.Equal_sym H))
    | [ H : Map.Equal (replay_mem ?x ?y) _
        |-  context [ replay_disk (Map.elements (replay_mem ?x ?y)) _ ] ] =>
        rewrite (mapeq_elements H)
    end.

  Ltac t :=
    repeat map_rewrites;
    try match goal with
      | [ H : goodSize _ ?a |- goodSize _ ?b ] => simplen
      | [ H : map_valid ?a _ |- map_valid ?a _ ] =>
          solve [ eapply (length_eq_map_valid _ H); simplen ]
    end.

  Lemma equal_unless_in_possible_crash : forall l a b c,
    equal_unless_in l (synced_list a) b ->
    possible_crash_list b c ->
    forall i, ~ In i l -> selN a i $0 = selN c i $0.
  Proof.
    unfold equal_unless_in, possible_crash_list, synced_list.
    intros; simpl in *; autorewrite with lists in *; intuition.
    destruct (lt_dec i (length b)).

    destruct (H4 i l0).
    rewrite <- H0.
    rewrite <- H3 by auto.
    rewrite selN_combine; simplen.

    contradict H0.
    rewrite <- H3 by auto.
    rewrite selN_combine by simplen; simpl.
    rewrite repeat_selN; simplen.
    repeat rewrite selN_oob; simplen.
  Qed.

  Lemma equal_unless_in_synced_list_updN : forall B l a (b : B) v d d',
    ~ KIn (a, b) l ->
    equal_unless_in (a :: map fst l) (synced_list d) d' ->
    equal_unless_in (map fst l) (synced_list (updN d a v)) (updN d' a (v, nil)).
  Proof.
    unfold equal_unless_in, synced_list; intuition; simpl in *.
    simplen.
    simplen.
    destruct (lt_dec a0 (length d)).
    destruct (Nat.eq_dec a a0); simplen.
    repeat rewrite selN_updN_ne by auto.
    rewrite <- H2; simplen; tauto.
    repeat rewrite selN_oob; simplen.
  Qed.

  Lemma possible_crash_list_updN : forall l l' a v vs,
    possible_crash_list l l' ->
    possible_crash_list (updN l a (v, vs)) (updN l' a v).
  Proof.
    unfold possible_crash_list; simpl; intuition.
    simplen.
    destruct (Nat.eq_dec a i); subst; simplen.
    repeat rewrite selN_updN_ne; eauto.
  Qed.

  Lemma equal_unless_in_replay_disk' : forall l a b c,
    KNoDup l ->
    equal_unless_in (map fst l) (synced_list a) b ->
    possible_crash_list b c ->
    replay_disk l a = replay_disk l c.
  Proof.
    induction l; intuition; simpl.
    eapply list_selN_ext.
    simplen.
    intros; eapply equal_unless_in_possible_crash; eauto.

    inversion H; simpl in *; subst.
    eapply IHl; auto.
    eapply equal_unless_in_synced_list_updN; eauto.
    apply possible_crash_list_updN; auto.
  Qed.

  Lemma equal_unless_in_replay_disk : forall a b c m,
    equal_unless_in (map_keys m) (synced_list a) b ->
    possible_crash_list b c ->
    replay_disk (Map.elements m) a = replay_disk (Map.elements m) c.
  Proof.
    intros.
    eapply equal_unless_in_replay_disk'; eauto.
    apply Map.elements_3w.
  Qed.

  Lemma nil_unless_in_nils : forall vsl nr,
    nil_unless_in nil vsl ->
    length vsl = nr ->
    vsl = repeat nil nr.
  Proof.
    unfold nil_unless_in.
    induction vsl; destruct nr; intuition; simpl.
    inversion H0.
    inversion H0.
    rewrite <- (H 0) at 1; simpl; auto.
    f_equal.
    inversion H0.
    apply IHvsl; intros; auto.
    rewrite <- (H (S a0)) at 2; simpl; eauto.
  Qed.


  Lemma possible_crash_list_combine_nils : forall d d',
    possible_crash_list (List.combine d (repeat nil (length d))) d' -> d = d'.
  Proof.
    unfold possible_crash_list.
    induction d; destruct d'; intuition.
    inversion H0.
    inversion H0.
    f_equal.
    generalize (H1 0); rewrite H0; simpl; intuition.
    destruct H; firstorder.

    apply IHd; intuition.
    generalize (H1 (S i)); rewrite H0; simpl; intros.
    apply H2; simplen.
    inversion H0; omega.
  Qed.

  Lemma nil_unless_in_empty : forall d d' vsl,
    possible_crash_list (List.combine d vsl) d' ->
    length vsl = length d ->
    nil_unless_in nil vsl ->
    d = d'.
  Proof.
    intros.
    apply possible_crash_list_combine_nils.
    erewrite <- nil_unless_in_nils; eauto.
  Qed.

  Lemma nil_unless_in_updN : forall V l a0 (v0 : V) vsl,
    ~ KIn (a0, v0) l ->
    nil_unless_in (a0 :: (map fst l)) vsl ->
    nil_unless_in (map fst l) (updN vsl a0 nil).
  Proof.
    unfold nil_unless_in; simpl; intuition.
    destruct (lt_dec a0 (length vsl)).
    destruct (addr_eq_dec a a0); subst; simpl.
    rewrite selN_updN_eq; auto.
    rewrite selN_updN_ne; auto.
    apply H0; intuition.

    destruct (addr_eq_dec a a0); subst; simpl.
    rewrite selN_oob; auto; simplen.
    rewrite selN_updN_ne; auto.
    apply H0; intuition.
  Qed.

  Lemma possible_crash_list_combine_updN : forall vsl d d' a v,
    selN d a $0 = v -> length vsl = length d ->
    possible_crash_list (List.combine d vsl) d' ->
    possible_crash_list (List.combine d (updN vsl a nil)) (updN d' a v).
  Proof.
    unfold possible_crash_list, vsmerge; intros; intuition; simplen.
    generalize (H3 i H1).
    repeat rewrite selN_combine by simplen; simpl; intros.
    destruct (addr_eq_dec a i); try subst a.
    setoid_rewrite selN_updN_eq; firstorder.
    setoid_rewrite selN_updN_ne; auto.
  Qed.

  Lemma In_InA : forall a v l,
    In a (map fst l) -> InA (@Map.eq_key valu) (a, v) l.
  Proof.
    intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply InA_alt.
    exists (a, x).
    split; auto.
    hnf; auto.
  Qed.
  Local Hint Resolve In_InA.

  Lemma nil_unless_in_replay_disk' : forall l d d' vsl,
    nil_unless_in (map fst l) vsl ->
    possible_crash_list (List.combine (replay_disk l d) vsl) d' ->
    KNoDup l -> length vsl = length d ->
    (forall x, InA (@Map.eq_key_elt valu) x l -> fst x < length d) ->
    replay_disk l d = replay_disk l d'.
  Proof.
    induction l; intuition; simpl in *.
    eapply nil_unless_in_empty; eauto.
    inversion H1; subst.

    eapply IHl; intros; eauto.
    eapply nil_unless_in_updN; eauto.
    apply possible_crash_list_combine_updN; auto.

    erewrite replay_disk_selN_other; auto.
    apply selN_updN_eq; auto.
    apply (H3 (a0, b)).
    apply InA_cons_hd; hnf; auto.
    simplen.
    simplen.
    simplen.
  Qed.

  Lemma nil_unless_in_replay_disk : forall m d d' vsl,
    map_valid m d ->
    nil_unless_in (map_keys m) vsl ->
    length vsl = length (replay_disk (Map.elements m) d) ->
    possible_crash_list (List.combine (replay_disk (Map.elements m) d) vsl) d' ->
    replay_disk (Map.elements m) d = replay_disk (Map.elements m) d'.
  Proof.
    unfold map_valid; intros.
    eapply nil_unless_in_replay_disk'; intros; eauto.
    apply Map.elements_3w.
    simplen.
    destruct x.
    eapply H.
    apply Map.elements_2.
    simpl; eauto.
  Qed.

  Lemma applying_after_crash_ok : forall xp na d m ents,
    crash_xform (rep_inner xp na (Applying d) m) =p=>
    after_crash_pred xp d ents.
  Proof.
    unfold rep_inner, map_replay; intros.
    xform.
    rewrite crash_xform_synced_data.
    rewrite DLog.xform_rep_synced.
    rewrite DLog.xform_rep_truncated.

    unfold unsync_applying, unsync_syncing.
    xform.
    cancel; xform; try rewrite crash_xform_arrayN;
    unfold after_crash_pred, rep_inner; cancel; or_l;
    unfold synced_data, map_replay; cancel; t.

    eapply equal_unless_in_replay_disk; eauto.
    eapply nil_unless_in_replay_disk; eauto.
    rewrite replay_disk_twice; auto.
    apply Map.elements_3w.
    apply map_valid_map0.
  Qed.

  Local Hint Resolve synced_after_crash_ok synced_replay_after_crash_ok
                     flushing_after_crash_ok applying_after_crash_ok.

  Lemma recover_either_after_crash : forall xp d ents,
    crash_xform (recover_either_pred xp d ents) =p=>
    after_crash_pred xp d ents.
  Proof.
    unfold recover_either_pred; intros.
    xform.
    cancel; auto.
  Qed.



  Remove Hints MapFacts.Equal_refl.

  Lemma recover_either_after_crash_unfold' : forall xp F d ents,
    crash_xform (F * recover_either_pred xp d ents)
      =p=>
    crash_xform F * exists na ms log old,
       synced_data xp old * DLog.rep xp (DLog.Synced na log) *
       [[ Map.Equal ms (replay_mem log map0) ]] *
       [[ goodSize addrlen (length old) ∧ map_valid ms old ]] *
     ( [[ d = replay_disk (Map.elements ms) old ]] \/
       [[ replay_disk ents d = replay_disk (Map.elements ms) old ]] ).
  Proof.
    intros; xform.
    rewrite recover_either_after_crash.
    unfold after_crash_pred, rep, rep_inner, map_replay.
    cancel_with eauto.
    or_l; cancel.
    or_r; cancel.
  Qed.


  Definition recover T xp cs rx : prog T :=
    let^ (cs, log) <- DLog.read xp cs;
    rx (mk_memstate (replay_mem log map0) cs).

  Theorem recover_ok: forall xp F cs,
    {< d ents raw,
    PRE
      BUFCACHE.rep cs raw *
      [[ crash_xform (F * recover_either_pred xp d ents)%pred raw ]]
    POST RET:ms' exists na,
      rep xp (crash_xform F) na (Synced d) ms' \/
      rep xp (crash_xform F) na (Synced (replay_disk ents d)) ms'
    CRASH exists raw' cs',
      BUFCACHE.rep cs' raw' *
      [[ ((crash_xform F) * recover_either_pred xp d ents)%pred raw' ]]
    >} recover xp cs.
  Proof.
    unfold recover; intros.
    prestep; xform.
    norml.

    (* manually get two after-crash cases *)
    apply recover_either_after_crash_unfold' in H4.
    destruct_lifts.
    apply sep_star_or_distr in H0; apply pimpl_or_apply in H0.
    destruct H0; destruct_lift H0.

    (* case 1 : last transaction unapplied *)
    - cancel.
      step.
      unfold rep; cancel.
      or_l; cancel.
      unfold rep_inner, map_replay, synced_data.
      cancel; try map_rewrites; auto.

      subst; pimpl_crash.
      unfold rep, recover_either_pred.
      cancel.
      or_l.
      unfold rep_inner, map_replay.
      cancel; auto.

    (* case 2 : last transaction applied *)
    - cancel.
      step.
      unfold rep; cancel.
      or_r; cancel.
      unfold rep_inner, map_replay, synced_data.
      cancel; try map_rewrites; auto.

      subst; pimpl_crash.
      unfold rep, recover_either_pred.
      cancel.
      or_r; or_l.
      unfold rep_inner, map_replay.
      cancel; eauto.
  Qed.


End MLOG.
