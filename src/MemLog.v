Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Classes.SetoidTactics.
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
Require Import DiskLog.
Require Import AsyncDisk.
Require Import SepAuto.
Require Import GenSepN.
Require Import MapUtils.
Require Import FMapFacts.


Import ListNotations.
Set Implicit Arguments.

Definition valumap := Map.t valu.
Definition vmap0 := map0 valu.
Definition diskstate := list valuset.

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
    fold_left (fun m' e => updN m' (fst e) (snd e, nil)) log m.

  Definition map_replay ms old cur :=
    cur = replay_disk (Map.elements ms) old.

  Definition map_merge (m1 m2 : valumap) :=
    replay_mem (Map.elements m2) m1.

  Definition equal_unless_in (keys: list addr) (l1 l2: list valuset) :=
    length l1 = length l2 /\
    forall a,  ~ In a keys -> selN l1 a ($0, nil) = selN l2 a ($0, nil).

  Definition synced_rep xp (d : diskstate) : rawpred :=
    arrayN (DataStart xp) d.

  Definition unsync_rep xp (ms : valumap) (old : diskstate) : rawpred :=
    (exists vs, [[ equal_unless_in (map_keys ms) old vs ]] *
     arrayN (DataStart xp) vs
    )%pred.

  Definition map_valid (ms : valumap) (m : diskstate) :=
     forall a v, Map.MapsTo a v ms -> a <> 0 /\ a < length m.

  Definition log_valid (ents : DLog.contents) (m : diskstate) :=
     KNoDup ents /\ forall a v, KIn (a, v) ents -> a <> 0 /\ a < length m.

  Definition rep_inner xp na st ms :=
    ( exists log d0,
      [[ Map.Equal ms (replay_mem log vmap0) ]] *
      [[ goodSize addrlen (length d0) /\ map_valid ms d0 ]] *
    match st with
    | Synced d =>
        [[ map_replay ms d0 d ]] *
        synced_rep xp d0 *
        DLog.rep xp (DLog.Synced na log)
    | Flushing d ents =>
        [[ log_valid ents d /\ map_replay ms d0 d ]] *
        synced_rep xp d0 *
        (DLog.rep xp (DLog.ExtendedUnsync log)
      \/ DLog.rep xp (DLog.Extended log ents))
    | Applying d =>
        [[ map_replay ms d0 d ]] *
        (((DLog.rep xp (DLog.Synced na log)) *
          (unsync_rep xp ms d0))
      \/ ((DLog.rep xp (DLog.Truncated log)) *
          (synced_rep xp d)))
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
    rx (mk_memstate vmap0 cs).

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
    map_valid vmap0 m.
  Proof.
    unfold map_valid, map0; intuition; exfalso;
    apply MapFacts.empty_mapsto_iff in H; auto.
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

  Lemma replay_disk_selN_other : forall l d a def,
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

  Lemma replay_disk_selN_In : forall l m a v def,
    In (a, v) l -> NoDup (map fst l) -> a < length m ->
    selN (replay_disk l m) a def = (v, nil).
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
    selN (replay_disk l m) a def = (v, nil).
  Proof.
    intros.
    eapply replay_disk_selN_In; eauto.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma replay_disk_selN_MapsTo : forall a v ms m def,
    Map.MapsTo a v ms -> a < length m ->
    selN (replay_disk (Map.elements ms) m) a def = (v, nil).
  Proof.
    intros.
    apply replay_disk_selN_In_KNoDup; auto.
    apply InA_eqke_In.
    apply MapFacts.elements_mapsto_iff; auto.
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
    eexists. apply In_InA; eauto.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma replay_disk_add : forall a v ds m,
    replay_disk (Map.elements (Map.add a v ds)) m = updN (replay_disk (Map.elements ds) m) a (v, nil).
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
    apply Map.find_2 in H0.
    setoid_rewrite replay_disk_selN_MapsTo at 2; eauto.
    erewrite replay_disk_selN_MapsTo; eauto.
    apply Map.add_2; eauto.
    (* [pos] is not in the transaction *)
    repeat rewrite replay_disk_selN_not_In; auto.
    apply MapFacts.not_find_in_iff; auto.
    apply MapFacts.not_find_in_iff.
    rewrite MapFacts.add_neq_o by auto; auto.
    Unshelve.
    exact ($0, nil).
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

  Lemma replay_disk_eq : forall a v v' ms d vs,
    Map.find a ms = Some v ->
    (exists F, F * a |-> (v', vs))%pred (list2nmem (replay_disk (Map.elements ms) d)) ->
    v = v'.
  Proof.
    intros.
    destruct H0.
    eapply list2nmem_sel with (def := ($0, nil)) in H0 as Hx.
    erewrite replay_disk_selN_MapsTo in Hx.
    inversion Hx; auto.
    apply Map.find_2; auto.
    apply list2nmem_ptsto_bound in H0.
    repeat rewrite replay_disk_length in *; auto.
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
    -> a < length d.
  Proof.
    intros.
    destruct H.
    apply list2nmem_ptsto_bound in H.
    autorewrite with lists in *; auto.
  Qed.

  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

  Section UnfoldProof1.
  Local Hint Unfold rep map_replay rep_inner: hoare_unfold.

  Theorem read_ok: forall xp ms a,
    {< F d na vs,
    PRE
      rep xp F na (Synced d) ms *
      [[[ d ::: exists F', (F' * a |-> vs) ]]]
    POST RET:^(ms', r)
      rep xp F na (Synced d) ms' * [[ r = fst vs ]]
    CRASH
      exists ms', rep xp F na (Synced d) ms'
    >} read xp a ms.
  Proof.
    unfold read.
    prestep.

    cancel.
    step.
    subst.
    eapply replay_disk_eq; eauto.
    instantiate (d := d0); pred_apply; cancel.
    pimpl_crash; cancel; auto. cancel.

    unfold synced_rep; cancel.
    subst; eapply synced_data_replay_inb; eauto.
    instantiate (c1 := (Map.elements (MSInLog ms))); pred_apply; cancel.

    prestep.
    cancel; subst; auto.
    unfold pred_apply in *.
    assert (selN d0 a ($0, nil) = (vs_cur, vs_old)) as Hx.
    eapply replay_disk_none_selN; eauto.
    pred_apply; cancel.
    destruct (selN d0 a ($0, nil)); inversion Hx; auto.

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


  Lemma replay_mem_map0 : forall m,
    Map.Equal (replay_mem (Map.elements m) vmap0) m.
  Proof.
    intros; hnf; intro.
    unfold replay_mem.
    rewrite <- Map.fold_1.
    rewrite MapProperties.fold_identity; auto.
  Qed.

  Local Hint Resolve MapFacts.Equal_refl.

  Lemma replay_mem_app' : forall l m,
    Map.Equal (replay_mem ((Map.elements m) ++ l) vmap0) (replay_mem l m).
  Proof.
    induction l using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite replay_mem_map0; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    rewrite <- IHl; auto.
  Qed.

  Lemma replay_mem_app : forall l2 l m,
    Map.Equal m (replay_mem l vmap0) ->
    Map.Equal (replay_mem (l ++ l2) vmap0) (replay_mem l2 m).
  Proof.
    induction l2 using rev_ind; intros.
    rewrite app_nil_r; simpl.
    rewrite H; auto.
    rewrite app_assoc.
    setoid_rewrite fold_left_app; simpl.
    rewrite <- IHl2; auto.
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


  Lemma In_replay_mem_mem0 : forall l k,
    KNoDup l ->
    In k (map fst (Map.elements (replay_mem l vmap0))) ->
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
    replay_disk l d = replay_disk (Map.elements (elt:=valu) (replay_mem l vmap0)) d.
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
    replay_disk (Map.elements (replay_mem l2 (replay_mem l1 vmap0))) d.
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
    rewrite replay_disk_merge' by auto.
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
    apply map_merge_repeat'; auto.
  Qed.

  Local Hint Resolve Map.is_empty_1 Map.is_empty_2.

  Lemma map_valid_replay_mem' : forall ents d ms,
    log_valid ents d ->
    map_valid ms d ->
    map_valid (replay_mem ents ms) d.
  Proof.
    unfold map_valid, log_valid; intros.
    destruct (InA_dec (@eq_key_dec valu) (a, v) ents).
    eapply H; eauto.
    eapply H0.
    eapply replay_mem_not_in'.
    3: eauto. apply H.
    contradict n.
    apply In_fst_KIn; simpl; auto.
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


  Section UnfoldProof2.
  Local Hint Unfold rep map_replay rep_inner synced_rep: hoare_unfold.

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
    Forall (fun e => fst e < length d) (Map.elements ms).
  Proof.
    unfold map_valid; intros.
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
    Forall (fun e => e < length d) (map fst (Map.elements ms)).
  Proof.
    unfold map_valid; intros.
    apply Forall_forall; intros.
    autorewrite with lists.
    apply In_map_fst_MapIn in H0.
    apply MapFacts.elements_in_iff in H0.
    destruct H0.
    eapply (H x).
    apply Map.elements_2; eauto.
  Qed.

  Lemma apply_synced_data_ok' : forall l d,
    NoDup (map fst l) ->
    vssync_vecs (vsupd_vecs d l) (map fst l) = replay_disk l d.
  Proof.
    induction l; intros; simpl; auto.
    destruct a; simpl.
    inversion H; subst.
    rewrite <- IHl by auto.

    rewrite vsupd_vecs_vsupd_notin by auto.
    rewrite vssync_vsupd_eq.
    rewrite updN_vsupd_vecs_notin; auto.
  Qed.

  Lemma apply_synced_data_ok : forall xp m d,
    arrayN (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (map_keys m))
    =p=> synced_rep xp (replay_disk (Map.elements m) d).
  Proof.
    unfold synced_rep; intros.
    apply arrayN_unify.
    apply apply_synced_data_ok'.
    apply KNoDup_NoDup; auto.
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
    arrayN (DataStart xp) (vsupd_vecs d (firstn n (Map.elements m)))
       =p=> unsync_rep xp m d.
  Proof.
    unfold unsync_rep, map_replay; cancel.
    apply apply_unsync_applying_ok'.
    apply KNoDup_NoDup; auto.
  Qed.

  Lemma vsupd_selN_not_in : forall l a d,
    NoDup (map fst l) ->
    ~ In a (map fst l) ->
    selN (vsupd_vecs d l) a ($0, nil) = selN d a ($0, nil).
  Proof.
    induction l; intros; destruct a; simpl in *; auto; intuition.
    inversion H; subst.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite selN_updN_ne; eauto.
  Qed.

  Lemma apply_unsync_syncing_ok' : forall l a d n,
    NoDup (map fst l) ->
    ~ In a (map fst l) ->
    selN d a ($0, nil) = selN (vssync_vecs (vsupd_vecs d l) (firstn n (map fst l))) a ($0, nil).
  Proof.
    induction l; intros; simpl.
    rewrite firstn_nil; simpl; auto.

    destruct a; inversion H; simpl in *; subst; intuition.
    destruct n; simpl; auto.
    rewrite vsupd_vecs_vsupd_notin by auto.
    unfold vsupd.
    rewrite selN_updN_ne by auto.
    rewrite vsupd_selN_not_in; auto.
    
    unfold vssync.
    rewrite -> updN_vsupd_vecs_notin by auto.
    rewrite <- IHl; auto.
    rewrite selN_updN_ne by auto.
    unfold vsupd.
    rewrite selN_updN_ne; auto.
  Qed.

  Lemma apply_unsync_syncing_ok : forall xp m d n,
    arrayN (DataStart xp) (vssync_vecs (vsupd_vecs d (Map.elements m)) (firstn n (map_keys m)))
       =p=> unsync_rep xp m d.
  Proof.
    unfold unsync_rep, equal_unless_in; cancel.
    rewrite vssync_vecs_length, vsupd_vecs_length; auto.
    apply apply_unsync_syncing_ok'.
    apply KNoDup_NoDup; auto.
    eauto.
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
  Local Hint Unfold rep map_replay rep_inner: hoare_unfold.
  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

  Theorem apply_ok: forall xp ms,
    {< F d na,
    PRE
      rep xp F na (Synced d) ms
    POST RET:ms'
      rep xp F (LogLen xp) (Synced d) ms' * [[ Map.Empty (MSInLog ms') ]]
    CRASH
      exists ms', rep xp F (LogLen xp) (Synced d) ms' \/
                  rep xp F na (Synced d) ms' \/
                  rep xp F na (Applying d) ms'
    >} apply xp ms.
  Proof.
    unfold apply; intros.
    step.
    unfold synced_rep; cancel.
    step.
    rewrite vsupd_vecs_length.
    apply map_valid_Forall_synced_map_fst; auto.
    step.
    step.

    rewrite vssync_vecs_length, vsupd_vecs_length; auto.
    apply map_valid_map0.
    rewrite apply_synced_data_ok'; auto.
    apply KNoDup_NoDup; auto.

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
    or_r; cancel.
    rewrite apply_synced_data_ok; cancel.

    (* synced nil *)
    or_l. norm.
    instantiate (2 := mk_memstate vmap0 cs).
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
    or_l; cancel.
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


  Local Hint Unfold map_replay : hoare_unfold.
  Hint Extern 1 ({{_}} progseq (apply _ _) _) => apply apply_ok : prog.
  Hint Extern 1 ({{_}} progseq (flush_noapply _ _ _) _) => apply flush_noapply_ok : prog.
  Hint Extern 0 (okToUnify (synced_rep ?a _) (synced_rep ?a _)) => constructor : okToUnify.

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





  Lemma map_valid_updN : forall m d a v,
    map_valid m d -> map_valid m (updN d a v).
  Proof.
    unfold map_valid; simpl; intuition.
    eapply H; eauto.
    rewrite length_updN.
    eapply H; eauto.
  Qed.

  Lemma map_valid_equal : forall d m1 m2,
    Map.Equal m1 m2 -> map_valid m1 d -> map_valid m2 d.
  Proof.
    induction d; unfold map_valid; simpl; intros; split;
    eapply H0; rewrite H; eauto.
  Qed.


  Lemma equal_unless_in_length_eq : forall a b l,
    equal_unless_in l a b -> length b = length a.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.

  Lemma length_eq_map_valid : forall m a b,
    map_valid m a -> length b = length a -> map_valid m b.
  Proof.
    unfold map_valid; firstorder.
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


  Lemma replay_disk_eq_length_eq : forall l l' a b,
    replay_disk l a = replay_disk l' b ->
    length a = length b.
  Proof.
    induction l; destruct l'; simpl; intros; subst;
    repeat rewrite replay_disk_length; autorewrite with lists; auto.
    setoid_rewrite <- length_updN.
    eapply IHl; eauto.
  Qed.

  Lemma ptsto_replay_disk_not_in' : forall l F a v d,
    ~ In a (map fst l) ->
    KNoDup l ->
    (F * a |-> v)%pred (list2nmem (replay_disk l d)) ->
    ((arrayN_ex d a) * a |-> v)%pred (list2nmem d).
  Proof.
    induction l; simpl; intros; auto.
    erewrite list2nmem_sel with (x := v); eauto.
    apply list2nmem_ptsto_cancel.
    eapply list2nmem_ptsto_bound; eauto.

    inversion H0; destruct a; subst.
    erewrite list2nmem_sel with (x := v); eauto.
    eapply IHl; simpl; auto.
    rewrite replay_disk_updN_comm, selN_updN_ne.
    apply list2nmem_ptsto_cancel.
    apply list2nmem_ptsto_bound in H1.
    rewrite replay_disk_length, length_updN in *; auto.
    intuition.
    contradict H4.
    apply In_KIn; auto.
    Unshelve. all: eauto.
  Qed.

  Lemma ptsto_replay_disk_not_in : forall F a v d m,
    ~ Map.In a m ->
    (F * a |-> v)%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    ((arrayN_ex d a) * a |-> v)%pred (list2nmem d).
  Proof.
    intros.
    eapply ptsto_replay_disk_not_in'; eauto.
    contradict H.
    apply In_map_fst_MapIn; auto.
  Qed.

  Lemma list2nmem_replay_disk_vsupd_not_in : forall F a v vc vo m d,
    ~ Map.In a m ->
    (F * a |-> (vc, vo))%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    (F * a |-> (v, vsmerge (vc, vo)))%pred (list2nmem (replay_disk (Map.elements m) (vsupd d a v))).
  Proof.
    intros.
    setoid_rewrite replay_disk_updN_comm.
    erewrite <- list2nmem_sel.
    eapply list2nmem_updN; eauto.
    eapply ptsto_replay_disk_not_in; eauto.
    contradict H.
    apply In_map_fst_MapIn; auto.
  Qed.

  Lemma list2nmem_replay_disk_vsupd_empty : forall F a v vc vo m d,
    Map.Empty m ->
    (F * a |-> (vc, vo))%pred (list2nmem (replay_disk (Map.elements m) d)) ->
    (F * a |-> (v, vsmerge (vc, vo)))%pred (list2nmem (replay_disk (Map.elements m) (vsupd d a v))).
  Proof.
    unfold vsupd; intros.
    apply MapProperties.elements_Empty in H.
    rewrite H in *; simpl in *.
    erewrite <- list2nmem_sel by eauto.
    eapply list2nmem_updN; eauto.
  Qed.


  Definition dwrite T xp a v ms rx : prog T :=
    let '(oms, cs) := (MSInLog ms, MSCache ms) in
    ms' <- IfRx irx (MapFacts.In_dec oms a) {
      ms <- apply xp ms;
      irx ms
    } else {
      irx ms
    };
    cs' <- BUFCACHE.write_array (DataStart xp) a v (MSCache ms');
    rx (mk_memstate (MSInLog ms') cs').


  Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.

  Theorem dwrite_ok: forall xp a v ms,
    {< F Fd d na vs,
    PRE
      rep xp F na (Synced d) ms *
      [[[ d ::: (Fd * a |-> vs) ]]]
    POST RET:ms' exists d' na',
      rep xp F na' (Synced d') ms' *
      [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    CRASH
      exists ms' d' na',
      rep xp F na' (Applying d') ms' * [[[ d' ::: (Fd * a |-> vs) ]]] \/
      rep xp F na' (Synced d')   ms' * [[[ d' ::: (Fd * a |-> vs) ]]] \/
      rep xp F na' (Synced d')   ms' * [[[ d' ::: (Fd * a |-> (v, vsmerge(vs))) ]]]
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite.
    step.

    (* case 1: apply happens *)
    step.
    prestep.
    unfold rep at 1, rep_inner at 1.
    unfold synced_rep, map_replay in *.
    cancel; auto.
    replace (length d0) with (length d).
    eapply list2nmem_inbound; eauto.
    subst; erewrite replay_disk_length; eauto.

    step.
    unfold rep, rep_inner, synced_rep, map_replay; cancel.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    apply list2nmem_replay_disk_vsupd_empty; auto.

    (* crashes for case 1 *)
    cancel.
    or_r; or_l.
    unfold rep, rep_inner, synced_rep, map_replay; cancel; eauto.
    instantiate (ms' := mk_memstate  (MSInLog r_) cs'); cancel.
    pred_apply; cancel.

    cancel.
    or_r; or_r.
    unfold rep, rep_inner, synced_rep, map_replay; cancel; eauto.
    instantiate (ms'3 := mk_memstate  (MSInLog r_) cs'); cancel.
    pred_apply; cancel.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    apply list2nmem_replay_disk_vsupd_empty; auto.

    or_r; or_l; cancel.
    or_r; or_l; cancel.
    or_l; cancel.


    (* case 2: no apply *)
    prestep.
    unfold rep, rep_inner, synced_rep, map_replay; cancel; eauto.
    replace (length d0) with (length d).
    eapply list2nmem_inbound; eauto.
    subst; erewrite replay_disk_length; eauto.

    step.
    unfold rep, rep_inner, synced_rep, map_replay; cancel.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    apply list2nmem_replay_disk_vsupd_not_in; eauto.

    (* crashes for case 2 *)
    cancel.
    or_r; or_l.
    unfold rep, rep_inner, synced_rep, map_replay; cancel; eauto.
    instantiate (ms' := mk_memstate (MSInLog ms) cs'); cancel.
    pred_apply; cancel.

    or_r; or_r.
    unfold rep, rep_inner, synced_rep, map_replay; cancel; eauto.
    instantiate (ms'0 := mk_memstate  (MSInLog ms) cs'); cancel.
    pred_apply; cancel.
    unfold vsupd; autorewrite with lists; auto.
    apply map_valid_updN; auto.
    apply list2nmem_replay_disk_vsupd_not_in; eauto.
  Qed.



  Hint Rewrite selN_combine repeat_selN' Nat.min_id synced_list_length : lists.

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
    | [H : possible_crash_list _ _ |- _ ] => apply possible_crash_list_length in H
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

  Lemma equal_unless_in_updN : forall B l a (b : B) v d d',
    ~ KIn (a, b) l ->
    equal_unless_in (a :: map fst l) d d' ->
    equal_unless_in (map fst l) (updN d a (v, nil)) (updN d' a (v, nil)).
  Proof.
    unfold equal_unless_in, synced_list; intuition; simpl in *.
    simplen.
    destruct (lt_dec a0 (length d)).
    destruct (Nat.eq_dec a a0); simplen.
    repeat rewrite selN_updN_ne by auto.
    rewrite <- H2; simplen; tauto.
    repeat rewrite selN_oob; simplen.
  Qed.

  Lemma equal_unless_in_sym : forall l a b,
    equal_unless_in l a b <-> equal_unless_in l b a.
  Proof.
    unfold equal_unless_in; firstorder.
  Qed.

  Lemma equal_unless_in_replay_disk' : forall l a b,
    KNoDup l ->
    equal_unless_in (map fst l) a b ->
    replay_disk l a = replay_disk l b.
  Proof.
    induction l; intuition; simpl.
    eapply list_selN_ext; intros.
    simplen.
    apply H0; auto.

    inversion H; simpl in *; subst.
    eapply IHl; auto.
    eapply equal_unless_in_updN; eauto.
  Qed.

  Lemma equal_unless_in_replay_disk : forall a b m,
    equal_unless_in (map_keys m) b a ->
    replay_disk (Map.elements m) a = replay_disk (Map.elements m) b.
  Proof.
    intros.
    eapply equal_unless_in_replay_disk'; eauto.
    apply equal_unless_in_sym; auto.
  Qed.

  Lemma list2nmem_replay_disk_crash_xform : forall ents vsl vl (F : rawpred),
    KNoDup ents ->
    possible_crash_list vsl vl ->
    F (list2nmem (replay_disk ents vsl)) ->
    crash_xform F (list2nmem (replay_disk ents (synced_list vl))).
  Proof.
    induction ents; simpl; intros.
    eapply list2nmem_crash_xform; eauto.
    inversion H; destruct a; simpl in *; subst.
    rewrite synced_list_updN.
    eapply IHents; eauto.
    apply possible_crash_list_updN; auto.
  Qed.

  Lemma map_valid_replay_mem_app : forall a ents l' x0 x1,
     Map.Equal x0 (replay_mem a vmap0) ->
     map_valid x0 x1 ->
     possible_crash_list x1 l' ->
     log_valid ents (replay_disk (Map.elements (elt:=valu) x0) x1) ->
     map_valid (replay_mem (a ++ ents) vmap0) (synced_list l').
  Proof.
      intros.
      eapply map_valid_equal.
      apply MapFacts.Equal_sym.
      apply replay_mem_app; auto.
      apply map_valid_replay_mem'.
      destruct H2; split; intros; auto.
      specialize (H3 _ _ H4); destruct H3.
      simplen.
      eapply map_valid_equal; eauto.
      unfold map_valid; intros.
      destruct (H0 _ _ H3); simplen.
  Qed.


  Definition recover_either_pred xp Fold Fnew :=
    (exists na ms d ents,
      ( rep_inner xp na (Synced d) ms *
          [[[ d ::: Fold ]]]
     \/ rep_inner xp na (Synced (replay_disk ents d)) ms *
          [[[ replay_disk ents d ::: Fnew ]]]
     \/ rep_inner xp na (Flushing d ents) ms *
          [[[ d ::: Fold ]]] *
          [[[ replay_disk ents d ::: Fnew ]]]
     \/ rep_inner xp na (Applying d) ms *
          [[[ d ::: Fold ]]]
      ))%pred.

  Definition after_crash_pred xp Fold Fnew:=
    (exists na ms d, 
      rep_inner xp na (Synced d) ms *
      ([[[ d ::: crash_xform Fold ]]] \/ [[[ d ::: crash_xform Fnew ]]])
    )%pred.

  Hint Rewrite crash_xform_arrayN
    DLog.xform_rep_synced  DLog.xform_rep_truncated
    DLog.xform_rep_extended DLog.xform_rep_extended_unsync: crash_xform.


  Lemma recover_either_after_crash : forall xp Fold Fnew,
    crash_xform (recover_either_pred xp Fold Fnew) =p=>
    after_crash_pred xp Fold Fnew.
  Proof.
    unfold recover_either_pred, after_crash_pred, rep_inner,
           map_replay, synced_rep, unsync_rep; intros.
    repeat progress (xform; norml; unfold stars; simpl; clear_norm_goal);
       cancel; t.

    (* Synced d *)
    or_l; cancel; t.
    eapply list2nmem_replay_disk_crash_xform; eauto.

    (* Synced (replay_disk ents d) *)
    or_r; cancel; t.
    eapply list2nmem_replay_disk_crash_xform; eauto.
    rewrite <- H3; auto.

    (* Flushing d ents :: ExtendedUnsync d *)
    or_l; cancel.
    eapply list2nmem_replay_disk_crash_xform; eauto.
    (* Flushing d ents :: Extended d *)
    or_l; cancel.
    eapply list2nmem_replay_disk_crash_xform; eauto.
    (* Flushing d ents :: Synced (replay_disk ents d) *)
    or_r; cancel.
    eapply list2nmem_replay_disk_crash_xform; eauto.
    setoid_rewrite mapeq_elements.
    2: apply replay_mem_app; eauto.
    rewrite <- replay_disk_replay_mem; auto.
    eapply map_valid_replay_mem_app; eauto.

    (* Applying d :: unsync *)
    or_l; cancel.
    eapply list2nmem_replay_disk_crash_xform; eauto.
    erewrite equal_unless_in_replay_disk; eauto.
    (* Applying d :: synced *)
    or_l; cancel.
    eapply list2nmem_replay_disk_crash_xform; eauto.
    rewrite replay_disk_twice; auto.
    (* Applying d :: Truncated *)
    or_l; cancel.
    eapply list2nmem_crash_xform; eauto.
    apply map_valid_map0.
  Qed.

  Remove Hints MapFacts.Equal_refl.

  Lemma recover_either_after_crash_unfold : forall xp F Fold Fnew,
    crash_xform (F * recover_either_pred xp Fold Fnew)
      =p=>
    crash_xform F * exists na ms log old new,
       synced_rep xp old * DLog.rep xp (DLog.Synced na log) *
       [[ new = replay_disk (Map.elements ms) old ]] *
       [[ Map.Equal ms (replay_mem log vmap0) ]] *
       [[ goodSize addrlen (length old) /\ map_valid ms old ]] *
       ([[[ new ::: crash_xform Fold ]]] \/ [[[ new ::: crash_xform Fnew ]]]).
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
    rx (mk_memstate (replay_mem log vmap0) cs).

  Theorem recover_ok: forall xp F cs,
    {< raw Fold Fnew,
    PRE
      BUFCACHE.rep cs raw *
      [[ crash_xform (F * recover_either_pred xp Fold Fnew)%pred raw ]]
    POST RET:ms' exists na d',
      rep xp (crash_xform F) na (Synced d') ms' *
      ([[[ d' ::: crash_xform Fold ]]] \/ [[[ d' ::: crash_xform Fnew ]]])
    CRASH exists raw' cs',
      BUFCACHE.rep cs' raw' *
      [[ (crash_xform F * recover_either_pred xp (crash_xform Fold) (crash_xform Fnew))%pred raw' ]]
    >} recover xp cs.
  Proof.
    unfold recover; intros.
    prestep; xform.
    norml.

    (* manually get two after-crash cases *)
    apply recover_either_after_crash_unfold in H4.
    destruct_lifts.
    apply sep_star_or_distr in H0; apply pimpl_or_apply in H0.
    destruct H0; destruct_lift H0.

    (* case 1 : last transaction unapplied *)
    - cancel.
      step.
      unfold rep; cancel.
      or_l; cancel; eauto.

      unfold synced_rep, rep_inner, map_replay.
      cancel; try map_rewrites; auto.

      pimpl_crash; unfold recover_either_pred, rep_inner, map_replay; cancel.
      or_l; cancel; eauto.

    (* case 2 : last transaction applied *)
    - cancel.
      step.
      unfold rep; cancel.
      or_r; cancel; eauto.

      unfold rep_inner, map_replay, synced_rep.
      cancel; try map_rewrites; auto.

      subst; pimpl_crash; unfold recover_either_pred, rep_inner, map_replay; cancel.
      or_r; or_l; cancel; eauto.
      Unshelve. eauto.
  Qed.

End MLog.
