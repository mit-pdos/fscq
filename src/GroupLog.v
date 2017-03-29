Require Import Arith.
Require Import Bool.
Require Import List.
Require Import Hashmap.
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
Require Import DiskLogHash.
Require Import MapUtils.
Require Import ListPred.
Require Import LogReplay.
Require Import DiskSet.

Import ListNotations.

Set Implicit Arguments.



Module GLog.

  Import AddrMap LogReplay ReplaySeq LogNotations.


  (************* state and rep invariant *)

  Record mstate := mk_mstate {
    MSVMap  : valumap;
    (* collapsed updates for all committed but unflushed txns,
        necessary for fast read() operation
     *)
    MSTxns  : txnlist;
    (* list of all unflushed txns, the order should match the
       second part of diskset. (first element is the latest)
    *)

    MSMLog  : MLog.mstate;
    (* lower-level states *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate vm ts ll : memstate := 
    (mk_mstate vm ts (MLog.MSInLog ll), (MLog.MSCache ll)).
  Definition mk_memstate0 := mk_mstate vmap0 nil vmap0.

  Definition MSCache (ms : memstate) := snd ms.
  Definition MSLL (ms : memstate) := MLog.mk_memstate (MSMLog (fst ms)) (snd ms).

  Definition readOnly (ms ms' : memstate) := (fst ms = fst ms').

  Lemma readOnlyLL : forall ms ms',
    MLog.readOnly (MSLL ms) (MSLL ms') ->
    MSVMap (fst ms) = MSVMap (fst ms') ->
    MSTxns (fst ms) = MSTxns (fst ms') ->
    readOnly ms ms'.
  Proof.
    destruct ms as [m c]; destruct m.
    destruct ms' as [m' c']; destruct m'.
    unfold MLog.readOnly, readOnly; simpl; congruence.
  Qed.

  Hint Resolve readOnlyLL.


  Inductive state :=
  | Cached   (ds : diskset)
  | Flushing (ds : diskset) (n : addr)
  | Rollback (d : diskstate)
  | Recovering (d : diskstate)
  .

  Definition vmap_match vm ts :=
    Map.Equal vm (fold_right replay_mem vmap0 ts).

  Definition ents_valid xp d ents :=
    log_valid ents d /\ length ents <= LogLen xp.

  Definition effective (ds : diskset) tslen := popn (length (snd ds) - tslen) ds.

  Definition dset_match xp ds ts :=
    Forall (ents_valid xp (fst ds)) ts /\ ReplaySeq ds ts.

  Definition rep xp st ms hm :=
  let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
  (match st with
    | Cached ds =>
      let ds' := effective ds (length ts) in
      [[ vmap_match vm ts ]] *
      [[ dset_match xp ds' ts ]] * exists nr,
      MLog.rep xp (MLog.Synced nr (fst ds')) mm hm
    | Flushing ds n =>
      let ds' := effective ds (length ts) in
      [[ dset_match xp ds' ts /\ n <= length ts ]] *
      MLog.would_recover_either xp (nthd n ds') (selR ts n nil) hm
    | Rollback d =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp (d, nil) ts ]] *
      MLog.rep xp (MLog.Rollback d) mm hm
    | Recovering d =>
      [[ vmap_match vm ts ]] *
      [[ dset_match xp (d, nil) ts ]] *
      MLog.rep xp (MLog.Recovering d) mm hm
  end)%pred.

  Definition would_recover_any xp ds hm :=
    (exists ms n ds',
      [[ NEListSubset ds ds' ]] *
      rep xp (Flushing ds' n) ms hm)%pred.

  Local Hint Resolve nelist_subset_equal.

  Lemma sync_invariant_rep : forall xp st ms hm,
    sync_invariant (rep xp st ms hm).
  Proof.
    unfold rep; destruct st; intros; eauto.
  Qed.

  Hint Resolve sync_invariant_rep.

  Lemma sync_invariant_would_recover_any : forall xp ds hm,
    sync_invariant (would_recover_any xp ds hm).
  Proof.
    unfold would_recover_any; intros; auto.
  Qed.

  Hint Resolve sync_invariant_would_recover_any.

  Lemma nthd_effective : forall n ds tslen,
    nthd n (effective ds tslen) = nthd (length (snd ds) - tslen + n) ds.
  Proof.
    unfold effective; intros.
    rewrite nthd_popn; auto.
  Qed.

  Lemma latest_effective : forall ds n,
    latest (effective ds n) = latest ds.
  Proof.
    unfold effective; intros.
    rewrite latest_popn; auto.
  Qed.

  Lemma effective_length : forall ds n,
    n <= (length (snd ds)) ->
    length (snd (effective ds n)) = n.
  Proof.
    unfold effective; intros.
    rewrite length_popn.
    omega.
  Qed.

  Lemma effective_length_le : forall ds n,
    length (snd (effective ds n)) <= length (snd ds).
  Proof.
    unfold effective; intros.
    rewrite length_popn.
    omega.
  Qed.


  Lemma cached_recover_any: forall xp ds ms hm,
    rep xp (Cached ds) ms hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep.
    intros. norm.
    cancel.
    rewrite nthd_effective, Nat.add_0_r.
    apply MLog.synced_recover_either.
    intuition.
  Qed.

  Lemma cached_recovering: forall xp ds ms hm,
    rep xp (Cached ds) ms hm =p=>
      exists n ms', rep xp (Recovering (nthd n ds)) ms' hm.
  Proof.
    unfold rep.
    intros. norm.
    cancel.
    rewrite MLog.rep_synced_pimpl.
    eassign (mk_mstate vmap0 nil (MSMLog ms)).
    cancel.
    intuition simpl; auto.
    unfold vmap_match; simpl; congruence.
    unfold dset_match; intuition.
    apply Forall_nil.
    constructor.
  Qed.

  Lemma flushing_recover_any: forall xp n ds ms hm,
    rep xp (Flushing ds n) ms hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep; intros; cancel.
  Qed.

  Lemma rollback_recover_any: forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=> would_recover_any xp (d, nil) hm.
  Proof.
    unfold would_recover_any, rep; intros.
    norm. unfold stars; simpl.
    rewrite nthd_0; cancel.
    rewrite MLog.rollback_recover_either.
    2: intuition.
    eauto.
    eauto.
  Qed.

  Lemma rollback_recovering: forall xp d ms hm,
    rep xp (Rollback d) ms hm =p=> rep xp (Recovering d) ms hm.
  Proof.
    unfold rep; intros.
    cancel.
    rewrite MLog.rep_rollback_pimpl.
    auto.
  Qed.


  Lemma rep_hashmap_subset : forall xp ms hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st ms hm
        =p=> rep xp st ms hm'.
  Proof.
    unfold rep; intros.
    destruct st; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.would_recover_either_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
  Qed.


  (************* program *)

  Definition read xp a (ms : memstate) :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    match Map.find a vm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- MLog.read xp a mm;
        Ret ^(mk_memstate vm ts mm', v)
    end.

  (* Submit a committed transaction.
     It might fail if the transaction is too big to fit into the log.
     We handle the anomaly here so that flushall() can always succeed.
     This keep the interface compatible with current Log.v, in which
     only commit() can fail, and the caller can choose to abort.
  *)
  Definition submit xp ents ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    let vm' := replay_mem ents vm in
    If (le_dec (length ents) (LogLen xp)) {
      Ret ^(mk_memstate vm' (ents :: ts) mm, true)
    } else {
      Ret ^(ms, false)
    }.

  Definition flushall_nomerge xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    let^ (mm) <- ForN i < length ts
    Hashmap hm
    Ghost [ F ds crash ]
    Loopvar [ mm ]
    Invariant
        exists nr,
        << F, MLog.rep: xp (MLog.Synced nr (nthd i ds)) mm hm >>
    OnCrash crash
    Begin
      (* r = false is impossible, flushall should always succeed *)
      let^ (mm, r) <- MLog.flush xp (selN ts (length ts - i - 1) nil) mm;
      Ret ^(mm)
    Rof ^(mm);
    Ret (mk_memstate vmap0 nil mm).

  Definition flushall xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (le_dec (Map.cardinal vm) (LogLen xp)) {
      let^ (mm, r) <- MLog.flush xp (Map.elements vm) mm;
      Ret (mk_memstate vmap0 nil mm)
    } else {
      ms <- flushall_nomerge xp ms;
      Ret ms
    }.

  Definition flushsync xp ms :=
    ms <- flushall xp ms;
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.apply xp mm;
    Ret (mk_memstate vm ts mm').

  Definition flushall_noop xp ms :=
    ms <- flushall xp ms;
    Ret ms.

  Definition flushsync_noop xp ms :=
    ms <- flushsync xp ms;
    Ret ms.

  Definition sync_cache xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.sync_cache xp mm;
    Ret (mk_memstate vm ts mm').

  Definition dwrite' (xp : log_xparams) a v ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite xp a v mm;
    Ret (mk_memstate vm ts mm').

  Definition dwrite (xp : log_xparams) a v ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (MapFacts.In_dec vm a) {
      ms <- flushall_noop xp ms;
      ms <- dwrite' xp a v ms;
      Ret ms
    } else {
      ms <- dwrite' xp a v ms;
      Ret ms
    }.

  Definition dwrite_vecs' (xp : log_xparams) avs ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite_vecs xp avs mm;
    Ret (mk_memstate vm ts mm').

  Definition dwrite_vecs (xp : log_xparams) avs ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (bool_dec (overlap (map fst avs) vm) true) {
      ms <- flushall_noop xp ms;
      ms <- dwrite_vecs' xp avs ms;
      Ret ms
    } else {
      ms <- dwrite_vecs' xp avs ms;
      Ret ms
    }.

  Definition dsync xp a ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync xp a mm;
    Ret (mk_memstate vm ts mm').

  Definition dsync_vecs xp al ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync_vecs xp al mm;
    Ret (mk_memstate vm ts mm').

  Definition recover xp cs :=
    mm <- MLog.recover xp cs;
    Ret (mk_memstate vmap0 nil mm).

  Definition init xp cs :=
    mm <- MLog.init xp cs;
    Ret (mk_memstate vmap0 nil mm).


  Arguments MLog.rep: simpl never.
  Hint Extern 0 (okToUnify (MLog.rep _ _ _ _) (MLog.rep _ _ _ _)) => constructor : okToUnify.



  (************* auxilary lemmas *)

  Lemma diskset_ptsto_bound_latest : forall F xp a vs ds ts,
    dset_match xp ds ts ->
    (F * a |-> vs)%pred (list2nmem ds!!) ->
    a < length (fst ds).
  Proof.
    intros.
    apply list2nmem_ptsto_bound in H0.
    erewrite <- replay_seq_latest_length; auto.
    apply H.
  Qed.

  Lemma diskset_vmap_find_none : forall ds ts vm a v vs xp F,
    dset_match xp ds ts ->
    vmap_match vm ts ->
    Map.find a vm = None ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    selN (fst ds) a ($0, nil) = (v, vs).
  Proof.
    unfold vmap_match, dset_match.
    intros ds ts; destruct ds; revert l.
    induction ts; intuition; simpl in *;
      denote ReplaySeq as Hs;inversion Hs; subst; simpl.
    denote ptsto as Hx; rewrite singular_latest in Hx by easy; simpl in Hx.
    erewrite surjective_pairing at 1.
    erewrite <- list2nmem_sel; eauto; simpl; auto.

    rewrite H0 in H1.
    eapply IHts.
    split; eauto.
    eapply Forall_cons2; eauto.

    apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono; eauto.

    rewrite latest_cons in *.
    eapply ptsto_replay_disk_not_in'; [ | | eauto].
    eapply map_find_replay_mem_not_in; eauto.
    denote Forall as Hx; apply Forall_inv in Hx; apply Hx.
  Qed.

  Lemma replay_seq_replay_mem : forall ds ts xp,
    ReplaySeq ds ts ->
    Forall (ents_valid xp (fst ds)) ts ->
    replay_disk (Map.elements (fold_right replay_mem vmap0 ts)) (fst ds) = latest ds.
  Proof.
    induction 1; simpl in *; intuition.
    rewrite latest_cons; subst.
    unfold latest in *; simpl in *.
    rewrite <- IHReplaySeq by (eapply Forall_cons2; eauto).
    rewrite replay_disk_replay_mem; auto.
    inversion H1; subst.
    eapply log_valid_length_eq.
    unfold ents_valid in *; intuition; eauto.
    rewrite replay_disk_length; auto.
  Qed.

  Lemma diskset_vmap_find_ptsto : forall ds ts vm a w v vs F xp,
    dset_match xp ds ts ->
    vmap_match vm ts ->
    Map.find a vm = Some w ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    w = v.
  Proof.
    unfold vmap_match, dset_match; intuition.
    eapply replay_disk_eq; eauto.
    eexists; rewrite H0.
    erewrite replay_seq_replay_mem; eauto.
  Qed.

  Lemma dset_match_ext : forall ents ds ts xp,
    dset_match xp ds ts ->
    log_valid ents ds!! ->
    length ents <= LogLen xp ->
    dset_match xp (pushd (replay_disk ents ds!!) ds) (ents :: ts).
  Proof.
    unfold dset_match, pushd, ents_valid; intuition; simpl in *.
    apply Forall_cons; auto; split; auto.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_latest_length; eauto.
    constructor; auto.
  Qed.

  Lemma vmap_match_nil : vmap_match vmap0 nil.
  Proof.
      unfold vmap_match; simpl; apply MapFacts.Equal_refl.
  Qed.

  Lemma dset_match_nil : forall d xp, dset_match xp (d, nil) nil.
  Proof.
      unfold dset_match; split; [ apply Forall_nil | constructor ].
  Qed.

  Lemma dset_match_length : forall ds ts xp,
    dset_match xp ds ts -> length ts = length (snd ds).
  Proof.
    intros.
    erewrite replay_seq_length; eauto.
    apply H.
  Qed.

  Lemma dset_match_log_valid_selN : forall ds ts i n xp,
    dset_match xp ds ts ->
    log_valid (selN ts i nil) (nthd n ds).
  Proof.
    unfold dset_match, ents_valid; intuition; simpl in *.
    destruct (lt_dec i (length ts)).
    eapply Forall_selN with (i := i) in H0; intuition.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_nthd_length; eauto.
    rewrite selN_oob by omega.
    unfold log_valid, KNoDup; intuition; inversion H.
  Qed.

  Lemma vmap_match_find : forall ts vmap,
    vmap_match vmap ts
    -> forall a v, KIn (a, v) (Map.elements vmap)
    -> Forall (@KNoDup valu) ts
    -> exists t, In t ts /\ In a (map fst t).
  Proof.
    induction ts; intros; simpl.
    unfold vmap_match in *; simpl in *.
    rewrite H in H0.
    unfold KIn in H0.
    apply InA_nil in H0; intuition.

    destruct (in_dec Nat_as_OT.eq_dec a0 (map fst a)).
    (* The address was written by the newest transaction. *)
    exists a; intuition.

    unfold vmap_match in *; simpl in *.
    remember (fold_right replay_mem vmap0 ts) as vmap_ts.
    destruct (in_dec Nat_as_OT.eq_dec a0 (map fst (Map.elements vmap_ts))).
    (* The address was written by an older transaction. *)
    replace a0 with (fst (a0, v)) in * by auto.
    apply In_fst_KIn in i.
    eapply IHts in i.
    deex.
    exists t; intuition.
    congruence.
    eapply Forall_cons2; eauto.
    rewrite Forall_forall in H1.
    specialize (H1 a).
    simpl in *; intuition.

    (* The address wasn't written by an older transaction. *)
    denote KIn as HKIn.
    apply KIn_fst_In in HKIn.
    apply In_map_fst_MapIn in HKIn.
    apply In_MapsTo in HKIn.
    deex.
    eapply replay_mem_not_in' in H1.
    denote (Map.MapsTo) as Hmap.
    eapply MapsTo_In in Hmap.
    eapply In_map_fst_MapIn in Hmap.
    apply n0 in Hmap; intuition.
    auto.
    rewrite <- H.
    eauto.
  Qed.

  Lemma dset_match_log_valid_grouped : forall ts vmap ds xp,
    vmap_match vmap ts
    -> dset_match xp ds ts
    -> log_valid (Map.elements vmap) (fst ds).
  Proof.
    intros.

    assert (HNoDup: Forall (@KNoDup valu) ts).
      unfold dset_match in *; simpl in *; intuition.
      unfold ents_valid, log_valid in *.
      eapply Forall_impl; try eassumption.
      intros; simpl; intuition.
      intuition.

    unfold log_valid; intuition;
    eapply vmap_match_find in H; eauto.
    deex.
    denote In as HIn.
    unfold dset_match in *; intuition.
    rewrite Forall_forall in H.
    eapply H in H3.
    unfold ents_valid, log_valid in *; intuition.
    replace 0 with (fst (0, v)) in * by auto.
    apply In_fst_KIn in HIn.
    apply H5 in HIn; intuition.

    deex.
    denote In as HIn.
    unfold dset_match in *; intuition.
    rewrite Forall_forall in H.
    eapply H in H2.
    unfold ents_valid, log_valid in *; intuition.
    replace a with (fst (a, v)) in * by auto.
    apply In_fst_KIn in HIn.
    apply H5 in HIn; intuition.
  Qed.


  Lemma dset_match_ent_length_exfalso : forall xp ds ts i,
    length (selN ts i nil) > LogLen xp ->
    dset_match xp ds ts ->
    False.
  Proof.
    unfold dset_match, ents_valid; intuition.
    destruct (lt_dec i (length ts)).
    eapply Forall_selN with (i := i) (def := nil) in H1; intuition.
    eapply le_not_gt; eauto.
    rewrite selN_oob in H; simpl in H; omega.
  Qed.


  Lemma ents_valid_length_eq : forall xp d d' ts,
    Forall (ents_valid xp d ) ts ->
    length d = length d' ->
    Forall (ents_valid xp d') ts.
  Proof.
    unfold ents_valid in *; intros.
    rewrite Forall_forall in *; intuition.
    eapply log_valid_length_eq; eauto.
    apply H; auto.
    apply H; auto.
  Qed.

  Lemma dset_match_nthd_S : forall xp ds ts n,
    dset_match xp ds ts ->
    n < length ts ->
    replay_disk (selN ts (length ts - n - 1) nil) (nthd n ds) = nthd (S n) ds.
  Proof.
    unfold dset_match; intuition.
    repeat erewrite replay_seq_nthd; eauto.
    erewrite skipn_sub_S_selN_cons; simpl; eauto.
  Qed.

  Lemma dset_match_replay_disk_grouped : forall ts vmap ds xp,
    vmap_match vmap ts
    -> dset_match xp ds ts
    -> replay_disk (Map.elements vmap) (fst ds) = nthd (length ts) ds.
  Proof.
    intros; simpl in *.
    denote dset_match as Hdset.
    apply dset_match_length in Hdset as Hlength.
    unfold dset_match in *.
    intuition.

    unfold vmap_match in *.
    rewrite H.
    erewrite replay_seq_replay_mem; eauto.
    erewrite nthd_oob; eauto.
    omega.
  Qed.

  Lemma dset_match_grouped : forall ts vmap ds xp,
    length (snd ds) > 0
    -> Map.cardinal vmap <= LogLen xp
    -> vmap_match vmap ts
    -> dset_match xp ds ts
    -> dset_match xp (fst ds, [ds !!]) [Map.elements vmap].
  Proof.
    intros.
    unfold dset_match; intuition simpl.
    unfold ents_valid.
    apply Forall_forall; intros.
    inversion H3; subst; clear H3.
    split.
    eapply dset_match_log_valid_grouped; eauto.
    setoid_rewrite <- Map.cardinal_1; eauto.

    inversion H4.

    econstructor.
    simpl.
    erewrite dset_match_replay_disk_grouped; eauto.
    erewrite dset_match_length; eauto.
    rewrite nthd_oob; auto.
    constructor.
  Qed.

  Lemma recover_before_any : forall xp ds ts hm,
    dset_match xp (effective ds (length ts)) ts ->
    MLog.would_recover_before xp ds!! hm =p=>
    would_recover_any xp ds hm.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite <- latest_nthd.
    rewrite latest_effective.
    eassign (mk_mstate vmap0 ts vmap0); simpl.
    cancel.
    apply MLog.recover_before_either.
    intuition simpl; auto.
    rewrite cuttail_length; omega.
  Qed.

  Lemma recover_before_any_fst : forall xp ds ts hm len,
    dset_match xp (effective ds (length ts)) ts ->
    len = length ts ->
    MLog.would_recover_before xp (fst (effective ds len)) hm =p=>
    would_recover_any xp ds hm.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite nthd_0.
    eassign (mk_mstate vmap0 ts vmap0); simpl.
    rewrite MLog.recover_before_either.
    cancel.
    intuition simpl; auto.
    omega.
  Qed.

  Lemma synced_recover_any : forall xp ds nr ms ts hm,
    dset_match xp (effective ds (length ts)) ts ->
    MLog.rep xp (MLog.Synced nr ds!!) ms hm =p=>
    would_recover_any xp ds hm.
  Proof.
    intros.
    rewrite MLog.synced_recover_before.
    eapply recover_before_any; eauto.
  Qed.

  Lemma recover_latest_any : forall xp ds hm ts,
    dset_match xp ds ts ->
    would_recover_any xp (ds!!, nil) hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    inversion H1.
    apply nelist_subset_latest.
  Qed.

  Lemma recover_latest_any_effective : forall xp ds hm ts,
    dset_match xp (effective ds (length ts)) ts ->
    would_recover_any xp (ds!!, nil) hm =p=> would_recover_any xp ds hm.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    inversion H1.
    apply nelist_subset_latest.
  Qed.

  Lemma cached_length_latest : forall F xp ds ms hm m,
    (F * rep xp (Cached ds) ms hm)%pred m ->
    length ds!! = length (fst (effective ds (length (MSTxns ms)))).
  Proof.
    unfold rep, dset_match; intuition.
    destruct_lift H.
    denote ReplaySeq as Hx.
    apply replay_seq_latest_length in Hx; simpl in Hx; rewrite <- Hx.
    rewrite latest_effective; auto.
  Qed.

  Lemma cached_latest_cached: forall xp ds ms hm,
    rep xp (Cached (ds!!, nil)) ms hm =p=> rep xp (Cached ds) ms hm.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl; clear_norm_goal.
    assert (MSTxns ms = nil) as Heq.
    apply dset_match_length in H2; simpl in H2.
    apply length_nil; auto.
    rewrite Heq in *; cancel.
    rewrite nthd_0, Nat.sub_0_r; simpl.
    rewrite latest_nthd; cancel.
    unfold effective.
    rewrite Nat.sub_0_r; simpl.
    rewrite popn_oob; auto.
  Qed.


  (************* correctness theorems *)

  Definition init_ok : forall xp cs,
    {< F l d m,
    PRE:hm   BUFCACHE.rep cs d *
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * PaddedLog.DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:hm' RET: ms
          << F, rep: xp (Cached (m, nil)) ms hm' >> 
    XCRASH:hm_crash any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    step.
    apply vmap_match_nil.
    apply dset_match_nil.
  Qed.


  Lemma dset_match_nthd_effective_fst : forall xp ds ts,
    dset_match xp (effective ds (length ts)) ts ->
    nthd (length (snd ds) - length ts) ds = fst (effective ds (length ts)).
  Proof.
    intros.
    rewrite <- nthd_0.
    rewrite nthd_effective.
    rewrite Nat.add_0_r; auto.
  Qed.


  Lemma effective_pushd_comm : forall n d ds,
    effective (pushd d ds) (S n) = pushd d (effective ds n).
  Proof.
    unfold effective; simpl; intros.
    rewrite popn_pushd_comm by omega; auto.
  Qed.

  Theorem read_ok: forall xp ms a,
    {< F ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds!! ::: exists F', (F' * a |-> vs) ]]]
    POST:hm' RET:^(ms', r)
      << F, rep: xp (Cached ds) ms' hm' >> * [[ r = fst vs ]] * [[ readOnly ms ms' ]]
    CRASH:hm'
      exists ms', << F, rep: xp (Cached ds) ms' hm' >>
    >} read xp a ms.
  Proof.
    unfold read, rep.
    prestep.
    cancel.

    (* case 1 : return from vmap *)
    step.
    eapply diskset_vmap_find_ptsto; eauto.
    rewrite latest_effective; eauto.
    pimpl_crash; cancel.

    (* case 2: read from MLog *)
    cancel.
    eexists; apply list2nmem_ptsto_cancel_pair.
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply diskset_ptsto_bound_latest; eauto.
    rewrite latest_effective; eauto.

    step; subst.
    erewrite fst_pair; eauto.
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply diskset_vmap_find_none; eauto.
    rewrite latest_effective; eauto.
    pimpl_crash; cancel.
    eassign (mk_mstate (MSVMap ms_1) (MSTxns ms_1) ms'_1); cancel.
    all: auto.
  Qed.


  Theorem submit_ok: forall xp ents ms,
    {< F ds,
    PRE:hm
        << F, rep: xp (Cached ds) ms hm >> *
        [[ log_valid ents ds!! ]]
    POST:hm' RET:^(ms', r)
        ([[ r = false /\ length ents > LogLen xp ]] *
         << F, rep: xp (Cached ds) ms' hm' >> *
        [[ ms' = ms ]])
     \/ ([[ r = true  ]] *
          << F, rep: xp (Cached (pushd (replay_disk ents (latest ds)) ds)) ms' hm' >>)
    CRASH:hm'
      exists ms', << F, rep: xp (Cached ds) ms' hm' >>
    >} submit xp ents ms.
  Proof.
    unfold submit, rep.
    step.
    step.
    or_r; cancel.
    rewrite nthd_pushd' by omega; eauto.

    unfold vmap_match in *; simpl.
    denote! (Map.Equal _ _) as Heq.
    rewrite Heq; apply MapFacts.Equal_refl.

    rewrite effective_pushd_comm.
    erewrite <- latest_effective.
    apply dset_match_ext; auto.
    rewrite latest_effective; auto.
    step.
    Unshelve. all: try exact vmap0; eauto.
  Qed.



  Local Hint Resolve vmap_match_nil dset_match_nil.
  Opaque MLog.flush.

  Theorem flushall_nomerge_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall_nomerge xp ms.
  Proof.
    unfold flushall_nomerge, would_recover_any, rep.
    prestep.
    cancel.

    rewrite nthd_effective, Nat.add_0_r.
    apply sep_star_comm.

    - safestep.
      eapply dset_match_log_valid_selN; eauto.
      safestep.

      (* flush() returns true *)
      erewrite dset_match_nthd_S by eauto; cancel.
      eexists.

      (* flush() returns false, this is impossible *)
      exfalso; eapply dset_match_ent_length_exfalso; eauto.

      (* crashes *)
      subst; repeat xcrash_rewrite.
      xform_norm; cancel.
      xform_normr. safecancel.
      eassign (mk_mstate vmap0 (MSTxns ms_1) vmap0); simpl.
      rewrite selR_inb by eauto; cancel.
      all: simpl; auto; omega.

    - safestep.
      rewrite nthd_oob, latest_effective, nthd_0.
      cancel.
      erewrite <- dset_match_length; eauto.
      apply dset_match_nil.

    - cancel.
      xcrash_rewrite.
      (* manually construct an RHS-like pred, but replace hm'' with hm *)
      instantiate (1 := (exists raw cs, BUFCACHE.rep cs raw *
        [[ (F * exists ms n, 
          [[ dset_match xp (effective ds (length (MSTxns ms))) (MSTxns ms)
            /\ n <= length (MSTxns ms) ]] *
          MLog.would_recover_either xp (nthd n (effective ds (length (MSTxns ms))))
           (selR (MSTxns ms) n nil) hm)%pred raw ]])%pred ).
      xform_norm; cancel.
      xform_normr; safecancel.
      apply MLog.would_recover_either_hashmap_subset.
      all: eauto.
    Unshelve. all: constructor.
  Qed.


  Hint Extern 1 ({{_}} Bind (flushall_nomerge _ _) _) => apply flushall_nomerge_ok : prog.

  Opaque flushall_nomerge.

  Theorem flushall_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall xp ms.
  Proof.
    unfold flushall.
    safestep.

    prestep; denote rep as Hx; unfold rep in Hx; destruct_lift Hx.
    cancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply dset_match_log_valid_grouped; eauto.

    prestep; unfold rep; safecancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite dset_match_replay_disk_grouped; eauto.
    erewrite nthd_oob; eauto.
    rewrite latest_effective, nthd_0; eauto.
    erewrite dset_match_length at 1; eauto.
    apply dset_match_nil.

    denote (length _ > _) as Hf; contradict Hf.
    setoid_rewrite <- Map.cardinal_1; omega.
    apply dset_match_nil.

    xcrash.
    erewrite dset_match_nthd_effective_fst; eauto.
    unfold would_recover_any, rep.
    destruct (MSTxns ms_1);
    norm; unfold stars; simpl.

    unfold vmap_match in *; simpl in *.
    denote (Map.Equal _ vmap0) as Heq.
    rewrite Heq.
    replace (Map.elements _) with (@nil (Map.key * valu)) by auto.
    rewrite nthd_effective.
    eassign (mk_mstate vmap0 nil (MSMLog ms_1)); simpl.
    rewrite Nat.add_0_r, selR_oob by auto.
    cancel.
    intuition.

    eassign (fst (effective ds (S (length t))), latest ds :: nil).
    eassign (mk_mstate vmap0 (Map.elements (MSVMap ms_1) :: nil) (MSMLog ms_1)); simpl.
    rewrite nthd_0.
    unfold selR; simpl; rewrite nthd_0; simpl.
    cancel.

    assert (length (snd ds) > 0).
    denote dset_match as Hx.
    apply dset_match_length in Hx; simpl in Hx.
    rewrite cuttail_length in Hx; omega.
    intuition.
    rewrite <- nthd_0, nthd_effective, Nat.add_0_r.
    apply nelist_subset_nthd_latest; omega.

    unfold effective; simpl; rewrite popn_0.
    replace (S (length t)) with (length (c :: t)) by auto.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite <- latest_effective; eauto.
    eapply dset_match_grouped; eauto; simpl.
    rewrite cuttail_length; omega.

    safestep.
    repeat match goal with
              | [ H := ?e |- _ ] => subst H
            end; cancel.
    step.

    Unshelve. all: try exact nil; eauto; try exact vmap0.
  Qed.


  Hint Extern 1 ({{_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (submit _ _ _) _) => apply submit_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushall _ _) _) => apply flushall_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.

  Theorem flushall_noop_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached ds) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushall_noop xp ms.
  Proof.
    unfold flushall_noop; intros.
    safestep.
    step.
    apply cached_latest_cached.
  Qed.

  Theorem flushsync_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushsync xp ms.
  Proof.
    unfold flushsync.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    xcrash.
    denote rep as Hx; unfold rep in Hx.
    destruct_lift Hx.
    eapply recover_before_any; eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (flushsync _ _) _) => apply flushsync_ok : prog.

  Theorem flushsync_noop_ok: forall xp ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached ds) ms' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = vmap0 ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} flushsync_noop xp ms.
  Proof.
    unfold flushsync_noop.
    safestep.
    step.
    apply cached_latest_cached.
  Qed.

  Hint Extern 1 ({{_}} Bind (flushall_noop _ _) _) => apply flushall_noop_ok : prog.
  Hint Extern 1 ({{_}} Bind (flushsync_noop _ _) _) => apply flushsync_noop_ok : prog.

  Lemma forall_ents_valid_length_eq : forall xp d d' ts,
    Forall (ents_valid xp d) ts ->
    length d' = length d ->
    Forall (ents_valid xp d') ts.
  Proof.
    unfold ents_valid; intros.
    rewrite Forall_forall in *.
    intros.
    specialize (H _ H1); intuition.
    eapply log_valid_length_eq; eauto.
  Qed.

  Lemma vmap_match_notin : forall ts vm a,
    Map.find a vm = None ->
    vmap_match vm ts ->
    Forall (fun e => ~ In a (map fst e)) ts.
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    constructor; simpl in *.
    eapply map_find_replay_mem_not_in.
    rewrite <- H0; auto.

    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono.
    rewrite <- H0; auto.
  Qed.

  Lemma dset_match_dsupd_notin : forall xp ds a v ts vm,
    Map.find a vm = None ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dsupd ds a v) ts.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply length_updN.
    apply replay_seq_dsupd_notin; auto.
    eapply vmap_match_notin; eauto.
  Qed.

  Lemma forall_ents_valid_ents_filter : forall ts xp d f,
    Forall (ents_valid xp d) ts ->
    Forall (ents_valid xp d) (map (fun x => filter f x) ts).
  Proof.
    induction ts; simpl; auto; intros.
    inversion H; subst.
    constructor; auto.
    split; destruct H2.
    apply log_vaild_filter; eauto.
    eapply le_trans.
    apply filter_length. auto.
  Qed.

  Lemma forall_ents_valid_ents_remove : forall ts xp d a,
    Forall (ents_valid xp d) ts ->
    Forall (ents_valid xp d) (map (ents_remove a) ts).
  Proof.
    intros; apply forall_ents_valid_ents_filter; auto.
  Qed.

  Lemma forall_ents_valid_ents_remove_list : forall ts xp d al,
    Forall (ents_valid xp d) ts ->
    Forall (ents_valid xp d) (map (ents_remove_list al) ts).
  Proof.
    intros; apply forall_ents_valid_ents_filter; auto.
  Qed.

  Lemma dset_match_dsupd : forall xp ts ds a v,
    dset_match xp ds ts ->
    dset_match xp (dsupd ds a v) (map (ents_remove a) ts).
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply ents_valid_length_eq.
    2: rewrite length_updN; auto.
    apply forall_ents_valid_ents_remove; auto.
    apply replay_seq_dsupd_ents_remove; auto.
  Qed.

  Lemma dset_match_dssync_vecs : forall xp ts ds al,
    dset_match xp ds ts ->
    dset_match xp (dssync_vecs ds al) ts.
  Proof.
    unfold dset_match; intuition; simpl in *; auto.
    eapply ents_valid_length_eq.
    2: apply eq_sym; apply vssync_vecs_length.
    auto.
    apply replay_seq_dssync_vecs_ents; auto.
  Qed.

  Lemma dset_match_dssync : forall xp ds a ts,
    dset_match xp ds ts ->
    dset_match xp (dssync ds a) ts.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply length_updN.
    apply replay_seq_dssync_notin; auto.
  Qed.

  Lemma effective_dsupd_comm : forall ds a v n,
    effective (dsupd ds a v) n = dsupd (effective ds n) a v.
  Proof.
    unfold effective, dsupd; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.

  Lemma effective_dsupd_vecs_comm : forall ds avl n,
    effective (dsupd_vecs ds avl) n = dsupd_vecs (effective ds n) avl.
  Proof.
    unfold effective, dsupd_vecs; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.

  Lemma effective_dssync_vecs_comm : forall ds al n,
    effective (dssync_vecs ds al) n = dssync_vecs (effective ds n) al.
  Proof.
    unfold effective, dssync_vecs; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.

  Lemma effective_dssync_comm : forall ds a n,
    effective (dssync ds a) n = dssync (effective ds n) a.
  Proof.
    unfold effective, dssync; simpl; intros.
    rewrite map_length.
    apply dmap_popn_comm.
  Qed.

  Lemma cached_dsupd_latest_recover_any : forall xp ds a v ms hm ms0,
    dset_match xp (effective ds (length ms0)) ms0 ->
    rep xp (Cached ((dsupd ds a v) !!, nil)) ms hm =p=>
    would_recover_any xp (dsupd ds a v) hm.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    rewrite synced_recover_any; auto.
    rewrite effective_dsupd_comm, map_length.
    eapply dset_match_dsupd; eauto.
  Qed.

  Lemma cached_dssync_vecs_latest_recover_any : forall xp ds al ms hm ms0,
    dset_match xp (effective ds (length ms0)) ms0 ->
    rep xp (Cached ((dssync_vecs ds al) !!, nil)) ms hm =p=>
    would_recover_any xp (dssync_vecs ds al) hm.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    unfold would_recover_any, rep.
    rewrite synced_recover_any; auto.
    rewrite effective_dssync_vecs_comm.
    eapply dset_match_dssync_vecs; eauto.
  Qed.

  Lemma cached_latest_recover_any : forall xp ds ms hm ms0,
    dset_match xp (effective ds (length ms0)) ms0 ->
    rep xp (Cached (ds !!, nil)) ms hm =p=>
    would_recover_any xp ds hm.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    unfold would_recover_any, rep.
    rewrite synced_recover_any; eauto.
  Qed.


  Theorem dwrite'_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Map.find a (MSVMap (fst ms)) = None ]] *
      [[[ fst (effective ds (length (MSTxns (fst ms)))) ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists ds',
      << F, rep: xp (Cached ds') ms' hm' >> *
      [[  ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
      \/ exists ms' d',
      << F, rep: xp (Cached (d', nil)) ms' hm' >> *
      [[  d' = updN (fst (effective ds (length (MSTxns (fst ms))))) a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge vs)) ]]]
    >} dwrite' xp a v ms.
  Proof.
    unfold dwrite', rep.
    step.
    erewrite dset_match_nthd_effective_fst; eauto.
    safestep.
    3: eauto.

    erewrite dset_match_nthd_effective_fst; eauto; simpl.
    erewrite dset_match_length, map_length; eauto.
    rewrite dsupd_nthd.
    cancel.
    rewrite effective_dsupd_comm.
    eapply dset_match_dsupd_notin; eauto.

    (* crashes *)
    subst; repeat xcrash_rewrite.
    xform_norm.
    or_l; cancel.
    xform_normr; cancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    rewrite recover_before_any_fst by eauto; cancel.

    or_r; cancel.
    xform_normr; cancel.
    xform_normr; cancel.
    rewrite nthd_0; simpl.
    eassign (mk_mstate vmap0 nil x_1); simpl; cancel.
    all: simpl; eauto.
    apply dset_match_nil.
  Qed.


  Hint Extern 1 ({{_}} Bind (dwrite' _ _ _ _) _) => apply dwrite'_ok : prog.

  Lemma diskset_ptsto_bound_effective : forall F xp a vs ds ts,
    dset_match xp (effective ds (length ts)) ts ->
    (F * a |-> vs)%pred (list2nmem ds!!) ->
    a < length (nthd (length (snd ds) - length ts) ds).
  Proof.
    intros.
    apply list2nmem_ptsto_bound in H0.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite <- replay_seq_latest_length; auto.
    rewrite latest_effective; auto.
    apply H.
  Qed.

  Theorem dwrite_ok: forall xp a v ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd ds a (v, vsmerge vs))) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      << F, would_recover_any: xp (dsupd ds a (v, vsmerge vs)) hm' -- >>
    >} dwrite xp a v ms.
  Proof.
    unfold dwrite, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; safecancel.
    substl (MSVMap a0); eauto.
    substl (MSTxns a0); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    simpl; pred_apply; cancel.
    auto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    substl (MSTxns a0); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    rewrite <- dsupd_latest.
    rewrite synced_recover_any; eauto.

    rewrite effective_dsupd_comm, map_length.
    eapply dset_match_dsupd; eauto.
    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    (* 2nd case: no flushall *)
    prestep; unfold rep; cancel.
    apply MapFacts.not_find_in_iff; auto.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_effective; eauto.

    prestep. norm. cancel.
    intuition simpl. pred_apply.
    repeat rewrite map_length.
    rewrite <- surjective_pairing in *.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite diskset_vmap_find_none; eauto; auto.
    cancel.
    erewrite <- diskset_vmap_find_none with (v := vs_cur).
    erewrite <- dset_match_nthd_effective_fst; eauto.
    all: eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).

    rewrite nthd_0; simpl.
    rewrite <- surjective_pairing in *; simpl.
    rewrite <- dsupd_nthd.
    rewrite MLog.synced_recover_before.
    rewrite dsupd_nthd.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite <- dsupd_fst, <- effective_dsupd_comm.
    rewrite recover_before_any_fst.
    erewrite diskset_vmap_find_none; eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.
    rewrite effective_dsupd_comm.
    eapply dset_match_dsupd; eauto.
    rewrite map_length; eauto.
    rewrite map_length; auto.
  Qed.


  Theorem dsync_ok: forall xp a ms,
    {< F Fd ds vs,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dssync ds a)) ms' hm' >>
    CRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync xp a ms.
  Proof.
    unfold dsync.
    prestep; unfold rep; cancel.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_effective; eauto.

    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dssync_nthd; cancel.
    rewrite effective_dssync_comm.
    eapply dset_match_dssync; eauto.

    cancel.
    rewrite MLog.synced_recover_before.
    erewrite dset_match_nthd_effective_fst; eauto.
    rewrite recover_before_any_fst; eauto.
    Unshelve. eauto.
  Qed.


  Lemma vmap_match_nonoverlap : forall ts vm al,
    overlap al vm = false ->
    vmap_match vm ts ->
    Forall (fun e => disjoint al (map fst e)) ts.
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    rewrite H0 in H; simpl in *.
    constructor; simpl in *.
    eapply nonoverlap_replay_mem_disjoint; eauto.
    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_nonoverlap_mono; eauto.
  Qed.

  Lemma dset_match_dsupd_vecs_nonoverlap : forall xp avl vm ds ts,
    overlap (map fst avl) vm = false ->
    vmap_match vm ts ->
    dset_match xp ds ts ->
    dset_match xp (dsupd_vecs ds avl) ts.
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply vsupd_vecs_length.
    apply replay_seq_dsupd_vecs_disjoint; auto.
    eapply vmap_match_nonoverlap; eauto.
  Qed.

  Theorem dwrite_vecs'_ok: forall xp avl ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ overlap (map fst avl) (MSVMap (fst ms)) = false ]] *
      [[ Forall (fun e => fst e < length (fst (effective ds (length (MSTxns (fst ms)))))) avl 
         /\ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      exists ms',
      << F, rep: xp (Cached (vsupd_vecs (fst (effective ds (length (MSTxns (fst ms))))) avl, nil)) ms' hm' >>
    >} dwrite_vecs' xp avl ms.
  Proof.
    unfold dwrite_vecs'.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dsupd_vecs_nthd; cancel.
    rewrite effective_dsupd_vecs_comm.
    eapply dset_match_dsupd_vecs_nonoverlap; eauto.

    xcrash.
    or_l; xform_norm; cancel.
    xform_normr; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite recover_before_any_fst by eauto; cancel.

    or_r; xform_norm; cancel.
    xform_normr; cancel.
    rewrite nthd_0.
    repeat erewrite dset_match_nthd_effective_fst by eauto.
    eassign (mk_mstate vmap0 nil x0_1); simpl; cancel.
    all: simpl; eauto.
    apply dset_match_nil.
  Qed.

  Hint Extern 1 ({{_}} Bind (dwrite_vecs' _ _ _) _) => apply dwrite_vecs'_ok : prog.

  Lemma effective_avl_addrs_ok : forall (avl : list (addr * valu)) ds ts xp,
    Forall (fun e => fst e < length (ds !!)) avl ->
    dset_match xp (effective ds (length ts)) ts ->
    Forall (fun e => fst e < length (nthd (length (snd ds) - length ts) ds)) avl.
  Proof.
    intros.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    rewrite latest_effective; eauto.
    unfold dset_match in *; intuition eauto.
  Qed.

  Theorem dwrite_vecs_ok: forall xp avl ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Forall (fun e => fst e < length (ds!!)) avl /\ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds avl)) ms' hm' >>
    XCRASH:hm'
      << F, would_recover_any: xp ds hm' -- >> \/
      << F, would_recover_any: xp (dsupd_vecs ds avl) hm' -- >>
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; safecancel.
    substl (MSVMap a).
    apply overlap_empty; apply map_empty_vmap0.
    eapply effective_avl_addrs_ok; eauto.
    auto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    substl (MSTxns a); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    rewrite <- dsupd_vecs_latest.
    rewrite synced_recover_any; eauto.
    eassign (MSTxns a); substl (MSTxns a); simpl.
    unfold effective; rewrite popn_oob by omega.
    apply dset_match_nil.

    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    prestep; unfold rep; cancel.
    apply not_true_iff_false; auto.
    eapply effective_avl_addrs_ok; eauto.

    step.
    cancel.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite <- dsupd_vecs_fst, <- effective_dsupd_vecs_comm.
    rewrite MLog.synced_recover_before.
    rewrite recover_before_any_fst.
    auto.

    rewrite effective_dsupd_vecs_comm.
    eapply dset_match_dsupd_vecs_nonoverlap.
    apply not_true_is_false; eauto.
    all: eauto.
  Qed.


  Theorem dsync_vecs_ok: forall xp al ms,
    {< F ds,
    PRE:hm
      << F, rep: xp (Cached ds) ms hm >> *
      [[ Forall (fun e => e < length (ds!!)) al /\ sync_invariant F ]]
    POST:hm' RET:ms'
      << F, rep: xp (Cached (dssync_vecs ds al)) ms' hm' >>
    CRASH:hm'
      << F, would_recover_any: xp ds hm' -- >>
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs.
    prestep; unfold rep; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    rewrite latest_effective; eauto.
    unfold dset_match in *; intuition eauto.

    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dssync_vecs_nthd; cancel.
    rewrite effective_dssync_vecs_comm.
    eapply dset_match_dssync_vecs; eauto.

    cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite MLog.synced_recover_before.
    rewrite recover_before_any_fst; eauto.
  Qed.

  Definition recover_any_pred xp ds hm :=
    ( exists d n ms, [[ n <= length (snd ds) ]] *
      (rep xp (Cached (d, nil)) ms hm \/
        rep xp (Rollback d) ms hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]])%pred.

  Theorem sync_invariant_recover_any_pred : forall xp ds hm,
    sync_invariant (recover_any_pred xp ds hm).
  Proof.
    unfold recover_any_pred; intros; auto 10.
  Qed.
  Hint Resolve sync_invariant_recover_any_pred.

  Lemma NEListSubset_effective : forall ds ds' n,
    NEListSubset ds ds' ->
    NEListSubset ds (effective ds' n).
  Proof.
    unfold effective; intros.
    apply nelist_subset_popn'; auto.
  Qed.

  Theorem crash_xform_any : forall xp ds hm,
    crash_xform (would_recover_any xp ds hm) =p=>
                 recover_any_pred  xp ds hm.
  Proof.
    unfold would_recover_any, recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_either.
    erewrite dset_match_length in H3; eauto.
    denote NEListSubset as Hds.
    eapply NEListSubset_effective in Hds.
    eapply nelist_subset_nthd in Hds as Hds'; eauto.
    deex.
    denote nthd as Hnthd.
    unfold MLog.recover_either_pred; xform_norm.

    - norm. cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      or_l; cancel.
      apply dset_match_nil.
      intuition simpl.
      eassumption.
      setoid_rewrite Hnthd; auto.

    - destruct (Nat.eq_dec x0 (length (MSTxns x))) eqn:Hlength; subst.
      norm. cancel.
      or_l; cancel.
      rewrite nthd_0.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      apply dset_match_nil.
      eassign n; intuition; simpl.
      setoid_rewrite Hnthd.
      pred_apply.
      rewrite selR_oob by auto; simpl; auto.

      denote (length (snd x1)) as Hlen.
      eapply nelist_subset_nthd with (n':=S x0) in Hds; eauto.
      deex.
      clear Hnthd.
      denote nthd as Hnthd.
      norm. cancel.
      or_l; cancel.
      rewrite nthd_0.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      apply dset_match_nil.
      eassign n1.
      unfold selR in *.
      destruct (lt_dec x0 (length (MSTxns x))); intuition.
      pred_apply.
      erewrite dset_match_nthd_S in *; eauto.
      setoid_rewrite Hnthd; auto.
      denote dset_match as Hx.
      apply dset_match_length in Hx; simpl in Hx; omega.
      denote dset_match as Hx. 
      apply dset_match_length in Hx; simpl in Hx; simpl.
      rewrite cuttail_length in *. omega.

    - norm. cancel.
      or_r; cancel.
      eassign (mk_mstate vmap0 nil ms'); eauto.
      auto.
      auto.
      eassign n.
      intuition.
      setoid_rewrite Hnthd.
      pred_apply.
      erewrite nthd_effective, dset_match_length; eauto.
  Qed.

  Lemma crash_xform_recovering : forall xp d mm hm,
    crash_xform (rep xp (Recovering d) mm hm) =p=>
                 recover_any_pred xp (d, nil) hm.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_recovering.
    instantiate (1:=nil).
    unfold MLog.recover_either_pred.
    norm.
    unfold stars; simpl.
    or_l; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    apply dset_match_nil.
    intuition simpl; eauto.
    or_l; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    apply dset_match_nil.
    intuition simpl; eauto.
    or_r; cancel.
    eassign (mk_mstate vmap0 nil ms'); cancel.
    auto.
    apply dset_match_nil.
    intuition simpl; eauto.
  Qed.

  Lemma crash_xform_cached : forall xp ds ms hm,
    crash_xform (rep xp (Cached ds) ms hm) =p=>
      exists d n ms', rep xp (Cached (d, nil)) ms' hm *
        [[[ d ::: (crash_xform (diskIs (list2nmem (nthd n ds)))) ]]] *
        [[ n <= length (snd ds) ]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_synced; norm.
    eassign (mk_mstate vmap0 nil ms'); simpl.
    cancel.
    intuition simpl.
    auto.
    apply dset_match_nil.
    pred_apply.
    cancel.
    omega.
  Qed.

  Lemma crash_xform_rollback : forall xp d ms hm,
    crash_xform (rep xp (Rollback d) ms hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' hm *
        [[[ d' ::: (crash_xform (diskIs (list2nmem d))) ]]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_rollback.
    cancel.
    eassign (mk_mstate vmap0 nil ms'); eauto.
    all: auto.
  Qed.

  Lemma any_pred_any : forall xp ds hm,
    recover_any_pred xp ds hm =p=>
    exists d, would_recover_any xp (d, nil) hm.
  Proof.
    unfold recover_any_pred; intros.
    xform_norm.
    rewrite cached_recover_any; cancel.
    rewrite rollback_recover_any; cancel.
  Qed.


  Lemma recover_idem : forall xp ds hm,
    crash_xform (recover_any_pred xp ds hm) =p=>
                 recover_any_pred xp ds hm.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    - rewrite MLog.crash_xform_synced.
      norm.
      eassign (mk_mstate (MSVMap x1) (MSTxns x1) ms'); cancel.
      or_l; cancel.
      replace d' with x in *.
      intuition simpl; eauto.
      apply list2nmem_inj.
      eapply crash_xform_diskIs_eq; eauto.
      intuition.
      erewrite Nat.min_l.
      eassign x0.
      eapply crash_xform_diskIs_trans; eauto.
      auto.

    - rewrite MLog.crash_xform_rollback.
      norm.
      eassign (mk_mstate (MSVMap x1) (MSTxns x1) ms'); cancel.
      or_r; cancel.
      denote (dset_match) as Hdset; inversion Hdset as (_, H').
      inversion H'.
      auto.
      intuition simpl; eauto.
      eapply crash_xform_diskIs_trans; eauto.
  Qed.


  Theorem recover_ok: forall xp cs,
    {< F raw ds,
    PRE:hm
      BUFCACHE.rep cs raw *
      [[ (F * recover_any_pred xp ds hm)%pred raw ]] *
      [[ sync_invariant F ]]
    POST:hm' RET:ms' exists raw',
      BUFCACHE.rep (MSCache ms') raw' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Cached (d, nil)) (fst ms') hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
      )%pred raw' ]]
    XCRASH:hm'
      exists raw' cs' mm', BUFCACHE.rep cs' raw' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Recovering d) mm' hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
          )%pred raw' ]]
    >} recover xp cs.
  Proof.
    unfold recover, recover_any_pred, rep.
    prestep. norm'l.
    denote or as Hx.
    apply sep_star_or_distr in Hx.
    destruct Hx; destruct_lift H; safecancel.

    (* Cached *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_l; cancel.
    eassign F. cancel.
    or_l; cancel. auto.

    safestep. eauto.
    apply dset_match_nil.
    eassumption.
    apply dset_match_nil.
    instantiate (1:=nil); cancel.

    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate vmap0 nil x1); eauto.
    intuition simpl; eauto.
    cancel.
    intuition simpl; eauto.

    (* Rollback *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_r; cancel.
    auto.

    safestep. eauto.
    apply dset_match_nil.
    eassumption.
    apply dset_match_nil.
    instantiate (1:=nil); cancel.

    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate vmap0 nil x1); eauto.
    intuition simpl; eauto.
    cancel.
    intuition simpl; eauto.
  Qed.


  Hint Extern 1 ({{_}} Bind (recover _ _) _) => apply recover_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


End GLog.

