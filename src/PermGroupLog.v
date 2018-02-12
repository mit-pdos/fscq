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
Require Import ListUtils.
Require Import MapUtils.
(*
Require Import ListPred.
*)
Require Import FSLayout.

Require Export PermMemLog PermDiskSet.

Import ListNotations.

Set Implicit Arguments.



Module GLog.

  Import AddrMap LogReplay ReplaySeq LogNotations.


  (************* state and rep invariant *)

  Record mstate := mk_mstate {
    MSVMap  : handlemap;
    (* collapsed updates for all committed but unflushed txns,
        necessary for fast read() operation
     *)
    MSTxns  : list input_contents;
    (* list of all unflushed txns, the order should match the
       second part of diskset. (first element is the latest)
    *)

    MSMLog  : MLog.mstate;
    (* lower-level states *)
  }.

  Definition memstate := (mstate * cachestate)%type.
  Definition mk_memstate vm ts ll : memstate := 
    (mk_mstate vm ts (MLog.MSInLog ll), (MLog.MSCache ll)).
  Definition mk_memstate0 := mk_mstate hmap0 nil hmap0.

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
    Map.Equal vm (fold_right replay_mem hmap0 ts).
  
  Definition ents_valid {T} xp d (ents: @generic_contents T) :=
    log_valid ents d /\ length ents <= LogLen xp.

  Definition effective (ds : diskset) tslen := popn (length (snd ds) - tslen) ds.

  Definition dset_match xp ds ts :=
    Forall (ents_valid xp (fst ds)) ts /\ ReplaySeq ds ts.


  Definition rep xp st ms bm hm :=
  let '(vm, ts, mm) := (MSVMap ms, MSTxns ms, MSMLog ms) in
  (match st with
    | Cached ds =>
      let ds' := effective ds (length ts) in
      [[ vmap_match vm ts ]] *
      [[ handles_valid_nested bm ts ]] *
      [[ dset_match xp ds' (extract_blocks_nested bm ts) ]] * exists nr,
      MLog.rep xp (MLog.Synced nr (fst ds')) mm bm hm
    | Flushing ds n =>
      let ds' := effective ds (length ts) in
      [[ handles_valid_nested bm ts ]] *
      [[ dset_match xp ds' (extract_blocks_nested bm ts) /\ n <= length ts ]] *
      MLog.would_recover_either xp (nthd n ds') (selR (extract_blocks_nested bm ts) n nil) bm hm
    | Rollback d =>
      [[ vmap_match vm ts ]] *
      [[ handles_valid_nested bm ts ]] *
      [[ dset_match xp (d, nil) (extract_blocks_nested bm ts) ]] *
      MLog.rep xp (MLog.Rollback d) mm bm hm
    | Recovering d =>
      [[ vmap_match vm ts ]] *
      [[ handles_valid_nested bm ts ]] *
      [[ dset_match xp (d, nil) (extract_blocks_nested bm ts) ]] *
      MLog.rep xp (MLog.Recovering d) mm bm hm
  end)%pred.

  Definition would_recover_any xp ds bm hm :=
    (exists ms n ds',
      [[ NEListSubset ds ds' ]] *
      rep xp (Flushing ds' n) ms bm hm)%pred.

  Local Hint Resolve nelist_subset_equal.

  Lemma sync_invariant_rep : forall xp st ms bm hm,
    sync_invariant (rep xp st ms bm hm).
  Proof.
    unfold rep; destruct st; intros; eauto 10.
  Qed.

  Hint Resolve sync_invariant_rep.

  Lemma sync_invariant_would_recover_any : forall xp ds bm hm,
    sync_invariant (would_recover_any xp ds bm hm).
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


  Lemma cached_recover_any: forall xp ds ms bm hm,
    rep xp (Cached ds) ms bm hm =p=> would_recover_any xp ds bm hm.
  Proof.
    unfold would_recover_any, rep.
    intros. norm.
    cancel.
    rewrite nthd_effective, Nat.add_0_r.
    apply MLog.synced_recover_either.
    intuition.
  Qed.

  Lemma cached_recovering: forall xp ds ms bm hm,
    rep xp (Cached ds) ms bm hm =p=>
      exists n ms', rep xp (Recovering (nthd n ds)) ms' bm hm.
  Proof.
    unfold rep.
    intros. norm.
    cancel.
    rewrite MLog.rep_synced_pimpl.
    eassign (mk_mstate hmap0 nil (MSMLog ms)).
    cancel.
    intuition simpl; auto.
    unfold vmap_match; simpl; congruence.
    apply Forall_nil.
    unfold dset_match; intuition.
    apply Forall_nil.
    constructor.    
  Qed.

  Lemma flushing_recover_any: forall xp n ds ms bm hm,
    rep xp (Flushing ds n) ms bm hm =p=> would_recover_any xp ds bm hm.
  Proof.
    unfold would_recover_any, rep; intros; cancel.
  Qed.

  Lemma rollback_recover_any: forall xp d ms bm hm,
    rep xp (Rollback d) ms bm hm =p=> would_recover_any xp (d, nil) bm hm.
  Proof.
    unfold would_recover_any, rep; intros.
    norm. unfold stars; simpl.
    rewrite nthd_0; cancel.
    rewrite MLog.rollback_recover_either.
    2: intuition.
    eauto.
    eauto.
    eauto.
  Qed.

  Lemma rollback_recovering: forall xp d ms bm hm,
    rep xp (Rollback d) ms bm hm =p=> rep xp (Recovering d) ms bm hm.
  Proof.
    unfold rep; intros.
    cancel.
    rewrite MLog.rep_rollback_pimpl.
    auto.
  Qed.


  Lemma rep_hashmap_subset : forall xp ms bm hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st ms bm hm
        =p=> rep xp st ms bm hm'.
  Proof.
    unfold rep; intros.
    destruct st; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.would_recover_either_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
  Qed.
  
  Lemma rep_blockmem_subset : forall xp ms bm bm' hm,
    bm c= bm'
    -> forall st, rep xp st ms bm hm
        =p=> rep xp st ms bm' hm.
  Proof.
    unfold rep; intros.
    destruct ms; simpl in *.
    destruct st; cancel.
    all: try solve [erewrite MLog.rep_blockmem_subset; eauto;
    apply extract_blocks_map_subset_trans; eauto].   
    all: try solve [eapply handles_valid_nested_subset_trans; eauto].
    all: try solve [eapply handles_valid_map_subset_trans; eauto].
    all: try solve [erewrite extract_blocks_nested_subset_trans; eauto].
    erewrite extract_blocks_nested_subset_trans with (bm':= bm'); eauto.
    unfold MLog.would_recover_either.
    cancel.
    all: rewrite MLog.rep_blockmem_subset; eauto; cancel.
  Qed.


  (************* program *)

  Definition read xp a (ms : memstate) :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    match Map.find a vm with
    | Some v =>  Ret ^(ms, v)
    | None =>
        let^ (mm', v) <- MLog.read xp a mm;;
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
    Blockmem bm
    Hashmap hm
    Ghost [ F ds crash ]
    Loopvar [ mm ]
    Invariant
        exists nr,
        << F, MLog.rep: xp (MLog.Synced nr (nthd i ds)) mm bm hm >>
    OnCrash crash
    Begin
      (* r = false is impossible, flushall should always succeed *)
      let^ (mm, r) <- MLog.flush xp (selN ts (length ts - i - 1) nil) mm;;
      Ret ^(mm)
    Rof ^(mm);;
    Ret (mk_memstate hmap0 nil mm).

  Definition flushall xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (le_dec (Map.cardinal vm) (LogLen xp)) {
      let^ (mm, r) <- MLog.flush xp (Map.elements vm) mm;;
      Ret (mk_memstate hmap0 nil mm)
    } else {
      ms <- flushall_nomerge xp ms;;
      Ret ms
    }.

  Definition flushsync xp ms :=
    ms <- flushall xp ms;;
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.apply xp mm;;
    Ret (mk_memstate vm ts mm').

  Definition flushall_noop xp ms :=
    ms <- flushall xp ms;;
    Ret ms.

  Definition flushsync_noop xp ms :=
    ms <- flushsync xp ms;;
    Ret ms.

  Definition sync_cache xp ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.sync_cache xp mm;;
    Ret (mk_memstate vm ts mm').

  Definition dwrite' (xp : log_xparams) a v ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite xp a v mm;;
    Ret (mk_memstate vm ts mm').

  Definition dwrite (xp : log_xparams) a v ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (MapFacts.In_dec vm a) {
      ms <- flushall_noop xp ms;;
      ms <- dwrite' xp a v ms;;
      Ret ms
    } else {
      ms <- dwrite' xp a v ms;;
      Ret ms
    }.

  Definition dwrite_vecs' (xp : log_xparams) avs ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dwrite_vecs xp avs mm;;
    Ret (mk_memstate vm ts mm').

  Definition dwrite_vecs (xp : log_xparams) avs ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    If (bool_dec (overlap (map fst avs) vm) true) {
      ms <- flushall_noop xp ms;;
      ms <- dwrite_vecs' xp avs ms;;
      Ret ms
    } else {
      ms <- dwrite_vecs' xp avs ms;;
      Ret ms
    }.

  Definition dsync xp a ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync xp a mm;;
    Ret (mk_memstate vm ts mm').

  Definition dsync_vecs xp al ms :=
    let '(vm, ts, mm) := (MSVMap (fst ms), MSTxns (fst ms), MSLL ms) in
    mm' <- MLog.dsync_vecs xp al mm;;
    Ret (mk_memstate vm ts mm').

  Definition recover xp cs :=
    mm <- MLog.recover xp cs;;
    Ret (mk_memstate hmap0 nil mm).

  Definition init xp cs :=
    mm <- MLog.init xp cs;;
    Ret (mk_memstate hmap0 nil mm).


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


  Lemma diskset_vmap_find_none : forall ds ts vm bm a v vs xp F,
    dset_match xp ds (extract_blocks_nested bm ts) ->
    vmap_match vm ts ->
    Map.find a vm = None ->
    (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
    selN (fst ds) a valuset0 = (v, vs).
  Proof.
    unfold vmap_match, dset_match.
    intros ds ts; destruct ds; revert l.
    induction ts; intuition; simpl in *;
    denote ReplaySeq as Hs; inversion Hs; subst; simpl.
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
    inversion Hs.
    eapply map_find_replay_mem_not_in; eauto.
    subst.
    admit.
    denote Forall as Hx; apply Forall_inv in Hx; apply Hx.
    Unshelve.
    exact bmap0.
  Admitted.

  Lemma replay_seq_replay_mem : forall ds ts xp,
    ReplaySeq ds ts ->
    Forall (ents_valid xp (fst ds)) ts ->
    replay_disk (Map.elements (fold_right replay_mem bmap0 ts)) (fst ds) = latest ds.
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

  Lemma vmap_match_nil : vmap_match hmap0 nil.
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

  Lemma vmap_match_find : forall ts vmap,
    vmap_match vmap ts
    -> forall a v, KIn (a, v) (Map.elements vmap)
    -> Forall (@KNoDup handle) ts
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
    destruct (in_dec Nat_as_OT.eq_dec a0 (map fst (Map.elements (fold_right replay_mem hmap0 ts) ))).
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


  Lemma ents_valid_length_eq : forall T xp d d' ts,
    Forall (@ents_valid T xp d ) ts ->
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

(*  
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
 *)


  Lemma recover_before_any :
    forall xp ds ts bm hm,
    handles_valid_nested bm ts ->
    dset_match xp (effective ds (length ts)) (extract_blocks_nested bm ts) ->
    MLog.would_recover_before xp ds!! bm hm =p=>
    would_recover_any xp ds bm hm.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite <- latest_nthd.
    rewrite latest_effective.
    eassign (mk_mstate hmap0 ts hmap0); simpl.
    cancel.
    apply MLog.recover_before_either.
    intuition simpl; auto.    
    rewrite cuttail_length; omega.
  Qed.

  Lemma recover_before_any_fst : forall xp ds ts hm bm len,
    handles_valid_nested bm ts ->
    dset_match xp (effective ds (length ts)) (extract_blocks_nested bm ts) ->
    len = length ts ->
    MLog.would_recover_before xp (fst (effective ds len)) bm hm =p=>
    would_recover_any xp ds bm hm.
  Proof. 
    unfold would_recover_any, rep.
    intros; norm'r.
    rewrite nthd_0.
    eassign (mk_mstate hmap0 ts hmap0); simpl.
    rewrite MLog.recover_before_either.
    cancel.
    intuition simpl; auto.
    omega.
  Qed.

  Lemma synced_recover_any : forall xp ds nr ms ts bm hm,
    handles_valid_nested bm ts ->
    dset_match xp (effective ds (length ts)) (extract_blocks_nested bm ts) ->
    MLog.rep xp (MLog.Synced nr ds!!) ms bm hm =p=>
    would_recover_any xp ds bm hm.
  Proof.
    intros.
    rewrite MLog.synced_recover_before.
    eapply recover_before_any; eauto.
  Qed.

  Lemma recover_latest_any : forall xp ds bm hm ts,
    dset_match xp ds ts ->
    would_recover_any xp (ds!!, nil) bm hm =p=> would_recover_any xp ds bm hm.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    inversion H1.
    apply nelist_subset_latest.
  Qed.

  Lemma recover_latest_any_effective : forall xp ds bm hm ts,
    dset_match xp (effective ds (length ts)) ts ->
    would_recover_any xp (ds!!, nil) bm hm =p=> would_recover_any xp ds bm hm.
  Proof.
    unfold would_recover_any, rep.
    safecancel.
    inversion H1.
    apply nelist_subset_latest.
  Qed.

  Lemma cached_length_latest : forall F xp ds ms bm hm m,
    (F * rep xp (Cached ds) ms bm hm)%pred m ->
    length ds!! = length (fst (effective ds (length (MSTxns ms)))).
  Proof.
    unfold rep, dset_match; intuition.
    destruct_lift H.
    denote ReplaySeq as Hx.
    apply replay_seq_latest_length in Hx; simpl in Hx; rewrite <- Hx.
    rewrite latest_effective; auto.
  Qed.

  
    

  Lemma cached_latest_cached: forall xp ds ms bm hm,
    rep xp (Cached (ds!!, nil)) ms bm hm =p=> rep xp (Cached ds) ms bm hm.
  Proof.
    unfold rep; intros.
    norml; unfold stars; simpl.
    assert (MSTxns ms = nil) as Heq.
    apply dset_match_length in H2; simpl in H2.
    apply length_nil; auto.
    setoid_rewrite <- extract_blocks_nested_length; eauto.
    rewrite Heq; simpl in *.
    apply dset_match_length in H2; simpl in H2.
    cancel.
    rewrite nthd_0, Nat.sub_0_r; simpl.
    rewrite latest_nthd; cancel.
    unfold effective.
    rewrite Nat.sub_0_r; simpl.
    rewrite popn_oob; auto.
    apply dset_match_nil.
  Qed.


  (************* correctness theorems *)

  Definition init_ok :
    forall xp cs pr,
    {< F l d m,
    PERM: pr   
    PRE:bm, hm,  PermCacheDef.rep cs d bm*
          [[ (F * arrayS (DataStart xp) m * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             length m = (LogHeader xp) - (DataStart xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET: ms
          << F, rep: xp (Cached (m, nil)) ms bm' hm' >> 
    XCRASH:bm_crash, hm_crash, any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    step.
    step.
    rewrite nthd_0; simpl.
    rewrite MLog.rep_hashmap_subset; eauto.
    apply vmap_match_nil.
    unfold handles_valid_nested; apply Forall_nil.
    apply dset_match_nil.
    solve_hashmap_subset.
  Qed.


  Lemma dset_match_nthd_effective_fst : forall xp ds bm ts,
    dset_match xp (effective ds (length ts)) (extract_blocks_nested bm ts) ->
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

 

 
 
 Lemma handles_valid_nested_handles_valid_map:
   forall ts vm ds xp bm,
     dset_match xp ds (extract_blocks_nested bm ts) ->
     vmap_match vm ts ->
     handles_valid_nested bm ts ->
     handles_valid_map bm vm.
 Proof.
   unfold dset_match, vmap_match; induction ts; simpl in *; intuition.
   eapply handles_valid_map_equal; eauto.
   apply MapFacts.Equal_sym; eauto.
   apply MLog.handles_valid_map_hmap0.
   destruct b;
   inversion H3.
   
   inversion H1; inversion H2;
   clear H1 H2 H5; subst.
   eapply handles_valid_map_equal; eauto.
   apply MapFacts.Equal_sym; eauto.
   assert (A: handles_valid_map bm (fold_right replay_mem hmap0 ts)).
   eapply  IHts.
   split.
   2: eauto.
   all: eauto.
   apply MapFacts.Equal_refl.
   unfold ents_valid, log_valid in *; cleanup.
   apply extract_blocks_list_KNoDup in H; auto.
   apply MLog.handles_valid_replay_mem; eauto.
 Qed.


 Lemma extract_blocks_map_extract_blocks_nested:
   forall ts bm,
     handles_valid_nested bm ts ->
     Map.Equal (extract_blocks_map bm (fold_right replay_mem hmap0 ts))
               (fold_right replay_mem bmap0 (extract_blocks_nested bm ts)).
 Proof.
   induction ts; simpl; intros.
   apply MLog.extract_blocks_map_empty.
   inversion H; subst.
   unfold Map.Equal; intros.
   erewrite replay_mem_equal.
   2: apply MapFacts.Equal_sym; eauto.
   rewrite MLog.extract_blocks_map_replay_mem_comm; auto.
 Qed.
 
 Lemma diskset_vmap_find_ptsto :
   forall ds ts vm a w v vs F xp bm,
     dset_match xp ds (extract_blocks_nested bm ts) ->
     vmap_match vm ts ->
     Map.find a vm = Some w ->
     handles_valid_nested bm ts ->
     (F * a |-> (v, vs))%pred (list2nmem ds !!) ->
     bm w = Some v.
 Proof.
   intros.
   eapply handles_valid_nested_handles_valid_map in H as Hx; eauto.
   eapply map_find_extract_blocks_mem in H1 as Hy; eauto.
   eapply handles_valid_map_extract_some in Hx as Hz; eauto; cleanup.
   unfold extract_block in *; rewrite H4 in *.
   destruct H.
   apply list2nmem_ptsto_bound in H3 as Hl.
   erewrite <- replay_seq_replay_mem in H3; eauto.
   eapply list2nmem_sel in H3 as Hz.
   erewrite replay_disk_selN_MapsTo in Hz.
   inversion Hz; subst; eauto.
   apply Map.find_2.
   unfold vmap_match in *.
   erewrite MapFacts.find_m; eauto.
   eapply MapFacts.Equal_trans.
   apply MapFacts.Equal_sym; apply extract_blocks_map_extract_blocks_nested; eauto.
   apply extract_blocks_map_equal.
   apply MapFacts.Equal_sym; auto.
   erewrite <- replay_seq_latest_length; eauto.
   Unshelve.
   exact valuset0.
 Qed.


  

  Theorem read_ok:
    forall xp ms a pr,
    {< F ds vs,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[[ ds!! ::: exists F', (F' * a |-> vs) ]]]
    POST:bm', hm', RET:^(ms', r)
      << F, rep: xp (Cached ds) ms' bm' hm' >> *
      [[ bm' r = Some (fst vs) ]] * [[ readOnly ms ms' ]]
    CRASH:bm', hm',
      exists ms', << F, rep: xp (Cached ds) ms' bm' hm' >>
    >} read xp a ms.
  Proof.
    unfold read, rep.
    prestep.
    cancel.

    (* case 1 : return from vmap *)
    step.
    rewrite MLog.rep_hashmap_subset; eauto.
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
    step; subst.
    erewrite MLog.rep_hashmap_subset; eauto.
    clear H16; eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.

    erewrite <- latest_effective in H5; eauto.
    eapply diskset_vmap_find_none in H10 as Hx; eauto.
    erewrite dset_match_nthd_effective_fst in H15; eauto.
    setoid_rewrite Hx in H15.
    unfold extract_block in H15; simpl in *; auto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    eassign (mk_mstate (MSVMap ms_1) (MSTxns ms_1) ms'_1); cancel.
    all: simpl; auto.
    eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.
  Qed.



Lemma log_valid_extract_blocks_list:
  forall l d bm,
    handles_valid_list bm l ->
    log_valid l d ->
    log_valid (extract_blocks_list bm l) d.
Proof.
  unfold log_valid; induction l; simpl in *; intros.
  intuition.
  unfold extract_blocks_list; simpl; unfold KNoDup; auto.
  unfold extract_blocks_list in *; simpl in *; unfold KNoDup in *; auto.
  inversion H0.
  unfold extract_blocks_list in *; simpl in *; unfold KNoDup in *; auto.
  inversion H0.
  inversion H; cleanup; clear H.
  inversion H0; cleanup; clear H0.
  unfold handle_valid in *; cleanup.
  split.
  unfold extract_blocks_list; simpl; cleanup.
  constructor.
  intuition.
  destruct a; simpl in *.
  eapply InA_extract_blocks_list in H0; eauto.
  apply NoDupA_combine; auto.
  intros.
  apply KIn_extract_blocks_list in H0; cleanup; eauto.
  eapply Forall_cons; eauto.
  unfold handle_valid; eauto.
Qed.


Lemma log_valid_extract_blocks_list2:
  forall l d bm,
    handles_valid_list bm l ->
    log_valid (extract_blocks_list bm l) d ->
    log_valid l d.
Proof.
  unfold log_valid; induction l; simpl in *; intros.
  unfold extract_blocks_list in *; simpl in *; unfold KNoDup in *; auto.
  inversion H0.
  split.
  auto.
  intros a v Hx; inversion Hx.
  
  inversion H0; clear H0.
  destruct a.
  inversion H; cleanup; clear H.
  denote (handle_valid _ _ ) as Hx; unfold handle_valid in Hx; destruct Hx.
  setoid_rewrite extract_blocks_list_cons in H1; eauto.
  
  inversion H1; cleanup.
  split.
  constructor.
  intuition.
  eapply InA_extract_blocks_list2 in H0; eauto.
  eapply NoDupA_combine2; eauto.
  intros.
  eapply KIn_extract_blocks_list2 in H0; cleanup; eauto.
  eapply Forall_cons; eauto.
  unfold handle_valid; eauto.
  Unshelve.
  all: eauto.
Qed.


Lemma dset_match_log_valid_selN : forall ds ts i n bm xp,
    handles_valid_nested bm ts ->
    dset_match xp ds (extract_blocks_nested bm ts) ->
    log_valid (selN ts i nil) (nthd n ds).
  Proof.
    unfold dset_match, ents_valid; intuition; simpl in *.
    destruct (lt_dec i (length ts)).
    eapply log_valid_extract_blocks_list2.
    apply handles_valid_nested_selN; eauto.
    eapply Forall_selN with (i := i) in H1; intuition.
    erewrite extract_blocks_list_nested_selN_comm; auto.
    eapply log_valid_length_eq; eauto.
    erewrite replay_seq_nthd_length; eauto.
    setoid_rewrite extract_blocks_nested_length; auto.
    rewrite selN_oob by omega.
    unfold log_valid, KNoDup; intuition; inversion H0.
    Unshelve.
    exact nil.
  Qed.
  

  Theorem submit_ok:
    forall xp ents ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
        << F, rep: xp (Cached ds) ms bm hm >> *
        [[ handles_valid_list bm ents ]] *
        [[ log_valid ents ds!! ]]
    POST:bm', hm', RET:^(ms', r)
        ([[ r = false /\ length ents > LogLen xp ]] *
         << F, rep: xp (Cached ds) ms' bm' hm' >> *
        [[ ms' = ms ]])
     \/ ([[ r = true  ]] *
          << F, rep: xp (Cached (pushd (replay_disk (extract_blocks_list bm' ents) (latest ds)) ds)) ms' bm' hm' >>)
    CRASH:bm', hm',
      exists ms', << F, rep: xp (Cached ds) ms' bm' hm' >>
    >} submit xp ents ms.
  Proof.
    unfold submit, rep.
    step.
    step.
    step.
    or_r; cancel.
    rewrite nthd_pushd' by omega; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.

    unfold vmap_match in *; simpl.
    denote! (Map.Equal _ _) as Heq.
    rewrite Heq; apply MapFacts.Equal_refl.
    constructor; eauto.

    rewrite effective_pushd_comm.
    erewrite <- latest_effective.
    apply dset_match_ext; auto.
    rewrite latest_effective; auto.
    eapply log_valid_extract_blocks_list; eauto.   
    setoid_rewrite extract_blocks_list_length; eauto.
    
    step.
    step.
    or_l; cancel.
    apply Nat.nle_gt; auto.
    rewrite MLog.rep_hashmap_subset; eauto.
    Unshelve. all: try exact bmap0; eauto.
  Qed.



  Local Hint Resolve vmap_match_nil dset_match_nil.
  Opaque MLog.flush.


  Theorem flushall_nomerge_ok:
    forall xp ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' bm' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = hmap0 ]]
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} flushall_nomerge xp ms.
  Proof.
    unfold flushall_nomerge, would_recover_any, rep.
    prestep.
    cancel.

    rewrite nthd_effective, Nat.add_0_r.
    apply sep_star_comm.
    eauto.

    - safestep.
      apply handles_valid_nested_selN; eauto.
      eapply handles_valid_nested_subset_trans; eauto.
      erewrite <- Nat.sub_add_distr.
      apply Nat.sub_lt.
      rewrite Nat.add_1_r; apply lt_le_S; auto.
      omega.
      eapply dset_match_log_valid_selN; eauto.
      safestep.
      safestep.

      (* flush() returns true *)
      erewrite extract_blocks_list_nested_selN_comm.
      setoid_rewrite <- extract_blocks_nested_length with (ts:= (MSTxns ms_1)).
      erewrite dset_match_nthd_S.
      repeat rewrite extract_blocks_nested_length.
      erewrite MLog.rep_hashmap_subset; eauto.
      rewrite extract_blocks_nested_length; eauto.
      erewrite extract_blocks_nested_subset_trans; eauto.
      setoid_rewrite extract_blocks_nested_length; auto.
      erewrite <- Nat.sub_add_distr.
      apply Nat.sub_lt.
      rewrite Nat.add_1_r; apply lt_le_S; auto.
      omega.
      solve_hashmap_subset.
      solve_blockmem_subset.

      cancel.

      
      (* flush() returns false, this is impossible *)
      exfalso; eapply dset_match_ent_length_exfalso; eauto.
      setoid_rewrite <- extract_blocks_list_nested_selN_comm.
      setoid_rewrite extract_blocks_list_length; eauto.
      eapply handles_valid_nested_selN; eauto.
      erewrite <- Nat.sub_add_distr.
      apply Nat.sub_lt.
      rewrite Nat.add_1_r; apply lt_le_S; auto.
      omega.
      erewrite <- Nat.sub_add_distr.
      apply Nat.sub_lt.
      rewrite Nat.add_1_r; apply lt_le_S; auto.
      omega.

      cancel.

      (* crashes *)
      norml.
      rewrite <- H1; cancel.
      solve_hashmap_subset.
      solve_blockmem_subset.
      subst; repeat xcrash_rewrite.
      xform_norm; cancel.
      xform_normr. safecancel.
      eassign (mk_mstate hmap0 (MSTxns ms_1) hmap0); simpl.
      rewrite selR_inb. cancel.
      rewrite extract_blocks_nested_length.
      setoid_rewrite <- extract_blocks_list_nested_selN_comm; eauto.
      erewrite <- Nat.sub_add_distr.
      apply Nat.sub_lt.
      rewrite Nat.add_1_r; apply lt_le_S; auto.
      omega.
      rewrite extract_blocks_nested_length; auto.
      all: simpl; auto.
      eapply handles_valid_nested_subset_trans; [|eauto].
      eauto.
      erewrite extract_blocks_nested_subset_trans; eauto.
      omega.

    - safestep.
      safestep.
      rewrite nthd_oob, latest_effective, nthd_0.
      simpl.
      rewrite MLog.rep_hashmap_subset; eauto.
      erewrite <- dset_match_length; eauto.
      setoid_rewrite extract_blocks_nested_length; auto.
      apply handles_valid_nested_empty.
      apply dset_match_nil.
      solve_hashmap_subset.
      cancel.

    - eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)); unfold false_pred; cancel.
      Unshelve.
      all: eauto; try solve constructor.
      exact tt.
      all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (flushall_nomerge _ _) _) => apply flushall_nomerge_ok : prog.

  Opaque flushall_nomerge.


  Lemma dset_match_log_valid_grouped : forall ts vmap ds bm xp,
    vmap_match vmap ts
    -> dset_match xp ds (extract_blocks_nested bm ts)
    -> handles_valid_nested bm ts
    -> log_valid (Map.elements vmap) (fst ds).
  Proof.
    intros.

    assert (HNoDup: Forall (@KNoDup handle) ts).
      unfold dset_match in *; simpl in *; intuition.
      unfold handles_valid_nested, ents_valid, log_valid in *.
      rewrite Forall_forall; intros.
      eapply extract_blocks_list_KNoDup; eauto.
      rewrite Forall_forall in *; auto.
      eapply extract_blocks_nested_in in H0; eauto.
      rewrite Forall_forall in *.
      edestruct H2; eauto.
      intuition.
      unfold log_valid; intuition;
      eapply vmap_match_find in H; eauto.
      deex.
      denote In as HIn.
      unfold dset_match in *; intuition.
      rewrite Forall_forall in H.
      eapply extract_blocks_nested_in in H4 as Hx; eauto.
      eapply H in Hx.

      unfold ents_valid, log_valid in *; intuition.
      replace 0 with (fst (0, v)) in * by auto.
      apply In_fst_KIn in HIn.
      eapply KIn_extract_blocks_list2 in HIn; eauto.
      cleanup.
      edestruct H7; eauto.
      unfold handles_valid_nested in *.
      rewrite Forall_forall in H1; eauto.
      
      deex.
      denote In as HIn.
      unfold dset_match in *; intuition.
      rewrite Forall_forall in H.
      eapply extract_blocks_nested_in in H3 as Hx; eauto.
      eapply H in Hx.

      unfold ents_valid, log_valid in *; intuition.
      replace a with (fst (a, v)) in * by auto.
      apply In_fst_KIn in HIn.
      eapply KIn_extract_blocks_list2 in HIn; eauto.
      cleanup.
      edestruct H7; eauto.
      unfold handles_valid_nested in *.
      rewrite Forall_forall in H1; eauto.
  Qed.


  (* Map proofs are very hard and time consuming. There must be an easier way to do them *)
  Lemma dset_match_replay_disk_grouped : forall ts vmap bm ds xp,
    vmap_match vmap ts
    -> dset_match xp ds (extract_blocks_nested bm ts)
    -> handles_valid_nested bm ts
    -> replay_disk  (extract_blocks_list bm (Map.elements vmap)) (fst ds) = nthd (length ts) ds.
  Proof. Admitted.
    (*
    intros; simpl in *.
    denote dset_match as Hdset.
    apply dset_match_length in Hdset as Hlength.
    unfold dset_match in *.
    intuition.

    unfold vmap_match in *.
    rewrite H.

    Search (Map.elements (fold_right _ _ _)).

    
    Search replay_disk.

    Lemma asd:
      forall ts ds xp bm,
        handles_valid_nested bm ts ->
        Forall (ents_valid xp (fst ds)) (extract_blocks_nested bm ts) ->
        ReplaySeq ds (extract_blocks_nested bm ts) ->
        replay_disk (extract_blocks_list bm (Map.elements (fold_right replay_mem hmap0 ts))) (fst ds) =
       replay_disk (Map.elements (fold_right replay_mem bmap0 (extract_blocks_nested bm ts))) (fst ds).
    Proof.
      induction 1; simpl in *; intuition eauto.
      inversion H1; cleanup; clear H1.
   
      Search (Map.elements (replay_mem _ _)).
      rewrite <- replay_disk_replay_mem.
      rewrite <- IHForall.
      Search (replay_disk _ (replay_disk _ _)).
      rewrite replay_disk_merge'.

      Lemma qwe:
        forall l x bm,
          
          extract_blocks_list bm (Map.elements (replay_mem x (fold_right replay_mem hmap0 l))) =
          Map.elements (replay_mem (extract_blocks_list bm x)
                       (replay_mem (extract_blocks_list bm (Map.elements (fold_right replay_mem hmap0 l))) bmap0)).

      Proof.
        induction l; simpl in *; intuition.
        Search extract_blocks_list replay_mem.

        Lemma rty:
          forall x hmap bmap bm,
            handles_valid_map bm hmap ->
            handles_valid_list bm x ->
            Map.Equal (extract_blocks_map bm hmap) bmap ->
            extract_blocks_list bm (Map.elements (replay_mem x hmap)) =
            Map.elements (replay_mem (extract_blocks_list bm x) bmap).
        Proof.
          induction x; simpl in *; intuition eauto.
          erewrite <- mapeq_elements with (m2:= bmap); eauto.

          Lemma extract_blocks_list_elements:
            forall hmap bm,
              handles_valid_map bm hmap ->
              extract_blocks_list bm (Map.elements hmap) = Map.elements (extract_blocks_map bm hmap).
          Proof.
            unfold extract_blocks_map, extract_blocks_list, handles_valid_map,
            Map.elements, AddrMap_AVL.Raw.elements, handles_valid_list;
            intro hmap; destruct hmap; generalize dependent this;
            induction this; simpl in *; intros; eauto.
            repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *;
            repeat rewrite map_app in *; simpl in *; repeat rewrite app_nil_r in *.
            
            rewrite extract_blocks_app; simpl.
            apply  handles_valid_app in H.
            destruct H.
            inversion H0; subst.
            rewrite combine_app.           
            unfold handle_valid in *; cleanup.
            unfold extract_block at 2; simpl in *; cleanup.
            inversion is_bst; cleanup.
            rewrite IHthis1, IHthis2; auto.
            rewrite extract_blocks_length; eauto.
            repeat rewrite map_length; eauto.
          Qed.

          apply extract_blocks_list_elements; auto.

          inversion H0; subst; unfold handle_valid in *; cleanup.
          erewrite extract_blocks_list_cons; eauto; simpl.
          apply IHx.


          Lemma handles_valid_map_add:
            forall m a b v bm,
              bm b = Some v ->
              handles_valid_map bm m ->
              handles_valid_map bm (Map.add a b m).
          Proof.
            unfold handles_valid_map, Map.elements, AddrMap_AVL.Raw.elements, handles_valid_list;
            intro hmap; destruct hmap; generalize dependent this;
            induction this; simpl in *; intros; eauto.
            unfold handles_valid; simpl.
            rewrite Forall_forall; intros.
            unfold handle_valid; inversion H1; subst; eauto.
            inversion H2.

            repeat rewrite AddrMap_AVL.Raw.Proofs.elements_app in *;
            repeat rewrite map_app in *; simpl in *; repeat rewrite app_nil_r in *.
            apply  handles_valid_app in H0.
            destruct H0.
            inversion H1; subst.

            destruct (Nat_as_OT.compare a k) eqn:D; simpl.
            eapply AddrMap_AVL.Raw.Proofs.R_add_1 in D.
            Search AddrMap_AVL.Raw.bal.
            Search AddrMap_AVL.Raw.add.
            unfold AddrMap_AVL.Raw.elements; simpl
            apply MapProperties.elements_Empty in HI.
            Search Map.add.
            Search Map.elements nil.
            
            
          

          
            inversion H; subst.
            induction hmap; simpl in *; eauto.
          
          unfold extract_blocks_map.
          
          Search Map.elements Map.map.
          destruct a; erewrite extract_blocks_list_cons.
          simpl.

        
      Search (replay_mem _ (replay_mem  _ _)).
      unfold extract_blocks_nested.
      Search fold_right.
    
    erewrite replay_seq_replay_mem; eauto.
    erewrite nthd_oob; eauto.
    omega.
    Qed.
     *)

Lemma dset_match_grouped : forall ts vmap ds bm xp,
    length (snd ds) > 0
    -> Map.cardinal vmap <= LogLen xp
    -> vmap_match vmap ts
    -> dset_match xp ds (extract_blocks_nested bm ts)
    -> handles_valid_list bm (Map.elements vmap)
    -> handles_valid_nested bm ts
    -> dset_match xp (fst ds, [ds !!]) [extract_blocks_list bm (Map.elements vmap)].
  Proof.
    intros.
    unfold dset_match; intuition simpl.
    unfold ents_valid.
    apply Forall_forall; intros.
    inversion H5; subst; clear H5.
    split.
    eapply log_valid_extract_blocks_list; auto.
    eapply dset_match_log_valid_grouped; eauto.
    setoid_rewrite extract_blocks_list_length; auto.
    setoid_rewrite <- Map.cardinal_1; eauto.

    inversion H6.

    econstructor.
    simpl.
    (* depends on the previous admitted lemma *) 
    erewrite dset_match_replay_disk_grouped; eauto.
    
    eapply dset_match_length in H2; eauto.
    rewrite nthd_oob; auto.
    rewrite <- H2.
    setoid_rewrite extract_blocks_nested_length; eauto.
    constructor.
  Qed.



  

  Theorem flushall_ok:
    forall xp ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' bm' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = hmap0 ]]
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} flushall xp ms.
  Proof.
    unfold flushall.
    safestep.

    prestep; denote rep as Hx; unfold rep in Hx; destruct_lift Hx.
    cancel.
    eapply handles_valid_nested_handles_valid_map; eauto. 
    erewrite dset_match_nthd_effective_fst; eauto.
    eapply dset_match_log_valid_grouped; eauto.

    prestep; unfold rep; safecancel.
    prestep; unfold rep; safecancel.    
    
    erewrite dset_match_nthd_effective_fst; eauto.  
    erewrite dset_match_replay_disk_grouped; eauto.
    erewrite nthd_oob; eauto.
    rewrite latest_effective, nthd_0; simpl; eauto.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite <- dset_match_length; eauto.
    setoid_rewrite extract_blocks_nested_length; auto.
    clear H15; erewrite extract_blocks_nested_subset_trans; eauto.
    clear H15; eapply handles_valid_nested_subset_trans; eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
    solve_hashmap_subset.
    cancel.

    denote (length _ > _) as Hf; contradict Hf.
    setoid_rewrite <- Map.cardinal_1; omega.
    cancel.

    apply sep_star_lift_l; intros.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    erewrite dset_match_nthd_effective_fst; eauto.
    unfold would_recover_any, rep.
    destruct (MSTxns ms_1);
    norm; unfold stars; simpl.

    unfold vmap_match in *; simpl in *.
    denote (Map.Equal _ hmap0) as Heq.
    rewrite Heq.
    replace (Map.elements _) with (@nil (Map.key * handle)) by auto.
    rewrite nthd_effective.
    eassign (mk_mstate hmap0 nil (MSMLog ms_1)); simpl.
    rewrite Nat.add_0_r, selR_oob by auto.
    cancel.
    intuition.
    simpl.
    apply handles_valid_nested_empty.

    eassign (fst (effective ds (S (length l))), latest ds :: nil).
    eassign (mk_mstate hmap0 (Map.elements (MSVMap ms_1) :: nil) (MSMLog ms_1)); simpl.
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
    simpl.
    unfold handles_valid_nested; rewrite Forall_forall; intros.
    inversion H11; subst.
    eapply handles_valid_list_subset_trans; eauto.
    eapply handles_valid_nested_handles_valid_map; eauto.
    unfold extract_blocks_nested; simpl; eauto.
    inversion H12.

    simpl.
    unfold effective; simpl; rewrite popn_0. 
    replace (S (length l)) with (length (i :: l)) by auto.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite <- latest_effective; eauto.
    
    eapply dset_match_grouped; eauto; simpl.
    rewrite cuttail_length; omega.
    erewrite <- extract_blocks_list_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    inversion H9; auto.
    inversion H9; auto.
    eapply handles_valid_list_subset_trans; eauto.
    eapply handles_valid_nested_handles_valid_map; eauto.
    simpl; eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    simpl; eauto.    

    safestep.
    repeat match goal with
              | [ H := ?e |- _ ] => subst H
            end; cancel.
    step.
    safestep.
    repeat match goal with
           | [ H := ?e |- _ ] => subst H
           end; cancel.
    erewrite rep_hashmap_subset; eauto.
    solve_hashmap_subset.

    Unshelve. all: try exact nil; eauto; try exact hmap0.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (init _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (submit _ _ _) _) => apply submit_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (flushall _ _) _) => apply flushall_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.

  Theorem flushall_noop_ok:
    forall xp ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached ds) ms' bm' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = hmap0 ]]
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} flushall_noop xp ms.
  Proof.
    unfold flushall_noop; intros.
    safestep.
    step.
    step.
    erewrite rep_hashmap_subset.
    apply cached_latest_cached.
    solve_hashmap_subset.
    solve_hashmap_subset.
  Qed.

  Theorem flushsync_ok:
    forall xp ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (ds!!, nil)) ms' bm' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = hmap0 ]]
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} flushsync xp ms.
  Proof.
    unfold flushsync.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    prestep; unfold rep; cancel.
    eapply MLog.rep_hashmap_subset;eauto.
    clear H20.
    eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.
    solve_blockmem_subset.

    cancel.
    norml.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    xcrash.
    denote rep as Hx; unfold rep in Hx.
    destruct_lift Hx.
    eapply recover_before_any; eauto.
    2: erewrite extract_blocks_nested_subset_trans; eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (flushsync _ _) _) => apply flushsync_ok : prog.

  Theorem flushsync_noop_ok:
    forall xp ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached ds) ms' bm' hm' >> *
      [[ MSTxns (fst ms') = nil /\ MSVMap (fst ms') = hmap0 ]]
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} flushsync_noop xp ms.
  Proof.
    unfold flushsync_noop.
    safestep.
    step.
    step.
    erewrite rep_hashmap_subset.
    apply cached_latest_cached.
    solve_hashmap_subset.
    solve_hashmap_subset.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (flushall_noop _ _) _) => apply flushall_noop_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (flushsync_noop _ _) _) => apply flushsync_noop_ok : prog.

  Lemma forall_ents_valid_length_eq : forall T xp d d' ts,
    Forall (@ents_valid T xp d) ts ->
    length d' = length d ->
    Forall (ents_valid xp d') ts.
  Proof.
    unfold ents_valid; intros.
    rewrite Forall_forall in *.
    intros.
    specialize (H _ H1); intuition.
    eapply log_valid_length_eq; eauto.
  Qed.

  Lemma forall_ents_valid_ents_filter : forall T ts xp d f,
    Forall (@ents_valid T xp d) ts ->
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

 (* 
  Lemma cached_dsupd_latest_recover_any : forall xp ds a v ms hm ms0 bm,
    handles_valid_nested bm ms0 ->
    dset_match xp (effective ds (length ms0)) (extract_blocks_nested bm ms0) ->
    rep xp (Cached ((dsupd ds a v) !!, nil)) ms bm hm =p=>
    would_recover_any xp (dsupd ds a v) bm hm.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    rewrite synced_recover_any; auto.
    apply H.
    rewrite effective_dsupd_comm.
    eapply dset_match_dsupd; eauto.
  Qed.
   *)
  
  Lemma cached_dssync_vecs_latest_recover_any : forall xp ds al ms hm bm ms0,
    handles_valid_nested bm ms0 ->
    dset_match xp (effective ds (length ms0)) (extract_blocks_nested bm ms0) ->
    rep xp (Cached ((dssync_vecs ds al) !!, nil)) ms bm hm =p=>
    would_recover_any xp (dssync_vecs ds al) bm hm.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    unfold would_recover_any, rep.
    rewrite synced_recover_any; auto.
    apply H.
    rewrite effective_dssync_vecs_comm.
    eapply dset_match_dssync_vecs; eauto.
  Qed.

  Lemma cached_latest_recover_any : forall xp ds ms hm ms0 bm,
    handles_valid_nested bm ms0 ->
    dset_match xp (effective ds (length ms0)) (extract_blocks_nested bm ms0) ->
    rep xp (Cached (ds !!, nil)) ms bm hm =p=>
    would_recover_any xp ds bm hm.
  Proof.
    unfold rep; cancel.
    rewrite nthd_0; simpl.
    unfold would_recover_any, rep.
    rewrite synced_recover_any; auto.
    apply H.
    eauto.
  Qed.

  Lemma vmap_match_notin : forall ts vm a bm,
    Map.find a vm = None ->
    vmap_match vm ts ->
    handles_valid_nested bm ts ->
    Forall (fun e => ~ In a (map fst e)) (extract_blocks_nested bm ts).
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    simpl.
    constructor; simpl in *.
    unfold extract_blocks_list.
    rewrite map_fst_combine.
    eapply map_find_replay_mem_not_in.
    rewrite <- H0; auto.
    rewrite extract_blocks_length; eauto.
    repeat rewrite map_length; eauto.
    inversion H1; auto.
    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_find_none_mono.
    rewrite <- H0; auto.
    inversion H1; eauto.
  Qed.
  Lemma dset_match_dsupd_notin : forall xp ds a v ts bm vm,
    Map.find a vm = None ->
    vmap_match vm ts ->
    dset_match xp ds (extract_blocks_nested bm ts) ->
    handles_valid_nested bm ts ->
    dset_match xp (dsupd ds a v) (extract_blocks_nested bm ts).
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply length_updN.
    apply replay_seq_dsupd_notin; auto.
    eapply vmap_match_notin; eauto.
  Qed.


  Theorem dwrite'_ok:
    forall xp a h ms pr,
    {< F Fd ds v vs,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ Map.find a (MSVMap (fst ms)) = None ]] *
      [[[ fst (effective ds (length (MSTxns (fst ms)))) ::: (Fd * a |-> vs) ]]] *
      [[ bm h = Some v ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists ds',
      << F, rep: xp (Cached ds') ms' bm' hm' >> *
      [[  ds' = dsupd ds a (v, vsmerge vs) ]]
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
      \/ exists ms' d',
      << F, rep: xp (Cached (d', nil)) ms' bm' hm' >> *
      [[  d' = updN (fst (effective ds (length (MSTxns (fst ms))))) a (v, vsmerge vs) ]] *
      [[[ d' ::: (Fd * a |-> (v, vsmerge vs)) ]]]
    >} dwrite' xp a h ms.
  Proof.
    unfold dwrite', rep.
    step.
    erewrite dset_match_nthd_effective_fst; eauto.
    safestep.
    safestep.
    4: eauto.

    erewrite dset_match_nthd_effective_fst; eauto; simpl.
    erewrite map_length; eauto.
    rewrite dsupd_nthd.
    erewrite MLog.rep_hashmap_subset; eauto.
    clear H18; eapply handles_valid_nested_subset_trans; eauto.

    rewrite effective_dsupd_comm.
    erewrite extract_blocks_nested_subset_trans.
    eapply dset_match_dsupd_notin; eauto.
    eauto.
    auto.
    solve_hashmap_subset.
    
    (* crashes *)
    cancel.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    subst; repeat xcrash_rewrite.
    xform_norm.
    or_l; cancel.
    xform_normr; cancel.
    erewrite dset_match_nthd_effective_fst; eauto.
    rewrite recover_before_any_fst. cancel.
    eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    auto.

    or_r; cancel.
    xform_normr; cancel.
    xform_normr; cancel.
    rewrite nthd_0; simpl.
    eassign (mk_mstate hmap0 nil x_1); simpl; cancel.
    all: simpl; eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (dwrite' _ _ _ _) _) => apply dwrite'_ok : prog.

  Lemma diskset_ptsto_bound_effective : forall F xp a vs ds ts bm,
    dset_match xp (effective ds (length ts)) (extract_blocks_nested bm ts) ->
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


  Theorem dwrite_ok:
    forall xp a h ms pr,
    {< F Fd ds v vs,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ bm h = Some v ]] *             
      [[[ ds !! ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (dsupd ds a (v, vsmerge vs))) ms' bm' hm' >>
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >> \/
      << F, would_recover_any: xp (dsupd ds a (v, vsmerge vs)) bm' hm' -- >>
    >} dwrite xp a h ms.
  Proof.
    unfold dwrite, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; safecancel.
    substl (MSVMap a0); eauto.
    substl (MSTxns a0); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    simpl; pred_apply; cancel.
    eauto.
    auto.

    step.
    step.
    erewrite MLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
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

    (* This goeal doesn't match with the lemma it used to solve.
    rewrite effective_dsupd_comm.

    rewrite H20 in H27; simpl in H27.
    rewrite Nat.sub_0_r, <- latest_nthd in H27.
    rewrite <- dsupd_latest in H27.
    unfold effective in H27.
    simpl in *.
    rewrite popn_0 in H27.


    LEFTHERE.
    
    eapply dset_match_dsupd; eauto.
     *) admit.

    
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    (* 2nd case: no flushall *)
    prestep; unfold rep; cancel.
    apply MapFacts.not_find_in_iff; auto.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_effective; eauto.
    eauto.

    step.
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    repeat rewrite map_length.
    rewrite <- surjective_pairing in *.
    erewrite dset_match_nthd_effective_fst; eauto.
    erewrite diskset_vmap_find_none; eauto; auto.
    cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    erewrite <- diskset_vmap_find_none with (v := vs_cur).
    erewrite <- dset_match_nthd_effective_fst; eauto.
    all: eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.
    apply MapFacts.not_find_in_iff; auto.
    rewrite latest_effective; eauto.
    solve_hashmap_subset.

    norml.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
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
    3: eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    rewrite effective_dsupd_comm.
    (* Same as above 
    eapply dset_match_dsupd; eauto.
     *) admit.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Admitted.


  Theorem dsync_ok:
    forall xp a ms pr,
    {< F Fd ds vs,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[[ ds !! ::: (Fd * a |-> vs) ]]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (dssync ds a)) ms' bm' hm' >>
    CRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} dsync xp a ms.
  Proof.
    unfold dsync.
    prestep; unfold rep; cancel.
    eapply list2nmem_ptsto_cancel_pair.
    eapply diskset_ptsto_bound_effective; eauto.

    step.
    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dssync_nthd; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    clear H15; eapply handles_valid_nested_subset_trans; eauto.
    rewrite effective_dssync_comm.
    eapply dset_match_dssync; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.
    
    rewrite <- H1; cancel.
    rewrite MLog.synced_recover_before.
    erewrite dset_match_nthd_effective_fst; eauto.
    rewrite recover_before_any_fst; eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.
    Unshelve. eauto.
  Qed.


  Lemma vmap_match_nonoverlap : forall ts vm al bm,
    overlap al vm = false ->
    vmap_match vm ts ->
    Forall (fun e => disjoint al (map fst e)) (extract_blocks_nested bm ts).
  Proof.
    unfold vmap_match; induction ts; intros.
    apply Forall_nil.
    rewrite H0 in H; simpl in *.
    constructor; simpl in *.
    eapply nonoverlap_replay_mem_disjoint; eauto.
    Search replay_mem extract_blocks_list.
    
    admit.
    
    eapply IHts.
    2: apply MapFacts.Equal_refl.
    eapply replay_mem_nonoverlap_mono; eauto.
    Unshelve. exact bmap0.
  Admitted.



 
  Lemma dset_match_dsupd_vecs_nonoverlap : 
    forall xp avl vm ds ts bm,
    handles_valid_nested bm ts ->
    handles_valid_list bm avl ->
    overlap (map fst avl) vm = false ->
    vmap_match vm ts ->
    dset_match xp ds (extract_blocks_nested bm ts) ->
    dset_match xp (dsupd_vecs ds (extract_blocks_list bm avl)) (extract_blocks_nested bm ts).
  Proof.
    unfold dset_match; intuition; simpl in *.
    eapply forall_ents_valid_length_eq; try eassumption.
    apply vsupd_vecs_length.
    apply replay_seq_dsupd_vecs_disjoint; auto.
    eapply vmap_match_nonoverlap; eauto.
    rewrite extract_blocks_list_map_fst; auto.
  Qed.

  
  Theorem dwrite_vecs'_ok:
    forall xp avl ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ overlap (map fst avl) (MSVMap (fst ms)) = false ]] *
      [[ handles_valid_list bm avl ]] *           
      [[ Forall (fun e => fst e < length (fst (effective ds (length (MSTxns (fst ms)))))) avl 
         /\ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds (extract_blocks_list bm' avl))) ms' bm' hm' >>
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >> \/
      exists ms',
        << F, rep: xp (Cached (vsupd_vecs (fst (effective ds (length (MSTxns (fst ms)))))
                                          (extract_blocks_list bm' avl), nil)) ms' bm' hm' >>
    >} dwrite_vecs' xp avl ms.
  Proof.
    unfold dwrite_vecs'.
    prestep; unfold rep; cancel.
    step.
    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dsupd_vecs_nthd; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    clear H17; eapply handles_valid_nested_subset_trans; eauto.
    rewrite effective_dsupd_vecs_comm.
    eapply dset_match_dsupd_vecs_nonoverlap; eauto.
    clear H17; eapply handles_valid_nested_subset_trans; eauto.
    clear H17; eapply handles_valid_list_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.

    norml.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash.
    or_l; xform_norm; cancel.
    xform_normr; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite recover_before_any_fst. cancel.
    3:eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.

    or_r; xform_norm; cancel.
    xform_normr; cancel.
    rewrite nthd_0.
    repeat erewrite dset_match_nthd_effective_fst by eauto.
    eassign (mk_mstate hmap0 nil x0_1); simpl; cancel.
    all: simpl; eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (dwrite_vecs' _ _ _) _) => apply dwrite_vecs'_ok : prog.

  
  Lemma effective_avl_addrs_ok : forall (avl : list (addr * handle)) ds ts xp bm,
    Forall (fun e => fst e < length (ds !!)) avl ->
    dset_match xp (effective ds (length ts)) ( extract_blocks_nested bm ts) ->
    Forall (fun e => fst e < length (nthd (length (snd ds) - length ts) ds)) avl.
  Proof.
    intros.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    rewrite latest_effective; eauto.
    unfold dset_match in *; intuition eauto.
  Qed.

  Theorem dwrite_vecs_ok:
    forall xp avl ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ handles_valid_list bm avl ]] *             
      [[ Forall (fun e => fst e < length (ds!!)) avl /\ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (dsupd_vecs ds (extract_blocks_list bm' avl))) ms' bm' hm' >>
    XCRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >> \/
      << F, would_recover_any: xp (dsupd_vecs ds (extract_blocks_list bm' avl)) bm' hm' -- >>
    >} dwrite_vecs xp avl ms.
  Proof.
    unfold dwrite_vecs, rep.
    step.
    prestep; unfold rep; cancel.
    prestep; unfold rep; safecancel.
    substl (MSVMap a).
    apply overlap_empty; apply map_empty_hmap0.
    eapply handles_valid_list_subset_trans; eauto.
    eapply effective_avl_addrs_ok; eauto.
    auto.

    step.
    step.
    erewrite MLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    repeat xcrash_rewrite; xform_norm.

    or_l; cancel.
    xform_normr; cancel.

    or_r; cancel.
    do 2 (xform_norm; cancel).
    repeat rewrite nthd_0; simpl.
    substl (MSTxns a); simpl.
    rewrite Nat.sub_0_r, <- latest_nthd.
    rewrite <- dsupd_vecs_latest.
    rewrite synced_recover_any; auto.
    eassign (MSTxns a); substl (MSTxns a); simpl.
    apply handles_valid_nested_empty.
    substl (MSTxns a); simpl.
    unfold effective; rewrite popn_oob.
    apply dset_match_nil.
    omega.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    repeat xcrash_rewrite; xform_norm.
    or_l; cancel.
    xform_normr; cancel.

    prestep; unfold rep; cancel.
    apply not_true_iff_false; auto.
    eapply effective_avl_addrs_ok; eauto.

    step.
    step.
    erewrite MLog.rep_hashmap_subset; eauto.
    solve_hashmap_subset.

    norml.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
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
    eapply handles_valid_nested_subset_trans.
    2: apply H12.
    solve_blockmem_subset.
    
    rewrite effective_dsupd_vecs_comm.
    erewrite <- extract_blocks_list_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    eapply dset_match_dsupd_vecs_nonoverlap.
    3: apply not_true_is_false; eauto.
    all: eauto.

    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem dsync_vecs_ok:
    forall xp al ms pr,
    {< F ds,
    PERM:pr   
    PRE:bm, hm,
      << F, rep: xp (Cached ds) ms bm hm >> *
      [[ Forall (fun e => e < length (ds!!)) al /\ sync_invariant F ]]
    POST:bm', hm', RET:ms'
      << F, rep: xp (Cached (dssync_vecs ds al)) ms' bm' hm' >>
    CRASH:bm', hm',
      << F, would_recover_any: xp ds bm' hm' -- >>
    >} dsync_vecs xp al ms.
  Proof.
    unfold dsync_vecs.
    prestep; unfold rep; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite Forall_forall in *; intros.
    erewrite <- replay_seq_latest_length; eauto.
    rewrite latest_effective; eauto.
    unfold dset_match in *; intuition eauto.

    step.
    prestep; unfold rep; cancel.
    rewrite map_length.
    rewrite dssync_vecs_nthd; cancel.
    erewrite MLog.rep_hashmap_subset; eauto.
    clear H15; eapply handles_valid_nested_subset_trans; eauto.
    rewrite effective_dssync_vecs_comm.
    eapply dset_match_dssync_vecs; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    erewrite dset_match_nthd_effective_fst by eauto.
    rewrite MLog.synced_recover_before.
    rewrite recover_before_any_fst; eauto.
    eapply handles_valid_nested_subset_trans; eauto.
    erewrite extract_blocks_nested_subset_trans; eauto.
    solve_hashmap_subset.
  Qed.

  Definition recover_any_pred xp ds bm hm :=
    ( exists d n ms, [[ n <= length (snd ds) ]] *
      (rep xp (Cached (d, nil)) ms bm hm \/
        rep xp (Rollback d) ms bm hm) *
      [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]])%pred.

  Theorem sync_invariant_recover_any_pred : forall xp ds bm hm,
    sync_invariant (recover_any_pred xp ds bm hm).
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

  (*
  Theorem crash_xform_any : forall xp ds bm hm,
    crash_xform (would_recover_any xp ds bm hm) =p=>
                 recover_any_pred  xp ds bm hm.
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

*)
  Lemma crash_xform_recovering : forall xp d mm bm hm,
    crash_xform (rep xp (Recovering d) mm bm hm) =p=>
                 recover_any_pred xp (d, nil) bm hm.
  Proof.
    unfold recover_any_pred, rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_recovering.
    instantiate (1:=nil).
    unfold MLog.recover_either_pred.
    norm.
    unfold stars; simpl.
    or_l; cancel.
    eassign (mk_mstate hmap0 nil ms'); cancel.
    auto.
    simpl; apply handles_valid_nested_empty.
    apply dset_match_nil.
    intuition simpl; eauto.
    or_l; cancel.
    eassign (mk_mstate hmap0 nil ms'); cancel.
    auto.
    simpl; apply handles_valid_nested_empty.
    apply dset_match_nil.
    intuition simpl; eauto.
    or_r; cancel.
    eassign (mk_mstate hmap0 nil ms'); cancel.
    auto.
    simpl; apply handles_valid_nested_empty.
    apply dset_match_nil.
    intuition simpl; eauto.
  Qed.

  (*
  Lemma crash_xform_cached : forall xp ds ms bm hm,
    crash_xform (rep xp (Cached ds) ms bm hm) =p=>
      exists d n ms', rep xp (Cached (d, nil)) ms' bm hm *
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
   *)
  
  Lemma crash_xform_rollback : forall xp d ms bm hm,
    crash_xform (rep xp (Rollback d) ms bm hm) =p=>
      exists d' ms', rep xp (Rollback d') ms' bm hm *
        [[[ d' ::: (crash_xform (diskIs (list2nmem d))) ]]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite MLog.crash_xform_rollback.
    cancel.
    eassign (mk_mstate hmap0 nil ms'); eauto.
    all: auto.
    simpl; apply handles_valid_nested_empty.
  Qed.

  Lemma any_pred_any : forall xp ds bm hm,
    recover_any_pred xp ds bm hm =p=>
    exists d, would_recover_any xp (d, nil) bm hm.
  Proof.
    unfold recover_any_pred; intros.
    xform_norm.
    rewrite cached_recover_any; cancel.
    rewrite rollback_recover_any; cancel.
  Qed.

(*
  Lemma recover_idem : forall xp ds bm hm,
    crash_xform (recover_any_pred xp ds bm hm) =p=>
                 recover_any_pred xp ds bm hm.
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
*)

  Theorem recover_ok:
    forall xp cs pr,
    {< F raw ds,
    PERM:pr   
    PRE:bm, hm,
      PermCacheDef.rep cs raw bm *
      [[ (F * recover_any_pred xp ds bm hm)%pred raw ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:ms' exists raw',
      PermCacheDef.rep (MSCache ms') raw' bm' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Cached (d, nil)) (fst ms') bm' hm' *
          [[[ d ::: crash_xform (diskIs (list2nmem (nthd n ds))) ]]]
      )%pred raw' ]]
    XCRASH:bm', hm',
      exists raw' cs' mm', PermCacheDef.rep cs' raw' bm' *
      [[ (exists d n, [[ n <= length (snd  ds) ]] *
          F * rep xp (Recovering d) mm' bm' hm' *
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
    or_l; cancel. eauto.
    auto.

    step.
    safestep.
    erewrite MLog.rep_hashmap_subset; eauto.
    rewrite nthd_0; simpl; eauto.
    eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
    eassumption.
    erewrite MLog.rep_hashmap_subset; eauto.
    rewrite nthd_0; simpl; eauto.
    eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
    pred_apply; eassign (nil: list (addr * tagged_block)); cancel.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    intuition.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate hmap0 nil x1); eauto.
    intuition simpl; eauto.
    apply handles_valid_nested_empty.
    cancel.
    intuition simpl; eauto.
    apply handles_valid_nested_empty.

    (* Rollback *)
    unfold MLog.recover_either_pred; cancel.
    rewrite sep_star_or_distr; or_r; cancel.
    auto.

    step.
    safestep.
     erewrite MLog.rep_hashmap_subset; eauto.
    rewrite nthd_0; simpl; eauto.
    eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
    eassumption.
    erewrite MLog.rep_hashmap_subset; eauto.
    rewrite nthd_0; simpl; eauto.
    eauto.
    apply handles_valid_nested_empty.
    apply dset_match_nil.
    pred_apply; eassign (nil: list (addr * tagged_block)); cancel.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    repeat xcrash_rewrite.
    xform_norm.
    cancel.
    xform_norm; cancel.
    xform_norm; cancel.
    rewrite crash_xform_sep_star_dist; cancel.
    xform_norm.
    norm. cancel.
    intuition.
    pred_apply.
    norm. cancel.

    eassign (mk_mstate hmap0 nil x1); eauto.
    intuition simpl; eauto.
    apply handles_valid_nested_empty.
    cancel.
    intuition simpl; eauto.
    apply handles_valid_nested_empty.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (recover _ _) _) => apply recover_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dwrite _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dwrite_vecs _ _ _) _) => apply dwrite_vecs_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dsync _ _ _) _) => apply dsync_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (dsync_vecs _ _ _) _) => apply dsync_vecs_ok : prog.


End GLog.

