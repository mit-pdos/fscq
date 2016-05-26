Require Import Mem.
Require Import List.
Require Import Prog.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.



Definition eviction_state : Type := unit.
Definition eviction_init : eviction_state := tt.
Definition eviction_update (s : eviction_state) (a : addr) := s.
Definition eviction_choose (s : eviction_state) : (addr * eviction_state) := (0, s).

Module UCache.

  Definition cachemap := Map.t (valu * bool).  (* (valu, dirty flag) *)

  Record cachestate := mk_cs {
    CSMap : cachemap;
    CSMaxCount : nat;
    CSEvict : eviction_state
  }.

  (* write-back if a block is dirty, but do not evict from cache *)
  Definition writeback T a (cs : cachestate) rx : prog T :=
    match (Map.find a (CSMap cs)) with
    | Some (v, true) =>
      Write a v ;;
      rx (mk_cs (Map.add a (v, false) (CSMap cs)) (CSMaxCount cs) (CSEvict cs))
    | _ =>
      rx cs
    end.

  Definition evict T a (cs : cachestate) rx : prog T :=
    cs <- writeback a cs;
    rx (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSEvict cs)).

  Definition maybe_evict T (cs : cachestate) rx : prog T :=
    If (lt_dec (Map.cardinal (CSMap cs)) (CSMaxCount cs)) {
      rx cs
    } else {
      let (victim, evictor) := eviction_choose (CSEvict cs) in
      match (Map.find victim (CSMap cs)) with
      | Some _ =>
        cs <- evict victim (mk_cs (CSMap cs) (CSMaxCount cs) evictor);
        rx cs
      | None => (* evictor failed, evict first block *)
        match (Map.elements (CSMap cs)) with
        | nil => rx cs
        | (a, v) :: tl =>
          cs <- evict a cs;
          rx cs
        end
      end
    }.

  Definition read T a (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    match Map.find a (CSMap cs) with
    | Some (v, dirty) => rx ^(cs, v)
    | None =>
      v <- Read a;
      rx ^(mk_cs (Map.add a (v, false) (CSMap cs))
                 (CSMaxCount cs) (eviction_update (CSEvict cs) a), v)
    end.

  Definition write T a v (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    rx (mk_cs (Map.add a (v, true) (CSMap cs))
              (CSMaxCount cs) (eviction_update (CSEvict cs) a)).

  Definition begin_sync T (cs : cachestate) rx : prog T :=
    rx cs.

  Definition sync T a (cs : cachestate) rx : prog T :=
    cs <- writeback a cs;
    rx cs.

  Definition end_sync T (cs : cachestate) rx : prog T :=
    @Sync T;;
    rx cs.

  Definition evict_sync T a (cs : cachestate) rx : prog T :=
    cs <- evict a cs;
    @Sync T;;
    rx cs.

  Definition cache0 sz := mk_cs (Map.empty _) sz eviction_init.

  Definition init T (cachesize : nat) (rx : cachestate -> prog T) : prog T :=
    rx (cache0 cachesize).

  Definition read_array T a i cs rx : prog T :=
    r <- read (a + i) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a + i) v cs;
    rx cs.


  (** rep invariant *)

  Definition size_valid cs :=
    Map.cardinal (CSMap cs) <= CSMaxCount cs /\ CSMaxCount cs <> 0.

  Definition addr_valid (d : rawdisk) (cm : cachemap) :=
    forall a, Map.In a cm -> d a <> None.

  Definition addr_clean cs a :=
    Map.find a (CSMap cs) = None \/ exists v, Map.find a (CSMap cs) = Some (v, false).

  Definition addrs_clean cs al :=
    Forall (addr_clean cs) al.

  Definition cachepred (cache : cachemap) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    (match Map.find a cache with
    | None => a |+> vs
    | Some (v, false) => a |+> vs * [[ v = fst vs ]]
    | Some (v, true)  => exists v0, a |+> (v0, snd vs) * [[ v = fst vs /\ In v0 (snd vs) ]]
    end)%pred.

  Notation mem_pred := (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _).

  Definition rep (cs : cachestate) (m : rawdisk) : rawpred :=
    ([[ size_valid cs /\ addr_valid m (CSMap cs) ]] *
     mem_pred (cachepred (CSMap cs)) m)%pred.

  Definition synpred (cache : cachemap) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    (exists vsd, a |+> vsd *
    match Map.find a cache with
    | None =>  [[ vs = (fst vsd, nil) ]]
    | Some (v, false) => [[ vs = (fst vsd, nil) /\ v = fst vsd ]]
    | Some (v, true)  => [[ vs = (v, (fst vsd) :: nil) ]]
    end)%pred.

  Definition synrep (cs : cachestate) (m : rawdisk) : rawpred :=
    ([[ size_valid cs /\ addr_valid m (CSMap cs) ]] *
     mem_pred (synpred (CSMap cs)) m)%pred.


  (** helper lemmas *)

  Theorem sync_invariant_cachepred : forall cache a vs,
    sync_invariant (cachepred cache a vs).
  Proof.
    unfold cachepred; intros.
    destruct (Map.find a cache); eauto.
    destruct p; destruct b; eauto.
  Qed.

  Theorem sync_invariant_synpred : forall cache a vs,
    sync_invariant (synpred cache a vs).
  Proof.
    unfold synpred; intros.
    destruct (Map.find a cache); eauto.
    destruct p; destruct b; eauto.
  Qed.

  Hint Resolve sync_invariant_cachepred sync_invariant_synpred.

  Theorem sync_invariant_rep : forall cs m,
    sync_invariant (rep cs m).
  Proof.
    unfold rep; eauto.
  Qed.

  Theorem sync_invariant_synrep : forall cs m,
    sync_invariant (synrep cs m).
  Proof.
    unfold synrep; eauto.
  Qed.

  Hint Resolve sync_invariant_rep sync_invariant_synrep.

  Lemma cachepred_remove_invariant : forall a a' v cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.remove a' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma cachepred_add_invariant : forall a a' v v' cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.add a' v' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.

  Lemma synpred_remove_invariant : forall a a' v cache,
    a <> a' -> synpred cache a v =p=> synpred (Map.remove a' cache) a v.
  Proof.
    unfold synpred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma synpred_add_invariant : forall a a' v v' cache,
    a <> a' -> synpred cache a v =p=> synpred (Map.add a' v' cache) a v.
  Proof.
    unfold synpred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.


  Lemma mem_pred_cachepred_remove_absorb : forall csmap d a w vs p_old,
    d a = Some (w, p_old) ->
    incl vs (vsmerge (w, p_old)) ->
    mem_pred (cachepred csmap) (mem_except d a) * a |-> (w, vs) =p=>
    mem_pred (cachepred (Map.remove a csmap)) d.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.remove_eq_o by auto.
    unfold ptsto_subset; cancel; eauto.
    rewrite mem_pred_pimpl_except; eauto.
    intros; apply cachepred_remove_invariant; eauto.
  Qed.

  Lemma size_valid_remove : forall cs a,
    size_valid cs ->
    size_valid (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSEvict cs)).
  Proof.
    unfold size_valid in *; intuition simpl.
    eapply le_trans.
    apply map_cardinal_remove_le; auto.
    auto.
  Qed.

  Lemma size_valid_remove_cardinal_ok : forall cs a,
    size_valid cs ->
    Map.In a (CSMap cs) ->
    Map.cardinal (Map.remove a (CSMap cs)) < CSMaxCount cs.
  Proof.
    unfold size_valid; intros.
    rewrite map_remove_cardinal.
    omega.
    apply In_MapsTo; auto.
  Qed.

  Lemma addr_valid_remove : forall d a cm,
    addr_valid d cm ->
    addr_valid d (Map.remove a cm).
  Proof.
    unfold addr_valid; intros.
    apply H.
    eapply MapFacts.remove_in_iff; eauto.
  Qed.


  Lemma addr_valid_mem_valid : forall a cm c d,
    Map.find a cm = Some c ->
    addr_valid d cm ->
    exists vs, d a = Some vs.
  Proof.
    intros.
    assert (Map.In a cm).
    apply MapFacts.in_find_iff.
    destruct (Map.find a cm); try congruence.
    specialize (H0 _ H1).
    destruct (d a); try congruence; eauto.
  Qed.

  Lemma addr_valid_ptsto_subset : forall a cm c d,
    Map.find a cm = Some c ->
    addr_valid d cm ->
    exists (F : rawpred) vs, (F * a |+> vs)%pred d.
  Proof.
    intros.
    edestruct addr_valid_mem_valid; eauto.
    exists (diskIs (mem_except d a)), x.
    eapply diskIs_extract' in H1.
    specialize (H1 d eq_refl).
    pred_apply; unfold ptsto_subset; cancel.
    apply incl_tl; apply incl_refl.
  Qed.


  Lemma mem_pred_cachepred_add_absorb_clean : forall csmap d a v vs,
    d a = Some (v, vs) ->
    mem_pred (cachepred csmap) (mem_except d a) ✶ a |+> (v, vs) =p=>
    mem_pred (cachepred (Map.add a (v, false) csmap)) d.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.add_eq_o by auto.
    unfold ptsto_subset; cancel; eauto.
    rewrite mem_pred_pimpl_except; eauto.
    intros; apply cachepred_add_invariant; eauto.
  Qed.

  Lemma addr_clean_cachepred_remove : forall cs a d F vs,
    addr_clean cs a ->
    (F * a |+> vs)%pred d ->
    mem_pred (cachepred (CSMap cs)) d =p=> mem_pred (cachepred (Map.remove a (CSMap cs))) d.
  Proof.
    unfold addr_clean; intros.
    apply ptsto_subset_valid' in H0; repeat deex.
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2; rewrite H0.
      unfold ptsto_subset; cancel.
      rewrite sep_star_comm.
      eapply mem_pred_cachepred_remove_absorb; eauto.
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2; rewrite H.
      unfold ptsto_subset; cancel.
      rewrite sep_star_comm.
      eapply mem_pred_cachepred_remove_absorb; eauto.
  Qed.

  Lemma size_valid_add_in : forall cs evictor vv v a,
    Map.find a (CSMap cs) = Some v ->
    size_valid cs ->
    size_valid (mk_cs (Map.add a vv (CSMap cs)) (CSMaxCount cs) evictor).
  Proof.
    unfold size_valid; intuition; simpl.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
  Qed.

  Lemma size_valid_add : forall cs evictor vv a,
    Map.cardinal (CSMap cs) < CSMaxCount cs ->
    size_valid cs ->
    size_valid (mk_cs (Map.add a vv (CSMap cs)) (CSMaxCount cs) evictor).
  Proof.
    unfold size_valid; intuition; simpl.
    destruct (Map.find a0 (CSMap cs)) eqn:?.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_cardinal. omega.
    intuition deex.
    apply MapFacts.find_mapsto_iff in H0; congruence.
  Qed.

  Lemma addr_valid_add : forall d cm a vv v,
    d a = Some v ->
    addr_valid d cm ->
    addr_valid d (Map.add a vv cm).
  Proof.
    unfold addr_valid; intros.
    destruct (addr_eq_dec a a0); subst; try congruence.
    apply H0.
    eapply MapFacts.add_in_iff in H1; intuition.
  Qed.


  Lemma addr_valid_upd : forall a vs d cm,
    addr_valid d cm ->
    addr_valid (upd d a vs) cm.
  Proof.
    unfold addr_valid; intros.
    destruct (addr_eq_dec a a0); subst.
    rewrite upd_eq; congruence.
    rewrite upd_ne; auto.
  Qed.

  Lemma addr_valid_upd_add : forall a vs vc d cm,
    addr_valid d cm ->
    addr_valid (upd d a vs) (Map.add a vc cm).
  Proof.
    intros.
    eapply addr_valid_add; eauto.
    apply upd_eq; auto.
    apply addr_valid_upd; auto.
  Qed.


  Lemma incl_vsmerge_in : forall w v0 l l',
    incl l (vsmerge (w, (vsmerge (v0, l')))) ->
    In v0 (vsmerge (w, l')) ->
    incl l (vsmerge (w, l')).
  Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H0); intuition.
    specialize (H _ H0); intuition subst; auto.
  Qed.

  Lemma incl_vsmerge_in' : forall w v0 l l',
    incl l (vsmerge (w, (vsmerge (v0, l')))) ->
    In v0 l' ->
    incl l (vsmerge (w, l')).
  Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H1); intuition subst.
    right; auto.
  Qed.
  Local Hint Resolve incl_vsmerge_in incl_vsmerge_in'.



  Lemma in_vsmerge_hd : forall w l,
    In w (vsmerge (w, l)).
  Proof.
    unfold vsmerge; intuition.
  Qed.
  Local Hint Resolve in_vsmerge_hd.


  (** specs *)
  Opaque vsmerge.

  Theorem writeback_ok : forall a cs,
    {< d vs (F : rawpred),
    PRE
      rep cs d * [[ (F * a |+> vs)%pred d ]]
    POST RET:cs'
      rep cs' d * [[ addr_clean cs' a ]] * 
      [[ Map.In a (CSMap cs) -> Map.In a (CSMap cs') ]]
    CRASH
      exists cs', rep cs' d
    >} writeback a cs.
  Proof.
    unfold writeback, rep; intros.

    prestep; norml; unfold stars; simpl; clear_norm_goal;
    denote ptsto_subset as Hx; apply ptsto_subset_valid' in Hx; repeat deex.

    (* cached, dirty *)
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2.
      destruct (Map.find a (CSMap cs)) eqn:Hm; try congruence.
      destruct p; destruct b; try congruence.
      cancel.
      step.
      erewrite <- upd_nop with (m := d) at 2 by eauto.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity.
      unfold ptsto_subset; cancel; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      cancel.
      eapply size_valid_add_in; eauto.
      eapply addr_valid_add; eauto.
      unfold addr_clean; right; eexists; simpl.
      apply MapFacts.add_eq_o; auto.
      eapply MapFacts.add_in_iff; eauto.

      (* crash *)
      unfold ptsto_subset; cancel; eauto.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3; rewrite Hm.
      unfold ptsto_subset; cancel; eauto.

    (* cached, non-dirty *)
    - cancel.
      step.
      unfold addr_clean; right; eexists; eauto.
      cancel.

    (* not cached *)
    - cancel.
      step.
      unfold addr_clean; left; auto.
      cancel.

    Unshelve. all: try exact addr_eq_dec.
  Qed.

  Hint Extern 1 ({{_}} progseq (writeback _ _) _) => apply writeback_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (synrep _ _) (synrep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (mem_pred ?p _) (mem_pred ?p _)) => constructor : okToUnify.

  Theorem evict_ok : forall a cs,
    {< d vs (F : rawpred),
    PRE
      rep cs d * [[ (F * a |+> vs)%pred d ]]
    POST RET:cs'
      rep cs' d *
      [[ ~ Map.In a (CSMap cs') ]] *
      [[ Map.In a (CSMap cs) -> Map.cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH
      exists cs', rep cs' d
    >} evict a cs.
  Proof.
    unfold evict; intros.
    step.
    prestep; unfold rep; cancel.

    eapply addr_clean_cachepred_remove; eauto.
    apply size_valid_remove; auto.
    apply addr_valid_remove; auto.
    eapply Map.remove_1; eauto.
    eapply size_valid_remove_cardinal_ok; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (evict _ _) _) => apply evict_ok : prog.


  Theorem maybe_evict_ok : forall cs,
    {< d,
    PRE
      rep cs d
    POST RET:cs
      rep cs d * [[ Map.cardinal (CSMap cs) < CSMaxCount cs ]]
    CRASH
      exists cs', rep cs' d
    >} maybe_evict cs.
  Proof.
    unfold maybe_evict; intros.
    step.
    step.

    prestep; unfold rep; norml; unfold stars; simpl; clear_norm_goal.

    (* found the victim  *)
    - edestruct addr_valid_ptsto_subset; eauto.
      norm. 2: intuition eauto. cancel.
      step.
      unfold rep; cancel.
      denote ( _ -> _ < _) as Hx; apply Hx.
      apply MapFacts.in_find_iff; congruence.

    (* victim not found, cache is empty *)
    - unfold size_valid in *; cancel.
      rewrite Map.cardinal_1, Heql; simpl; omega.

    (* victim not found, cache is non-empty *)
    - clear Heqo.
      assert (Map.find k (CSMap cs) = Some (p0_1, p0_2)).
      rewrite MapFacts.elements_o, Heql; simpl.
      destruct (MapFacts.eqb k k) eqn:?; auto.
      contradict Heqb.
      unfold MapFacts.eqb, MapOrdProperties.P.F.eq_dec.
      destruct (Nat.eq_dec k k); congruence.

      edestruct addr_valid_ptsto_subset; eauto; repeat deex.
      norm. 2: intuition eauto. cancel.
      step.
      unfold rep; cancel.
      denote ( _ -> _ < _) as Hx; apply Hx.
      apply MapFacts.in_find_iff; congruence.

    Unshelve. all: eauto; exact 0.
  Qed.

  Hint Extern 1 ({{_}} progseq (maybe_evict _) _) => apply maybe_evict_ok : prog.



  Theorem read_ok : forall cs a,
    {< d (F : rawpred) v vs,
    PRE
      rep cs d * [[ (F * a |+> (v, vs))%pred d ]]
    POST RET:^(cs, r)
      rep cs d * [[ r = v ]]
    CRASH
      exists cs', rep cs' d
    >} read a cs.
  Proof.
    unfold read, rep; intros.
    safestep; eauto.
    unfold rep; cancel.

    prestep; unfold rep; norml; unfold stars; simpl; clear_norm_goal;
    edestruct ptsto_subset_valid'; eauto; intuition simpl in *;
    erewrite mem_pred_extract with (a := a) at 1 by eauto;
    unfold cachepred at 2; rewrite Heqo.

    (* found in cache *)
    - destruct b; simpl.
      unfold ptsto_subset; cancel.
      rewrite sep_star_comm.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3; rewrite Heqo.
      unfold ptsto_subset; cancel; eauto.

      cancel.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3.
      rewrite Heqo.
      unfold ptsto_subset; cancel; eauto.

    (* not found *)
    - cancel.
      step.
      eapply mem_pred_cachepred_add_absorb_clean; eauto.
      apply size_valid_add; auto.
      eapply addr_valid_add; eauto.

      cancel; eauto.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold cachepred at 3.
      rewrite Heqo.
      unfold ptsto_subset; cancel; eauto.
  Qed.


  Theorem write_ok : forall cs a v,
    {< d (F : rawpred) v0,
    PRE
      rep cs d * [[ (F * a |+> v0)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a |+> (v, vsmerge v0))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} write a v cs.
  Proof.
    unfold write, rep; intros.
    safestep; eauto.
    unfold rep; cancel.

    prestep; unfold rep; norml; unfold stars; simpl; clear_norm_goal.
    edestruct ptsto_subset_valid'; eauto; intuition simpl in *.
    erewrite mem_pred_extract with (a := a) at 1 by eauto.
    unfold cachepred at 2.
    destruct (Map.find a (CSMap r_)) eqn:Hm.
    destruct p; destruct b.

    (* found in cache, was dirty *)
    - cancel.
      2: apply size_valid_add; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      rewrite <- mem_pred_absorb with (hm := d) (a := a) (v := (v, v0_cur :: x)).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity; safecancel.
      eassign v0; rewrite ptsto_subset_pimpl.
      cancel.
      apply incl_tl; apply incl_refl.
      apply in_cons; auto.

      apply addr_valid_upd_add; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_cons2; auto.

    (* found in cache, was clean *)
    - cancel.
      2: apply size_valid_add; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      rewrite <- mem_pred_absorb with (hm := d) (a := a) (v := (v, v0_cur :: x)).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity; safecancel.
      rewrite ptsto_subset_pimpl.
      cancel.
      apply incl_tl; apply incl_refl.
      left; auto.
      apply addr_valid_upd_add; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_cons; simpl; auto.
      eapply incl_tran; eauto; apply incl_tl; apply incl_refl.

    (* not found in cache *)
    - cancel.
      2: apply size_valid_add; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply cachepred_add_invariant; eassumption.
      rewrite <- mem_pred_absorb with (hm := d) (a := a) (v := (v, v0_cur :: x)).
      unfold cachepred at 3.
      rewrite MapFacts.add_eq_o by reflexivity; safecancel.
      rewrite ptsto_subset_pimpl.
      cancel.
      apply incl_tl; apply incl_refl.
      left; auto.
      apply addr_valid_upd_add; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_cons; simpl; auto.
      eapply incl_tran; eauto; apply incl_tl; apply incl_refl.
  Qed.


  Lemma cachepred_synpred : forall cm a vs,
    cachepred cm a vs =p=> exists vs', synpred cm a vs' *
      [[ fst vs' = fst vs /\ incl (snd vs') (snd vs) ]].
  Proof.
    unfold cachepred, synpred; intros.
    destruct (Map.find a cm) eqn:?.
    destruct p, b; cancel.
    apply incl_cons; auto; apply incl_nil.
    apply incl_nil.
    cancel; apply incl_nil.
  Qed.

  Definition avs_match (avs1 avs2 : addr * valuset)  : Prop :=
    let '(a1, vs1) := avs1 in let '(a2, vs2) := avs2 in
    a2 = a1 /\ (fst vs2 = fst vs1) /\ incl (snd vs2) (snd vs1).

  Lemma listpred_cachepred_synpred : forall l cm,
    listpred (fun av => cachepred cm (fst av) (snd av)) l =p=> exists l',
    listpred (fun av => synpred cm (fst av) (snd av)) l' *
    [[ Forall2 avs_match l l' ]].
  Proof.
    induction l; simpl; intros.
    cancel; simpl; auto.
    rewrite cachepred_synpred, IHl.
    cancel.
    eassign ((a_1, (a_2_cur, vs'_old)) :: l'); simpl.
    cancel.
    constructor; auto.
    unfold avs_match; simpl; intuition.
  Qed.

  Lemma avs_match_map_fst_eq : forall l l',
    Forall2 avs_match l l' ->
    map fst l' = map fst l.
  Proof.
    unfold avs_match; induction 1; simpl; auto.
    f_equal; auto.
    destruct x, y; intuition.
  Qed.

  Lemma avs2mem_mem_match : forall V l l',
    map fst l' = map fst l ->
    @mem_match _ V _ (avs2mem addr_eq_dec l) (avs2mem addr_eq_dec l').
  Proof.
    induction l; destruct l'; simpl; try congruence; intros; cbn.
    cbv; intuition.
    destruct a, p; simpl in *.
    inversion H; subst.
    apply mem_match_upd.
    apply IHl; auto.
  Qed.

  Lemma addr_valid_mem_match : forall d d' cm,
    mem_match d d' ->
    addr_valid d cm ->
    addr_valid d' cm.
  Proof.
    unfold addr_valid; intros.
    specialize (H0 _ H1).
    edestruct mem_match_cases with (a := a); eauto; intuition.
    repeat deex; congruence.
  Qed.

  Lemma avs_match_addr_valid : forall l l' cm,
    Forall2 avs_match l l' ->
    addr_valid (avs2mem addr_eq_dec l) cm ->
    addr_valid (avs2mem addr_eq_dec l') cm.
  Proof.
    intros.
    eapply addr_valid_mem_match; eauto.
    apply avs2mem_mem_match.
    apply avs_match_map_fst_eq; auto.
  Qed.

  Lemma avs_match_possible_sync : forall l l',
    Forall2 avs_match l l' ->
    possible_sync (avs2mem addr_eq_dec l) (avs2mem addr_eq_dec l').
  Proof.
    unfold possible_sync; induction 1; intuition.
    unfold avs_match in H.
    specialize (IHForall2 a); destruct x, y; cbn.
    destruct p, p0; intuition; simpl in *; subst; repeat deex.
    - destruct (addr_eq_dec a n); subst.
      repeat rewrite upd_eq; auto.
      right; do 3 eexists; intuition.
      repeat rewrite upd_ne; auto.
    - destruct (addr_eq_dec a n); subst.
      repeat rewrite upd_eq; auto.
      right; do 3 eexists; intuition.
      repeat rewrite upd_ne; auto.
      right; do 3 eexists; intuition eauto.
  Qed.

  Lemma avs_match_sync_invariant : forall l l' F,
    Forall2 avs_match l l' ->
    sync_invariant F ->
    F (avs2mem addr_eq_dec l) ->
    F (avs2mem addr_eq_dec l').
  Proof.
    unfold sync_invariant; intros.
    eapply H0; eauto.
    apply avs_match_possible_sync; auto.
  Qed.

  Lemma synpred_cachepred : forall vs cm a,
    sync_xform (synpred cm a vs) =p=> cachepred cm a vs.
  Proof.
    unfold cachepred, synpred; intros.
    rewrite sync_xform_exists_comm.
    apply pimpl_exists_l; intro vs0.
    rewrite sync_xform_sep_star_dist.
    destruct vs0 as [v0 l0].
    destruct (Map.find a cm) eqn:?; try destruct p, b;
    rewrite sync_xform_lift_empty, sync_xform_ptsto_subset_precise;
    unfold ptsto_subset; cancel; apply incl_nil.
  Qed.

  Lemma sync_xform_listpred_synpred_cachepred : forall l cm,
    sync_xform (listpred (fun x => synpred cm (fst x) (snd x)) l) =p=>
    listpred (fun x => cachepred cm (fst x) (snd x)) l.
  Proof.
    intros; rewrite sync_xform_listpred; eauto.
    intros; eapply synpred_cachepred.
  Qed.



  Theorem begin_sync_ok : forall cs,
    {< d F,
    PRE
      rep cs d * [[ sync_invariant F /\ F d ]]
    POST RET:cs exists d',
      synrep cs d' * [[ F d' ]]
    CRASH
      exists cs', rep cs' d
    >} begin_sync cs.
  Proof.
    unfold begin_sync, rep, synrep.
    step.
    prestep; unfold mem_pred.
    norml; unfold stars, mem_pred_one; simpl; clear_norm_goal.
    rewrite listpred_cachepred_synpred; cancel.
    eapply avs_match_addr_valid; eauto.
    erewrite avs_match_map_fst_eq; eauto.
    eapply avs_match_sync_invariant; eauto.
  Qed.

  Theorem end_sync_ok : forall cs,
    {< d F,
    PRE
      synrep cs d * [[ F d ]]
    POST RET:cs exists d',
      rep cs d' * [[ F d' ]]
    CRASH
      exists cs', synrep cs' d
    >} end_sync cs.
  Proof.
    unfold end_sync, rep, synrep.
    step.
    prestep; unfold mem_pred.
    norml; unfold stars, mem_pred_one; simpl; clear_norm_goal.
    rewrite pimpl_exists_r_star_r, sync_xform_exists_comm, pimpl_exists_r_star_r.
    apply pimpl_exists_l; intros.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
    rewrite sync_xform_listpred_synpred_cachepred.
    rewrite sync_xform_sync_invariant by auto.
    cancel.
    auto.
  Qed.

  Theorem writeback_ok' : forall cs a,
    {< d (F : rawpred) v0,
    PRE
      synrep cs d * [[ (F * a |+> v0)%pred d ]]
    POST RET:cs exists d',
      synrep cs d' * [[ (F * a |+> (fst v0, nil))%pred d' ]]
    CRASH
      exists cs', synrep cs' d
    >} writeback a cs.
  Proof.
    unfold writeback, synrep.
    prestep; unfold synrep; norml; unfold stars; simpl; clear_norm_goal;
    denote ptsto_subset as Hx; apply ptsto_subset_valid' in Hx as Hy; repeat deex.

    (* cached, dirty *)
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold synpred at 2.
      destruct (Map.find a (CSMap cs)) eqn:Hm; try congruence.
      destruct p; destruct b; try congruence.
      cancel.
      step.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold synpred at 3.
      rewrite MapFacts.add_eq_o by reflexivity.
      unfold ptsto_subset; cancel; eauto.
      rewrite mem_pred_pimpl_except.
      2: intros; apply synpred_add_invariant; eassumption.
      cancel.
      eapply size_valid_add_in; eauto.
      eapply addr_valid_add; eauto.
      apply upd_eq; auto.
      apply addr_valid_upd; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_refl.

      (* crash *)
      unfold ptsto_subset; cancel; eauto.
      eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
      unfold synpred at 3; rewrite Hm.
      unfold ptsto_subset; cancel; eauto.

    (* cached, non-dirty *)
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold synpred at 2.
      destruct (Map.find a (CSMap cs)) eqn:Hm; try congruence.
      destruct p; destruct b; try congruence.
      cancel.
      prestep. norm. unfold stars; simpl.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold synpred at 3.
      rewrite Hm.
      cancel.
      intuition.
      apply addr_valid_upd; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_refl.

      (* crash *)
      cancel.
      erewrite <- upd_nop with (m := d) at 2 by eauto.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold synpred at 3; rewrite Hm; cancel.
      auto. auto.

    (* not cached *)
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold synpred at 2.
      destruct (Map.find a (CSMap cs)) eqn:Hm; try congruence.
      cancel.
      prestep. norm. unfold stars; simpl.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold synpred at 3.
      rewrite Hm.
      cancel.
      intuition.
      apply addr_valid_upd; auto.
      eapply ptsto_subset_upd; eauto.
      apply incl_refl.

      (* crash *)
      cancel.
      erewrite <- upd_nop with (m := d) at 2 by eauto.
      rewrite <- mem_pred_absorb with (hm := d) (a := a).
      unfold synpred at 3; rewrite Hm; cancel.
      auto. auto.
    Unshelve. all: try exact addr_eq_dec.
  Qed.

  Theorem sync_ok : forall cs a,
    {< d (F : rawpred) v0,
    PRE
      synrep cs d * [[ (F * a |+> v0)%pred d ]]
    POST RET:cs exists d',
      synrep cs d' * [[ (F * a |+> (fst v0, nil))%pred d' ]]
    CRASH
      exists cs', synrep cs' d
    >} sync a cs.
  Proof.
    unfold sync; intros.
    eapply pimpl_ok2.
    apply writeback_ok'.
    cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (begin_sync _) _) => apply begin_sync_ok : prog.
  Hint Extern 1 ({{_}} progseq (end_sync _) _) => apply end_sync_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.


  Definition sync_one T a (cs : cachestate) rx : prog T :=
    cs <- begin_sync cs;
    cs <- sync a cs;
    cs <- end_sync cs;
    rx cs.

  Theorem sync_one_ok : forall cs a,
    {< d (F : rawpred) v0,
    PRE
      rep cs d * [[ sync_invariant F /\ (F * a |+> v0)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a |+> (fst v0, nil))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} sync_one a cs.
  Proof.
    unfold sync_one.
    prestep; norm. cancel. intuition simpl.
    2: eauto. eauto.
    safestep.
    step.
    step.
    2: cancel.
    (* XXX: synrep =p=> rep  *)
  Admitted.




  Fixpoint avl_sync_addr (a : addr) (l : list (addr * valuset)) : list (addr * valuset) :=
    match l with
    | nil => nil
    | (a', vs) :: rest =>
      let rest' := avl_sync_addr a rest in
      if addr_eq_dec a' a then (a, (fst vs, nil)) :: rest' else (a', vs) :: rest'
    end.

  Lemma sync_xform_listpred_cachepred_notin : forall l a cm,
    Map.find a cm = None ->
    NoDup (map fst l) ->
    sync_xform (listpred (fun av => cachepred cm (fst av) (snd av)) l) =p=>
    (listpred (fun av => cachepred cm (fst av) (snd av)) (avl_sync_addr a l)).
  Proof.
    induction l; simpl; intros.
    apply sync_xform_emp.
    destruct a as [a vs]; simpl in *.
    inversion H0; subst.
    rewrite sync_xform_sep_star_dist.
    destruct (addr_eq_dec a a0); subst; simpl.
    - unfold cachepred at 1 3.
      rewrite H; rewrite IHl; eauto; cancel.
      rewrite sync_xform_ptsto_subset_precise.
      rewrite ptsto_pimpl_ptsto_subset; auto.
    - rewrite IHl; eauto; cancel.
      rewrite sync_xform_sync_invariant; eauto.
  Qed.

  Lemma avl_sync_addr_map_fst : forall l a,
    map fst (avl_sync_addr a l) = map fst l.
  Proof.
    induction l; simpl; auto; intros.
    destruct a; simpl.
    destruct (addr_eq_dec n a0); subst; simpl; rewrite IHl; auto.
  Qed.

  Lemma sync_addr_avs2mem_avl_sync_addr : forall l a,
    NoDup (map fst l) ->
    sync_addr (avs2mem addr_eq_dec l) a = avs2mem addr_eq_dec (avl_sync_addr a l).
  Proof.
    unfold avs2mem, sync_addr.
    induction l; simpl; intros; apply functional_extensionality; intros.
    destruct (addr_eq_dec a x); auto.

    inversion H; subst.
    destruct a; destruct (addr_eq_dec a0 x); subst; simpl in *.
    - destruct (addr_eq_dec n x); subst; simpl.
      repeat rewrite upd_eq; auto; subst.
      destruct p; auto.
      repeat rewrite upd_ne; auto; subst.
      rewrite <- IHl; auto.
      destruct (addr_eq_dec x x); try congruence.
    - destruct (addr_eq_dec n a0); subst; simpl.
      repeat rewrite upd_ne; auto.
      rewrite <- IHl; auto.
      destruct (addr_eq_dec a0 x); try congruence.
      destruct (addr_eq_dec x n); subst; try congruence.
      repeat rewrite upd_eq; auto.
      repeat rewrite upd_ne; auto.
      rewrite <- IHl; auto.
      destruct (addr_eq_dec a0 x); try congruence.
  Qed.

  Lemma sync_xform_mem_pred_cache_notin : forall cm d a,
    ~ Map.In a cm ->
    sync_xform (mem_pred (cachepred cm) d) =p=> mem_pred (cachepred cm) (sync_addr d a).
  Proof.
    unfold mem_pred, mem_pred_one; intros.
    rewrite sync_xform_exists_comm.
    apply pimpl_exists_l; intro l.
    repeat rewrite sync_xform_sep_star_dist.
    repeat rewrite sync_xform_lift_empty.
    cancel.
    apply sync_xform_listpred_cachepred_notin; eauto.
    apply MapFacts.not_find_in_iff; eauto.
    rewrite avl_sync_addr_map_fst; auto.
    apply sync_addr_avs2mem_avl_sync_addr; auto.
  Qed.

  Lemma addr_valid_sync_addr : forall d a cm,
    addr_valid d cm ->
    addr_valid (sync_addr d a) cm.
  Proof.
    unfold addr_valid, sync_addr; intros.
    destruct (addr_eq_dec a a0); subst; auto.
    destruct (d a0) eqn:?; auto.
    destruct p; congruence.
    specialize (H _ H0); congruence.
  Qed.

  Lemma sync_addr_ptsto_subset : forall AT AEQ (m : @mem AT AEQ valuset) F a v vs,
    (F * a |+> (v, vs))%pred m ->
    (F * a |+> (v, nil))%pred (sync_addr m a).
  Proof.
    unfold sync_addr; unfold_sep_star; intros; repeat deex.
    exists m1.
    exists (fun a' => if AEQ a' a then Some (v, nil) else None).
    split; [|split].
    - apply functional_extensionality; intro.
      destruct (AEQ a x); subst.
      unfold mem_union; destruct (AEQ x x); try congruence.
      unfold ptsto_subset in H3; destruct_lift H3.
      destruct (m1 x) eqn:?.
      destruct H.
      repeat eexists; eauto.
      eapply ptsto_valid.
      pred_apply; cancel.
      erewrite ptsto_valid.
      2: pred_apply; cancel.
      auto.
      unfold mem_union.
      destruct (m1 x); auto.
      destruct (AEQ x a); subst; try congruence.
      unfold ptsto_subset, ptsto in H3; destruct_lift H3; intuition.
    - unfold mem_disjoint in *. intuition. repeat deex.
      apply H.
      unfold ptsto_subset, ptsto in H3; destruct_lift H3; intuition.
      destruct (AEQ a0 a); subst; eauto; congruence.
    - intuition.
      unfold ptsto_subset in *.
      destruct_lift H3; intuition.
      eexists.
      apply sep_star_lift_apply'.
      unfold ptsto; intuition.
      destruct (AEQ a a); eauto; intuition.
      destruct (AEQ a' a); eauto; congruence.
      apply incl_nil.
  Qed.

  Theorem evict_sync_ok : forall cs a,
    {< d (F : rawpred) v0,
    PRE
      rep cs d * [[ (F * a |+> v0)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a |+> (fst v0, nil))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} evict_sync a cs.
  Proof.
    unfold evict_sync, rep; intros.
    prestep; unfold rep; safecancel.

    safestep.
    safestep.
    rewrite sync_xform_sep_star_dist.
    setoid_rewrite sync_xform_sync_invariant at 2; auto.
    rewrite sync_xform_mem_pred_cache_notin by eauto.
    cancel.
    apply addr_valid_sync_addr; auto.
    eapply sync_addr_ptsto_subset; eauto.
    cancel.
  Qed.


End UCache.

Global Opaque UCache.write_array.
Global Opaque UCache.read_array.

