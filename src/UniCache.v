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

  Definition addr_clean (cm : cachemap) a :=
    Map.find a cm = None \/ exists v, Map.find a cm = Some (v, false).

  Definition addrs_clean cm al :=
    Forall (addr_clean cm) al.

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

  Definition synrep' (cs : cachestate) (m : rawdisk) : rawpred :=
    ([[ size_valid cs /\ addr_valid m (CSMap cs) ]] *
     mem_pred (synpred (CSMap cs)) m)%pred.

  Definition synrep (cs : cachestate) (mbase m : rawdisk) : rawpred :=
    (rep cs mbase /\ synrep' cs m)%pred.


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

  Hint Resolve sync_invariant_rep.

  Theorem sync_invariant_synrep' : forall cs m,
    sync_invariant (synrep' cs m).
  Proof.
    unfold synrep'; eauto.
  Qed.

  Hint Resolve sync_invariant_synrep'.

  Theorem sync_invariant_synrep : forall cs mbase m,
    sync_invariant (synrep cs mbase m).
  Proof.
    unfold synrep; eauto.
  Qed.

  Hint Resolve sync_invariant_synrep.

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
    addr_clean (CSMap cs) a ->
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

  Theorem writeback_ok' : forall a cs,
    {< vs0,
    PRE
      a |+> vs0
    POST RET:cs' exists v,
      ( [[ Map.find a (CSMap cs) = Some (v, true) /\
         cs' = mk_cs (Map.add a (v, false) (CSMap cs)) (CSMaxCount cs) (CSEvict cs) ]] *
         a |+> (v, vsmerge vs0)) \/
      ( [[ (Map.find a (CSMap cs) = None \/
          exists v, Map.find a (CSMap cs) = Some (v, false)) /\ cs' = cs ]] * a |+> vs0 )
    CRASH
      a |+> vs0
    >} writeback a cs.
  Proof.
    unfold writeback; intros.
    hoare.
    Unshelve. all: eauto.
  Qed.


  Theorem writeback_ok : forall a cs,
    {< d vs (F : rawpred),
    PRE
      rep cs d * [[ (F * a |+> vs)%pred d ]]
    POST RET:cs'
      rep cs' d * [[ addr_clean (CSMap cs') a ]] * 
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
  Hint Extern 0 (okToUnify (synrep _ _ _) (synrep _ _ _)) => constructor : okToUnify.
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
      [[ fst vs' = fst vs /\ incl (snd vs') (snd vs) /\
         (addr_clean cm a -> snd vs' = nil) ]].
  Proof.
    unfold cachepred, synpred, addr_clean; intros.
    destruct (Map.find a cm) eqn:?.
    destruct p, b; cancel.
    apply incl_cons; auto; apply incl_nil.
    deex; congruence.
    apply incl_nil.
    cancel.
    apply incl_nil.
  Qed.

  Definition avs_match (avs1 avs2 : addr * valuset)  : Prop :=
    let '(a1, vs1) := avs1 in let '(a2, vs2) := avs2 in
    a2 = a1 /\ (fst vs2 = fst vs1) /\ incl (snd vs2) (snd vs1).

  Definition nil_if_clean cm (avs : addr * valuset)  : Prop :=
    let '(a, vs) := avs in addr_clean cm a -> snd vs = nil.

  Lemma listpred_cachepred_synpred : forall l cm,
    listpred (fun av => cachepred cm (fst av) (snd av)) l =p=> exists l',
    listpred (fun av => synpred cm (fst av) (snd av)) l' *
    [[ Forall2 avs_match l l' /\ Forall (nil_if_clean cm) l' ]].
  Proof.
    induction l; simpl; intros.
    cancel; simpl; auto.
    rewrite cachepred_synpred, IHl.
    safecancel.
    eassign ((a_1, (a_2_cur, vs'_old)) :: l'); simpl.
    cancel.
    constructor; auto.
    unfold avs_match; simpl; intuition.
    auto.
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

  Lemma avs_match_addr_valid' : forall l l' cm,
    Forall2 avs_match l' l ->
    addr_valid (avs2mem addr_eq_dec l) cm ->
    addr_valid (avs2mem addr_eq_dec l') cm.
  Proof.
    intros.
    eapply addr_valid_mem_match; eauto.
    apply avs2mem_mem_match.
    apply eq_sym.
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

  Lemma synpred_cachepred_sync : forall vs cm a,
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
    intros; eapply synpred_cachepred_sync.
  Qed.


  Lemma rep_synrep_split : forall cs d F,
    rep cs d /\ (exists d', synrep' cs d' * [[ F d' ]]) =p=>
    (exists d', (rep cs d ⋀ synrep' cs d') * [[ F d' ]]).
  Proof.
    intros.
    rewrite pimpl_and_r_exists.
    unfold pimpl; intros. destruct H. destruct H. destruct_lift H0.
    exists x.
    eapply sep_star_lift_apply'; eauto.
    split; eauto.
  Qed.

  Lemma synrep_rep : forall cs d0 d,
    synrep cs d0 d =p=> rep cs d0.
  Proof.
    unfold synrep; intros.
    apply pimpl_l_and; eauto.
  Qed.


  Lemma nil_if_clean_synced : forall l a cm vs,
    Forall (nil_if_clean cm) l ->
    addr_clean cm a ->
    avs2mem addr_eq_dec l a = Some vs ->
    NoDup (map fst l) ->
    snd vs = nil.
  Proof.
    induction l; simpl; intros.
    cbv in H1; congruence.
    inversion H; inversion H2; subst.
    destruct a; cbn in H1; simpl in *.
    destruct (addr_eq_dec n a0); subst.
    rewrite upd_eq in H1 by auto; inversion H1; subst; eauto.
    rewrite upd_ne in H1 by auto.
    eapply IHl; eauto; simpl in *.
  Qed.


  Lemma rep_synrep : forall (F : rawpred) d0 cs,
    F d0 ->
    sync_invariant F ->
    rep cs d0 =p=> exists d, synrep cs d0 d * 
      [[ F d /\ forall a vs, addr_clean (CSMap cs) a -> d a = Some vs -> snd vs = nil ]].
  Proof.
    unfold synrep; intros.
    rewrite <- rep_synrep_split.
    apply pimpl_and_split; auto.
    unfold rep, synrep', mem_pred, mem_pred_one.
    norml; unfold stars; simpl.
    rewrite listpred_cachepred_synpred.
    cancel.
    eapply addr_valid_mem_match; eauto.
    apply avs2mem_mem_match.
    erewrite avs_match_map_fst_eq; eauto.
    erewrite avs_match_map_fst_eq; eauto.
    eapply avs_match_sync_invariant; eauto.
    eapply nil_if_clean_synced; eauto.
    erewrite avs_match_map_fst_eq; eauto.
  Qed.

  Theorem begin_sync_ok : forall cs,
    {< d F,
    PRE
      rep cs d * [[ sync_invariant F /\ F d ]]
    POST RET:cs exists d',
      synrep cs d d' * [[ F d' ]]
    CRASH
      exists cs', rep cs' d
    >} begin_sync cs.
  Proof.
    unfold begin_sync, synrep.
    step.
    prestep.
    norml; unfold stars; simpl.
    rewrite rep_synrep by eauto.
    cancel; eauto.
  Qed.

  Theorem end_sync_ok : forall cs,
    {< d0 d,
    PRE
      synrep cs d0 d
    POST RET:cs
      rep cs d
    CRASH
      exists cs', rep cs' d0
    >} end_sync cs.
  Proof.
    unfold end_sync, synrep, synrep'.
    step.
    prestep; unfold mem_pred.
    norml; unfold stars, mem_pred_one; simpl; clear_norm_goal.
    rewrite sync_xform_sep_star_dist. rewrite sync_xform_and_dist.
    rewrite sep_star_and_distr'. rewrite pimpl_r_and.
    unfold rep, mem_pred, mem_pred_one. 
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    norml; unfold stars; simpl.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    cancel.
    rewrite sync_xform_listpred_synpred_cachepred.
    rewrite sync_xform_sync_invariant by auto.
    cancel.
    all: auto.
    rewrite pimpl_l_and.
    cancel.
  Qed.

  Lemma rep_synrep_addr_clean : forall (F : rawpred) d0 cs a vs,
    (F * a |+> vs)%pred d0 ->
    addr_clean (CSMap cs) a ->
    sync_invariant F ->
    rep cs d0 =p=> exists d, synrep cs d0 d *
      [[ (F * a |=> fst vs)%pred d ]].
  Proof.
    intros.
    rewrite rep_synrep by eauto.
    norml; unfold stars; simpl; clear_norm_goal.
    apply pimpl_exists_r; exists d.
    cancel_exact; norm. cancel.

    denote (forall _ _, _) as Hx; denote ptsto_subset as Hz.
    eapply ptsto_subset_valid' in Hz as Hy; repeat deex; simpl in *.
    assert (snd (vs_cur, l) = nil) by (eapply Hx; eauto); clear Hx.
    simpl in *; subst.
    generalize Hz; unfold_sep_star; unfold ptsto_subset.
    intros; repeat deex.
    denote! (_ m2) as Hx; denote mem_union as Hy.
    destruct_lift Hx; do 2 eexists; intuition eauto.
    assert (dummy = nil); subst; auto.
    unfold ptsto in *; intuition.
    rewrite mem_union_comm in Hy; auto.
    erewrite mem_union_addr in Hy; eauto.
    inversion Hy; auto.
    apply mem_disjoint_comm; auto.
    Unshelve. all: try exact addr_eq_dec; eauto; try exact unit.
  Qed.



  Theorem sync_ok' : forall cs a,
    {< d0 d (F F' : rawpred) v0 v',
    PRE
      synrep cs d0 d * [[ sync_invariant F ]] *
      [[ (F * a |+> v0)%pred d ]] *
      [[ (F' * a |+> v')%pred d0 ]]
    POST RET:cs exists d,
      synrep cs d0 d *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH
      exists cs', rep cs' d0
    >} sync a cs.
  Proof.
    unfold sync; intros.
    eapply pimpl_ok2. apply writeback_ok'.
    intros.
    norml; unfold stars; simpl; clear_norm_goal.
    denote (_ d) as Hx; apply ptsto_subset_valid' in Hx as Hy; repeat deex.
    denote (_ d0) as Hz; apply ptsto_subset_valid' in Hz as Hy; repeat deex.
    unfold synrep, rep, synrep'.
    rewrite lift_empty_and_distr_l; norml; unfold stars; simpl; clear_norm_goal.
    rewrite mem_pred_extract with (a := a) (hm := d) by eauto.
    rewrite mem_pred_extract with (a := a) (hm := d0) by eauto.
    unfold cachepred at 2; unfold synpred at 2; simpl in *.
    destruct (Map.find a (CSMap cs)) eqn:?; try destruct p, b.
    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; clear_norm_goal; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl; clear_norm_goal.
      2: intuition; repeat deex; congruence.
      inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply cachepred_add_invariant; eassumption.
        cancel.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply synpred_add_invariant; eassumption.
        cancel.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
        rewrite upd_eq; auto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; clear_norm_goal; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl; clear_norm_goal;
      intuition; repeat deex; try congruence; inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

    - unfold ptsto_subset.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; clear_norm_goal; subst.
      rewrite sep_star_ptsto_and_eq.
      cancel; subst; eauto.

      prestep; norml; unfold stars; simpl; clear_norm_goal;
      intuition; repeat deex; try congruence; inv_option_eq.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        apply addr_valid_upd; auto.
      + (* crash *)
        cancel.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

    Unshelve. all: eauto.
  Qed.


  Theorem sync_synrep_helper_1 : forall m cs d0 d a (F : @pred _ addr_eq_dec _) v,
    synrep cs d0 d m ->
    (F * a |+> v)%pred d ->
    exists (F0 : @pred _ addr_eq_dec _) v0,
    (F0 * a |+> v0)%pred d0.
  Proof.
    unfold synrep, rep, synrep', ptsto_subset; intros.
    case_eq (d0 a); intros.
    - destruct p.
      eapply any_sep_star_ptsto in H1.
      pred_apply.
      safecancel.
      eassign (w, l).
      eassign l.
      cancel.
      firstorder.
    - destruct H.
      destruct_lift H.
      destruct_lift H2.
      destruct_lift H0.
      apply ptsto_valid' in H0.
      eapply mem_pred_absent_lm in H; eauto.
      eapply mem_pred_absent_hm in H2; eauto.
      congruence.

      unfold synpred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.

      unfold cachepred, ptsto_subset; intros.
      destruct (Map.find a0 (CSMap cs)); try destruct p; try destruct b; cancel.
  Qed.

  Theorem sync_synrep_helper_2 : forall cs d0 d a (F : @pred _ addr_eq_dec _) v,
    (F * a |+> v)%pred d ->
    synrep cs d0 d =p=> synrep cs d0 d * exists (F0 : @pred _ addr_eq_dec _) v0,
    [[ (F0 * a |+> v0)%pred d0 ]].
  Proof.
    unfold pimpl; intros.
    eapply sync_synrep_helper_1 in H; eauto; repeat deex.
    pred_apply; cancel.
  Qed.


  Theorem sync_ok : forall cs a,
    {< d0 d (F : rawpred) v0,
    PRE
      synrep cs d0 d * [[ sync_invariant F ]] *
      [[ (F * a |+> v0)%pred d ]]
    POST RET:cs exists d,
      synrep cs d0 d *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH
      exists cs', rep cs' d0
    >} sync a cs.
  Proof.
    intros.
    eapply pimpl_ok2.
    apply sync_ok'.
    intros; norml; unfold stars; simpl.
    rewrite sync_synrep_helper_2 by eauto.
    safecancel.
    eauto.
    step.
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
    safestep.
    step.
    cancel.
    cancel.
  Qed.


  Definition sync_two T a1 a2 (cs : cachestate) rx : prog T :=
    cs <- begin_sync cs;
    cs <- sync a1 cs;
    cs <- sync a2 cs;
    cs <- end_sync cs;
    rx cs.

  Theorem sync_two_ok : forall cs a1 a2,
    {< d (F : rawpred) v1 v2,
    PRE
      rep cs d * [[ sync_invariant F /\ (F * a1 |+> v1 * a2 |+> v2)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a1 |+> (fst v1, nil) * a2 |+> (fst v2, nil))%pred d' ]]
    CRASH
      exists cs' d, rep cs' d
    >} sync_two a1 a2 cs.
  Proof.
    unfold sync_two.
    prestep; norm. cancel. intuition simpl.
    2: eauto. eauto.
    safestep.
    safestep.
    prestep.
    cancel.
    step.
    cancel.
    cancel.
    cancel.
    cancel.
  Qed.


  (** crashes and recovery *)

  Lemma xform_cachepred_ptsto : forall m a vs,
    crash_xform (cachepred m a vs) =p=> 
      exists v, [[ In v (vsmerge vs) ]] * a |=> v.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros; try destruct p, b.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel; subst.
      apply in_inv in H1; simpl in *; intuition subst;
      apply in_cons; auto.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel.
  Qed.

  Lemma xform_mem_pred_cachepred : forall cs hm,
    crash_xform (mem_pred (cachepred cs) hm) =p=> 
      exists m', [[ possible_crash hm m' ]] *
      mem_pred (cachepred (Map.empty _)) m'.
  Proof.
    intros.
    rewrite xform_mem_pred.
    unfold mem_pred at 1.
    xform_norm; subst.

    rename hm_avs into l.
    revert H; revert l.
    induction l; simpl; intros.
    cancel.
    apply mem_pred_empty_mem.
    unfold possible_crash; intuition.

    inversion H; destruct a; subst; simpl in *.
    unfold mem_pred_one; simpl.

    rewrite IHl by auto.
    xform_norm.
    rewrite xform_cachepred_ptsto.
    norml; unfold stars; simpl; clear_norm_goal.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    apply possible_crash_upd; eauto.
    apply incl_nil.
  Qed.


  Lemma crash_xform_rep: forall cs m,
    crash_xform (rep cs m) =p=>
       exists m' cs', [[ possible_crash m m' ]] * rep cs' m'.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite xform_mem_pred_cachepred.
    cancel.
    eassign (cache0 (CSMaxCount cs)); cancel.
    all: unfold cache0; simpl; eauto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
  Qed.


  Lemma crash_xform_rep_pred : forall cs m (F : pred),
    F%pred m ->
    crash_xform (rep cs m) =p=>
    exists m' cs', rep cs' m' * [[ (crash_xform F)%pred m' ]].
  Proof.
    intros.
    rewrite crash_xform_rep.
    norm. cancel. split; auto.
    exists m; eauto.
  Qed.





End UCache.

Global Opaque UCache.write_array.
Global Opaque UCache.read_array.

