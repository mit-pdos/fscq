Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import PermArray.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.
Require Import ADestructPair DestructVarname.
Require Import Pred PermPredCrash.
Require Export PermCacheDef.

Import AddrMap.
Import Map.
Import ListNotations.

Set Implicit Arguments.

Lemma find_elements_hd:
  forall T a (v:T) l m,
    elements m = (a, v)::l ->
    find a m = Some v.
Proof.
  intros.
  apply find_1.
  assert (A: InA (fun a b =>  fst a = fst b /\ snd a = snd b)
                 (a,v) (elements m)).
  rewrite H; apply InA_cons_hd; auto.
  apply elements_2 in A; auto.
Qed.

Theorem sync_invariant_cachepred :
  forall cache a vs bm,
    sync_invariant (cachepred cache bm a vs).
Proof.
  unfold cachepred; intros.
  destruct (Map.find a cache); eauto.
  destruct p; destruct b; eauto.
Qed.

Theorem sync_invariant_synpred :
  forall cache bm a vs,
    sync_invariant (synpred cache bm a vs).
Proof.
  unfold synpred; intros.
  destruct (Map.find a cache); eauto.
  destruct p; destruct b; eauto.
Qed.

Hint Resolve sync_invariant_cachepred sync_invariant_synpred.

Theorem sync_invariant_rep :
  forall (cs: cachestate) m bm,
    sync_invariant (rep cs m bm).
Proof.
  unfold rep; intros; eauto.
Qed.

Hint Resolve sync_invariant_rep.

Theorem sync_invariant_synrep' :
  forall cs m bm,
  sync_invariant (synrep' cs m bm).
Proof.
  unfold synrep'; eauto.
Qed.

Hint Resolve sync_invariant_synrep'.

Theorem sync_invariant_synrep :
  forall cs mbase m bm,
    sync_invariant (synrep cs mbase m bm).
Proof.
  unfold synrep; eauto.
Qed.

Hint Resolve sync_invariant_synrep.


  Lemma cachepred_remove_invariant : forall a a' v cache bm,
    a <> a' -> cachepred cache bm a v =p=> cachepred (Map.remove a' cache) bm a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma cachepred_add_invariant : forall a a' v v' cache bm,
    a <> a' -> cachepred cache bm a v =p=> cachepred (Map.add a' v' cache) bm a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.

    Lemma synpred_remove_invariant : forall a a' v cache bm,
    a <> a' -> synpred cache bm a v =p=> synpred (Map.remove a' cache) bm a v.
  Proof.
    unfold synpred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma synpred_add_invariant : forall a a' v v' cache bm,
    a <> a' -> synpred cache bm a v =p=> synpred (Map.add a' v' cache) bm a v.
  Proof.
    unfold synpred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.


Lemma mem_pred_cachepred_remove_absorb : forall csmap d a w bm,
    d a = Some w ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred csmap bm) (mem_except d a) * a |+> w =p=>
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred (remove a csmap) bm) d.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.remove_eq_o by auto.
    cancel; eauto.
    rewrite mem_pred_pimpl_except; eauto.
    intros; apply cachepred_remove_invariant; eauto.
  Qed.


Lemma addr_clean_cachepred_remove_none :
  forall cs a d bm,
    find a (CSMap cs) = None ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred (CSMap cs) bm) d =p=>
      mem_pred (HighAEQ:= addr_eq_dec) (cachepred (remove a (CSMap cs)) bm) d.
Proof.
  intros.
  eapply mem_pred_pimpl; intros.
  destruct (Nat.eq_dec a a0); subst.
  unfold cachepred; simpl; cleanup.
  rewrite MapFacts.remove_eq_o; auto.
  eapply cachepred_remove_invariant; eauto.
Qed.  

Lemma addr_clean_cachepred_remove :
  forall cs a d F vs bm,
    addr_clean (CSMap cs) a ->
    (F * a |+> vs)%pred d ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred (CSMap cs) bm) d =p=>
      mem_pred (HighAEQ:= addr_eq_dec) (cachepred (remove a (CSMap cs)) bm) d.
  Proof.
    unfold addr_clean; intros.
    apply ptsto_subset_valid' in H0; cleanup.
    destruct H; cleanup.
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2; rewrite H.
      cancel.
      rewrite sep_star_comm.
      eapply mem_pred_cachepred_remove_absorb; eauto.
    - rewrite mem_pred_extract with (a := a) by eauto.
      unfold cachepred at 2; rewrite H.
      rewrite sep_star_comm.
      cancel.
      eapply mem_pred_cachepred_remove_absorb; eauto.
  Qed.

  Lemma addr_valid_ptsto_subset:
      forall a b cs d,
        addr_valid d (CSMap cs) ->
        find a (CSMap cs) = Some b ->
        exists F tb, (sep_star (AEQ:=addr_eq_dec) F (a|+>tb))%pred d.
    Proof.
      unfold rep, addr_valid; intros.
      destruct_lift H.
      assert (A: find a (CSMap cs) <> None ).
      intuition; congruence.
      apply MapFacts.in_find_iff in A.
      specialize (H _ A).
      destruct (d a) eqn:D; try congruence.
      do 2 eexists.
      erewrite <- ptsto_pimpl_ptsto_subset.
      apply any_sep_star_ptsto; eauto.
    Qed.

  Lemma size_valid_remove : forall cs a,
    size_valid cs ->
    Map.In a (CSMap cs) ->
    size_valid (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs - 1) (CSEvict cs)).
  Proof.
    unfold size_valid in *; intuition simpl.
    rewrite map_remove_cardinal by eauto; congruence.
    eapply le_trans.
    apply map_cardinal_remove_le; auto.
    auto.
  Qed.

  Lemma size_valid_remove_notin : forall cs a,
    size_valid cs ->
    ~ Map.In a (CSMap cs) ->
    size_valid (mk_cs (Map.remove a (CSMap cs)) (CSMaxCount cs) (CSCount cs) (CSEvict cs)).
  Proof.
    unfold size_valid in *; intuition simpl.
    rewrite Map.cardinal_1 in *.
    rewrite map_remove_not_in_elements_eq by auto. auto.
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

  Lemma size_valid_cache0 : forall cachesize,
    cachesize <> 0 ->
    size_valid (cache0 cachesize).
  Proof.
    unfold size_valid, cache0; simpl; intros.
    rewrite Map.cardinal_1.
    rewrite MapProperties.elements_empty.
    intuition.
  Qed.

  Lemma addr_valid_remove : forall d a cm,
    addr_valid d cm ->
    addr_valid d (Map.remove a cm).
  Proof.
    unfold addr_valid; intros.
    apply H.
    eapply MapFacts.remove_in_iff; eauto.
  Qed.

  Lemma addr_valid_empty : forall m,
    addr_valid m (Map.empty (handle * bool)).
  Proof.
    unfold addr_valid; intros.
    apply MapFacts.empty_in_iff in H.
    exfalso; auto.
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

  Lemma size_valid_add :
    forall cs evictor vv a,
    cardinal (CSMap cs) < CSMaxCount cs ->
    Map.find a (CSMap cs) = None ->
    size_valid cs ->
    size_valid (mk_cs (add a vv (CSMap cs)) (CSMaxCount cs) (CSCount cs + 1) evictor).
  Proof.
    unfold size_valid; intuition; simpl.

    destruct (find a0 (CSMap cs)) eqn:?; try congruence.
    rewrite map_add_cardinal. omega.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.

    destruct (Map.find a0 (CSMap cs)) eqn:?.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_cardinal. omega.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.
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

  
  Lemma mem_pred_cachepred_add_absorb_clean :
    forall csmap d a tb bm h,
      d a = Some tb ->
      bm h = None ->
     mem_pred (HighAEQ:= addr_eq_dec) (cachepred csmap bm) (mem_except d a) ✶ a |+> tb =p=>
     mem_pred (HighAEQ:= addr_eq_dec) (cachepred (Map.add a (h, false) csmap) (upd bm h (fst tb))) d.
  Proof.
    intros.
    eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
    unfold cachepred at 3.
    rewrite MapFacts.add_eq_o by auto.
    cancel; eauto.
    apply mem_pred_pimpl_except; eauto.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; eauto.
    destruct (find a0 csmap) eqn:D; cancel.
    destruct p_2; cancel;
    destruct (Nat.eq_dec h p_1); subst; try congruence;
    rewrite upd_ne; auto.
    apply upd_eq; auto.
  Qed.


Lemma rep_none_upd_pimpl:
  forall cs d bm h tb,
    bm h  = None ->
    rep cs d bm =p=> rep cs d (upd bm h tb).
Proof.
  unfold rep, cachepred; intros; cancel.
  eapply mem_pred_pimpl; intros.
  destruct (find a (CSMap cs)); [| cancel];
  destruct p; destruct b;
  cancel;
  destruct (Nat.eq_dec h0 h); subst;
  try congruence; rewrite upd_ne; auto.
Qed.

  Lemma size_valid_add_in : forall cs evictor vv v a,
    Map.find a (CSMap cs) = Some v ->
    size_valid cs ->
    size_valid (mk_cs (Map.add a vv (CSMap cs)) (CSMaxCount cs) (CSCount cs) evictor).
  Proof.
    unfold size_valid; intuition; simpl.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
    rewrite map_add_dup_cardinal; auto.
    eexists; eapply MapFacts.find_mapsto_iff; eauto.
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
    List.In v0 (vsmerge (w, l')) ->
    incl l (vsmerge (w, l')).
  Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H0); intuition.
    specialize (H _ H0); intuition subst; auto.
  Qed.

  Lemma incl_vsmerge_in' : forall w v0 l l',
    incl l (vsmerge (w, (vsmerge (v0, l')))) ->
    List.In v0 l' ->
    incl l (vsmerge (w, l')).
  Proof.
    unfold vsmerge, incl; simpl; intuition subst.
    specialize (H _ H1); intuition subst.
    right; auto.
  Qed.

  Lemma incl_vsmerge_in'' : forall a v l,
    List.In v l ->
    incl a (vsmerge (v, l)) ->
    incl a l.
  Proof.
    unfold vsmerge, incl; intuition simpl in *.
    specialize (H0 _ H1); intuition subst; auto.
  Qed.

Hint Resolve incl_vsmerge_in incl_vsmerge_in' incl_vsmerge_in''.

  Lemma in_vsmerge_hd : forall w l,
    List.In w (vsmerge (w, l)).
  Proof.
    unfold vsmerge; intuition.
  Qed.

  Lemma in_incl_trans: forall A (a b : list A) x,
    incl a b ->
    List.In x a ->
    List.In x b.
  Proof.
    unfold incl; intros.
    specialize (H _ H0); auto.
  Qed.

  Lemma incl_vsmerge_trans: forall a v l l',
    incl a (vsmerge (v, l')) ->
    incl l' l ->
    incl a (vsmerge (v, l)).
  Proof.
    unfold incl, vsmerge; simpl; intros.
    specialize (H _ H1); intuition.
  Qed.

  Lemma incl_vsmerge_in_trans : forall a v l l',
    List.In v l ->
    incl l' l ->
    incl a (vsmerge (v, l')) ->
    incl a l.
  Proof.
    intros.
    eapply incl_vsmerge_in''; eauto.
    eapply incl_vsmerge_trans; eauto.
  Qed.

Hint Resolve in_vsmerge_hd incl_vsmerge_trans incl_vsmerge_in_trans.




  Lemma cachepred_synpred : forall cm bm a vs,
    cachepred cm bm a vs =p=> exists vs', synpred cm bm a vs' *
      [[ fst vs' = fst vs /\ incl (snd vs') (snd vs) /\
         (addr_clean cm a -> snd vs' = nil) ]].
  Proof.
    unfold cachepred, synpred, addr_clean; intros.
    destruct (Map.find a cm) eqn:?.
    destruct p, b; cancel; auto.
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

  Lemma listpred_cachepred_synpred : forall l cm bm,
    listpred (fun av => cachepred cm bm (fst av) (snd av)) l =p=> exists l',
    listpred (fun av => synpred cm bm (fst av) (snd av)) l' *
    [[ Forall2 avs_match l l' /\ Forall (nil_if_clean cm) l' ]].
  Proof.
    induction l; simpl; intros.
    cancel; simpl; auto.
    rewrite cachepred_synpred, IHl.
    safecancel.
    eassign ((a_1, (t1, l1)) :: l'); simpl.
    cancel.
    constructor; auto.
    unfold avs_match; simpl; intuition.
    auto.
  Qed.

  Lemma avs_match_map_fst_eq : forall l l',
    Forall2 avs_match l l' ->
    List.map fst l' = List.map fst l.
  Proof.
    unfold avs_match; induction 1; simpl; auto.
    f_equal; auto.
    destruct x, y; intuition.
  Qed.

  Lemma avs2mem_mem_match : forall V l l',
    List.map fst l' = List.map fst l ->
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
    destruct v, v0; intuition; simpl in *; subst; repeat deex.
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

  Lemma synpred_cachepred_sync : forall vs cm bm a,
    sync_xform (synpred cm bm a vs) =p=> cachepred cm bm a vs.
  Proof.
    unfold cachepred, synpred; intros.
    rewrite sync_xform_exists_comm.
    apply pimpl_exists_l; intro vs0.
    rewrite sync_xform_sep_star_dist.
    destruct vs0 as [v0 l0].
    destruct (Map.find a cm) eqn:?; try destruct p, b.
    rewrite sync_xform_exists_comm; unfold pimpl; intros.
    destruct_lift H.
    rewrite sync_xform_sep_star_dist in H.
    repeat rewrite sync_xform_lift_empty in H;
    rewrite sync_xform_ptsto_subset_precise in H.
    destruct_lift H; cleanup.
    pred_apply; cancel.
    unfold ptsto_subset; cancel; subst.

    rewrite sync_xform_sep_star_dist.
    repeat rewrite sync_xform_lift_empty.
    rewrite sync_xform_ptsto_subset_precise.
    unfold ptsto_subset; cancel; subst.
    rewrite sync_xform_lift_empty.
    rewrite sync_xform_ptsto_subset_precise.
    unfold ptsto_subset; cancel; subst.
  Qed.
  
  Lemma sync_xform_listpred_synpred_cachepred : forall l cm bm,
    sync_xform (listpred (fun x => synpred cm bm (fst x) (snd x)) l) =p=>
    listpred (fun x => cachepred cm bm (fst x) (snd x)) l.
  Proof.
    intros.
    rewrite sync_xform_listpred'; eauto.
    intros; eapply synpred_cachepred_sync.
  Qed.
  
  Lemma rep_synrep_split : forall cs (d: tagged_disk) bm F,
    rep cs d bm /\ (exists d', synrep' cs d' bm * [[ F d' ]]) =p=>
    (exists d', (rep cs d bm ⋀ synrep' cs d' bm) * [[ F d' ]]).
  Proof.
    intros.
    rewrite pimpl_and_r_exists.
    unfold pimpl; intros. destruct H. destruct H. destruct_lift H0.
    exists x.
    eapply sep_star_lift_apply'; eauto.
    split; eauto.
  Qed.

  Lemma synrep_rep : forall cs d0 d bm,
    synrep cs d0 d bm =p=> rep cs d0 bm.
  Proof.
    unfold synrep; intros.
    apply pimpl_l_and; eauto.
  Qed.


  Lemma nil_if_clean_synced : forall l a cm vs,
    Forall (nil_if_clean cm) l ->
    addr_clean cm a ->
    avs2mem addr_eq_dec l a = Some vs ->
    NoDup (List.map fst l) ->
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


  Lemma rep_synrep : forall (F : rawpred) d0 cs bm,
    F d0 ->
    sync_invariant F ->
    rep cs d0 bm =p=> exists d, synrep cs d0 d bm * 
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

  Lemma sync_invariant_sync_xform:
  forall P,
    sync_invariant (sync_xform P).
Proof.
  unfold sync_xform, sync_invariant; simpl; intros.
  cleanup.
  exists x.
  intuition; apply possible_sync_after_sync; auto.
Qed.


Notation arrayS := (arrayN ptsto_subset).

Lemma sync_invariant_arrayS :
  forall l a, sync_invariant (arrayS a l).
Proof.
  induction l; intros; simpl; eauto.
Qed.


 Lemma mem_pred_cachepred_refl_arrayN : forall l start bm m,
    arrayN (@ptsto _ _ _) start l m ->
    mem_pred (cachepred (Map.empty (handle * bool)) bm) m m.
  Proof.
    induction l; simpl; intros.
    - apply emp_empty_mem_only in H; subst.
      unfold mem_pred. exists nil; simpl.
      eapply pimpl_apply; [ | apply emp_empty_mem ].
      cancel.
      constructor.
    - unfold mem_pred in *.
      apply ptsto_mem_except in H as H'.
      specialize (IHl _ bm _ H').
      destruct IHl.
      destruct_lift H0.
      destruct a.
      exists ((start, (t0, l0)) :: x).
      simpl.
      unfold mem_pred_one at 1. unfold cachepred at 1.
      rewrite MapFacts.empty_o; simpl.

      eapply pimpl_apply.
      2: eapply mem_except_ptsto.
      3: eassumption.
      2: apply ptsto_valid in H; eauto.
      rewrite ptsto_pimpl_ptsto_subset.
      cancel.

      constructor; auto.
      eapply avs2mem_none_notin; eauto.
      denote avs2mem as Heq; rewrite <- Heq.
      apply mem_except_eq.
      cbn.
      denote avs2mem as Heq; setoid_rewrite <- Heq.
      rewrite upd_mem_except.
      rewrite upd_nop; eauto.
      eapply ptsto_valid; eauto.
  Qed.

  Lemma arrayS_arrayN : forall l start,
    arrayS start l =p=> exists l', arrayN (@ptsto _ _ _) start l'.
  Proof.
    induction l; simpl; intros.
    exists nil; simpl; eauto.
    rewrite IHl.
    unfold ptsto_subset.
    norml; unfold stars; simpl.
    exists ((t0, old) :: l'); simpl.
    pred_apply; cancel.
  Qed.

    
Lemma mem_pred_cachepred_refl_arrayS : forall l start bm m,
    arrayS start l m ->
    mem_pred (cachepred (Map.empty (handle * bool)) bm) m m.
  Proof.
    intros.
    apply arrayS_arrayN in H.
    destruct_lift H.
    eapply mem_pred_cachepred_refl_arrayN; eauto.
  Qed.

  Lemma sync_xform_arrayS : forall l start,
    sync_xform (arrayS start l) =p=> arrayS start l.
  Proof.
    induction l; simpl; intros.
    rewrite sync_xform_emp; cancel.
    rewrite sync_xform_sep_star_dist.
    rewrite sync_xform_ptsto_subset_preserve.
    rewrite IHl.
    cancel.
  Qed.


  Lemma block_mem_subset_mem_pred_cachepred:
    forall bm bm' cs d,
      bm c= bm' ->
      mem_pred (HighAEQ:=addr_eq_dec) (cachepred (CSMap cs) bm) d
      =p=> mem_pred (HighAEQ:=addr_eq_dec) (cachepred (CSMap cs) bm') d.
  Proof.
    intros.
    apply mem_pred_pimpl; intros.
    unfold cachepred.
    destruct (find a (CSMap cs)); cancel.
    destruct p_2; cancel;
    specialize (H p_1); cleanup; auto.
  Qed.
  
  Lemma block_mem_subset_rep:
    forall bm bm' cs d,
      bm c= bm' ->
          rep cs d bm =p=> rep cs  d bm'.
  Proof.
    unfold rep; intros; cancel.
    apply block_mem_subset_mem_pred_cachepred; eauto.
  Qed.
  
  Hint Resolve block_mem_subset_mem_pred_cachepred block_mem_subset_rep.
  
  Theorem sync_synrep_helper_1 : forall m cs d0 d a (F : @pred _ addr_eq_dec _) bm v,
    synrep cs d0 d bm m ->
    (F * a |+> v)%pred d ->
    exists (F0 : @pred _ addr_eq_dec _) v0,
    (F0 * a |+> v0)%pred d0.
  Proof.
    unfold synrep, rep, synrep', ptsto_subset; intros.
    case_eq (d0 a); intros.
    - destruct v0.
      eapply any_sep_star_ptsto in H1.
      pred_apply.
      safecancel.
      eassign (t0, l).
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

  Theorem sync_synrep_helper_2 : forall cs d0 d bm a (F : @pred _ addr_eq_dec _) v,
    (F * a |+> v)%pred d ->
    synrep cs d0 d bm =p=> synrep cs d0 d bm * exists (F0 : @pred _ addr_eq_dec _) v0,
    [[ (F0 * a |+> v0)%pred d0 ]].
  Proof.
    unfold pimpl; intros.
    eapply sync_synrep_helper_1 in H; eauto; repeat deex.
    pred_apply; cancel.
    eassign F0; cancel.
  Qed.

  
   Lemma sync_xform_cachepred : forall m bm a vs,
    sync_xform (cachepred m bm a vs) =p=> 
      exists v, [[ List.In v (vsmerge vs) ]] * a |=> v.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros; try destruct p, b.
    - rewrite sync_xform_exists_comm.
      apply pimpl_exists_l; intro.
      repeat rewrite sync_xform_sep_star_dist, sync_xform_lift_empty.
      rewrite sync_xform_ptsto_subset_precise; simpl.
      cancel.
    - rewrite sync_xform_sep_star_dist, sync_xform_lift_empty.
      rewrite sync_xform_ptsto_subset_precise; simpl.
      cancel.
    - rewrite sync_xform_ptsto_subset_precise; cancel.
  Qed.



Theorem sync_xform_mem_pred : forall prd (hm : rawdisk),
  sync_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => sync_xform (prd a v)) hm.
Proof.
  unfold mem_pred; intros; split.
  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.

  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  apply pimpl_exists_r; eexists.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.
Qed.

  
  Lemma sync_xform_mem_pred_cachepred : forall cm bm m,
    sync_xform (mem_pred (HighAEQ:=addr_eq_dec) (cachepred cm bm) m) =p=> exists m',
      mem_pred (HighAEQ:=addr_eq_dec) (cachepred (Map.empty (handle * bool)) bm) m' * [[ possible_crash m m' ]].
  Proof.
    intros.
    rewrite sync_xform_mem_pred.
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
    rewrite sync_xform_cachepred.
    norml; unfold stars; simpl.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    cleanup.
    apply possible_crash_upd; eauto.
    apply possible_crash_upd; eauto.
    unfold vsmerge; simpl; auto.
  Qed.



 Lemma xform_cachepred_ptsto : forall m bm a vs,
    crash_xform (cachepred m bm a vs) =p=> 
      exists v, [[ List.In v (vsmerge vs) ]] * a |=> v.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros; try destruct p, b.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel; subst.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel.
    - xform_norm; subst.
      rewrite crash_xform_ptsto_subset.
      cancel.
  Qed.


Theorem xform_listpred : forall V (l : list V) prd,
  crash_xform (listpred prd l) <=p=> listpred (fun x => crash_xform (prd x)) l.
Proof.
  induction l; simpl; intros; split; auto; xform_dist; auto.
  rewrite IHl; auto.
  rewrite IHl; auto.
Qed.


Lemma crash_xform_pprd : forall A B (prd : A -> B -> rawpred),
  (fun p => crash_xform (pprd prd p)) =
  (pprd (fun x y => crash_xform (prd x y))).
Proof.
  unfold pprd, prod_curry, crash_xform; intros.
  apply functional_extensionality; intros; destruct x; auto.
Qed.

Theorem xform_listmatch : forall A B (a : list A) (b : list B) prd,
  crash_xform (listmatch prd a b) <=p=> listmatch (fun x y => crash_xform (prd x y)) a b.
Proof.
  unfold listmatch; intros; split; xform_norm;
  rewrite xform_listpred; cancel;
  rewrite crash_xform_pprd; auto.
Qed.

Theorem xform_listpred_idem_l : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) =p=> prd e) ->
  crash_xform (listpred prd l) =p=> listpred prd l.
Proof.
  induction l; simpl; intros; auto.
  xform_dist.
  rewrite H.
  rewrite IHl; auto.
Qed.


Theorem xform_listpred_idem_r : forall V (l : list V) prd,
  (forall e,  prd e =p=> crash_xform (prd e)) ->
  listpred prd l =p=> crash_xform (listpred prd l).
Proof.
  induction l; simpl; intros; auto.
  xform_dist; auto.
  xform_dist.
  rewrite <- H.
  rewrite <- IHl; auto.
Qed.

Theorem xform_listpred_idem : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) <=p=> prd e) ->
  crash_xform (listpred prd l) <=p=> listpred prd l.
Proof.
  split.
  apply xform_listpred_idem_l; intros.
  apply H.
  apply xform_listpred_idem_r; intros.
  apply H.
Qed.

Theorem xform_listmatch_idem_l : forall A B (a : list A) (b : list B) prd,
  (forall a b, crash_xform (prd a b) =p=> prd a b) ->
  crash_xform (listmatch prd a b) =p=> listmatch prd a b.
Proof.
  unfold listmatch; intros.
  xform_norm; cancel.
  apply xform_listpred_idem_l; intros.
  destruct e; cbn; auto.
Qed.

Theorem xform_listmatch_idem_r : forall A B (a : list A) (b : list B) prd,
  (forall a b,  prd a b =p=> crash_xform (prd a b)) ->
  listmatch prd a b =p=> crash_xform (listmatch prd a b).
Proof.
  unfold listmatch; intros.
  cancel.
  xform_normr.
  rewrite <- xform_listpred_idem_r; cancel.
  auto.
Qed.

Theorem xform_listmatch_idem : forall A B (a : list A) (b : list B) prd,
  (forall a b, crash_xform (prd a b) <=p=> prd a b) ->
  crash_xform (listmatch prd a b) <=p=> listmatch prd a b.
Proof.
  split.
  apply xform_listmatch_idem_l; auto.
  apply H.
  apply xform_listmatch_idem_r; auto.
  apply H.
Qed.

Lemma xform_listpred_ptsto : forall l,
  crash_xform (listpred (fun a => a |->?) l) =p=>
               listpred (fun a => a |->?) l.
Proof.
  induction l; simpl.
  rewrite crash_invariant_emp; auto.
  xform_dist.
  rewrite crash_xform_ptsto_exis, IHl.
  auto.
Qed.

Lemma xform_listpred_ptsto_fp : forall FP,
  (forall a, crash_xform (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
  forall l,
  crash_xform (listpred (fun a => exists v, a |-> v * [[ FP v ]]) l) =p=>
               listpred (fun a => exists v, a |-> v * [[ FP v ]]) l.
Proof.
  induction l; simpl.
  rewrite crash_invariant_emp; auto.
  xform_dist.
  rewrite H.
  rewrite IHl.
  cancel.
Qed.

Theorem sync_invariant_listpred : forall T prd (l : list T),
  (forall x, sync_invariant (prd x)) ->
  sync_invariant (listpred prd l).
Proof.
  induction l; simpl; eauto.
Qed.

Hint Resolve sync_invariant_listpred.

Theorem sync_xform_listpred : forall V (l : list V) prd,
  sync_xform (listpred prd l) <=p=> listpred (fun x => sync_xform (prd x)) l.
Proof.
  induction l; simpl; intros; split; auto.
  apply sync_xform_emp.
  apply sync_xform_emp.
  rewrite sync_xform_sep_star_dist.
  rewrite IHl; auto.
  rewrite sync_xform_sep_star_dist.
  rewrite IHl; auto.
Qed.


Lemma sync_xform_listpred' : forall T (l : list T) p q,
  (forall x, sync_xform (p x) =p=> q x) ->
  sync_xform (listpred p l) =p=> listpred q l.
Proof.
  induction l; simpl; intros; auto.
  apply sync_xform_emp.
  repeat rewrite sync_xform_sep_star_dist.
  rewrite IHl by eauto.
  rewrite H; auto.
Qed.

Theorem xform_mem_pred : forall prd (hm : rawdisk),
  crash_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => crash_xform (prd a v)) hm.
Proof.
  unfold mem_pred; intros; split.
  xform_norm; subst.
  rewrite xform_listpred.
  cancel.

  cancel; subst.
  xform_normr; cancel.
  rewrite xform_listpred.
  cancel.
  eauto.
Qed.

Theorem sync_invariant_mem_pred : forall HighAT HighAEQ HighV (prd : HighAT -> HighV -> _) hm,
  (forall a v, sync_invariant (prd a v)) ->
  sync_invariant (@mem_pred _ _ _ _ HighAEQ _ prd hm).
Proof.
  unfold mem_pred; eauto.
Qed.
  
  Lemma xform_mem_pred_cachepred : forall cs bm hm,
    crash_xform (mem_pred (HighAEQ:=addr_eq_dec) (cachepred cs bm) hm) =p=> 
      exists m', [[ possible_crash hm m' ]] *
      mem_pred (HighAEQ:=addr_eq_dec) (cachepred (Map.empty _) bm) m'.
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
    norml; unfold stars; simpl.
    apply pimpl_exists_r.
    exists (upd m' n (v, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3; unfold ptsto_subset.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    cleanup; apply possible_crash_upd; eauto.
    cleanup; apply possible_crash_upd; eauto.
    unfold vsmerge; simpl; eauto.
  Qed.


  Lemma crash_xform_rep: forall cs bm m,
    crash_xform (rep cs m bm) =p=>
       exists m' cs', [[ possible_crash m m' ]] * rep cs' m' bm.
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

  Lemma crash_xform_rep': forall cs bm m,
    crash_xform (rep cs m bm) =p=>
       exists m' cs' bm', [[ possible_crash m m' ]] * [[ bm c= bm' ]] * rep cs' m' bm'.
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


  Lemma crash_xform_rep_pred : forall cs m bm (F : pred),
    F%pred m ->
    crash_xform (rep cs m bm) =p=>
    exists m' cs', rep cs' m' bm * [[ (crash_xform F)%pred m' ]].
  Proof.
    intros.
    rewrite crash_xform_rep.
    norm. cancel. split; auto.
    exists m; eauto.
  Qed.

  Lemma listpred_cachepred_mem_except : forall a v l m buf bm,
    listpred (mem_pred_one (cachepred buf bm)) ((a, v) :: l) m ->
    listpred (mem_pred_one (cachepred buf bm)) l (mem_except m a).
  Proof.
    unfold mem_pred_one; simpl; intros.
    unfold cachepred at 1 in H.
    destruct (Map.find a buf) eqn: Heq; try destruct p, b;
    unfold ptsto_subset in H; destruct_lift H;
    eapply ptsto_mem_except; pred_apply; eauto.
  Qed.


  Lemma mem_pred_cachepred_refl : forall m m' m'' cm bm,
    mem_pred (HighAEQ:=addr_eq_dec) (cachepred cm bm) m' m'' ->
    mem_match m m' ->
    mem_pred (HighAEQ:=addr_eq_dec) (cachepred (Map.empty (handle * bool)) bm) m m.
  Proof.
    unfold mem_pred; intros.
    destruct H; destruct_lift H.
    generalize dependent m''.
    generalize dependent m.
    generalize dependent x.
    induction x; intros.
    - exists nil.
      rewrite listpred_nil in *.
      apply sep_star_assoc.
      apply lift_impl; intros.
      simpl; auto.
      cbn in *; subst.
      assert (@emp _ addr_eq_dec _ m) by firstorder.
      apply lift_impl; intros; auto.
      apply emp_empty_mem_only; auto.

    - destruct a.
      inversion H2; subst.
      edestruct IHx; eauto.
      + rewrite notindomain_mem_eq with (a := n).
        erewrite mem_except_upd.
        apply mem_match_except; eauto.
        apply avs2mem_notindomain; eauto.
      + eapply listpred_cachepred_mem_except; eauto.
      + destruct (mem_match_cases n H0).
        exists x0.
        destruct H3.
        rewrite mem_except_none in H1; eauto.

        do 3 destruct H3.
        exists ((n, x1) :: x0).
        destruct_lift H1.
        apply sep_star_assoc.
        apply lift_impl; intros.
        apply NoDup_cons; eauto.
        eapply avs2mem_none_notin; eauto.
        denote mem_except as Hx; rewrite <- Hx.
        apply mem_except_eq.

        apply lift_impl; intros.
        cbn; denote mem_except as Hx; setoid_rewrite <- Hx.
        rewrite upd_mem_except.
        rewrite upd_nop; auto.

        unfold mem_pred_one, cachepred at 1; simpl.
        unfold ptsto_subset; simpl.
        apply pimpl_exists_r_star.
        exists (snd x1).
        apply sep_star_assoc.
        destruct x1; simpl in *.
        apply mem_except_ptsto; eauto.
        unfold mem_pred_one in H1; simpl in *.
        pred_apply' H1; cancel.
  Qed.

 
  Lemma possible_crash_mem_match : forall (m1 m2 : rawdisk),
    possible_crash m1 m2 ->
    @mem_match _ _ addr_eq_dec m1 m2.
  Proof.
    unfold possible_crash, mem_match; intuition.
    specialize (H a); intuition.
    repeat deex; congruence.
    specialize (H a); intuition.
    repeat deex; congruence.
  Qed.

  Lemma listpred_cachepred_notin : forall cs bm l m a,
    ~ List.In a (List.map fst l) ->
    listpred (mem_pred_one (cachepred cs bm)) l m ->
    m a = None.
  Proof.
    induction l; intros; eauto.
    destruct a; subst; simpl in *; intuition.
    unfold mem_pred_one at 1, cachepred at 1 in H0; simpl in *.
    destruct (Map.find n cs) eqn: Heq; try destruct p, b;
    unfold ptsto_subset in *; destruct_lifts;
    eapply notindomain_mem_except with (a' := n); eauto;
    apply IHl; eauto;
    eapply ptsto_mem_except; eauto.
  Qed.

  Lemma mem_pred_cachepred_none : forall m1 m2 cs bm a,
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred cs bm) m1 m2 ->
    m1 a = None ->
    m2 a = None.
  Proof.
    unfold mem_pred; intros.
    destruct_lift H; subst.
    rename dummy into l.
    apply avs2mem_none_notin in H0 as Hx.
    erewrite listpred_cachepred_notin with (m := m2); eauto.
  Qed.

  Lemma mem_pred_cachepred_some : forall m1 m2 cs bm a v,
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred cs bm) m1 m2 ->
    synced_mem m1 ->
    m1 a = Some v ->
    m2 a = Some v.
  Proof.
    intros.
    specialize (H0 a); intuition try congruence; repeat deex.
    rewrite H0 in H1; inversion_clear H1; subst.
    eapply mem_pred_extract in H; eauto.
    unfold cachepred in H at 2.
    destruct (Map.find a cs) eqn:?; try destruct p, b;
    unfold ptsto_subset in H; destruct_lift H;
    denote incl as Hx; apply incl_in_nil in Hx; subst.
    intuition.
    eapply ptsto_valid'; eauto.
    eapply ptsto_valid'; eauto.
  Qed.

  Lemma mem_pred_cachepred_eq : forall m1 m2 cs bm,
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred cs bm) m1 m2 ->
    synced_mem m1 ->
    m1 = m2.
  Proof.
    intros.
    apply functional_extensionality; intros.
    destruct (m1 x) eqn: Heq.
    erewrite mem_pred_cachepred_some; eauto.
    eapply mem_pred_cachepred_none in H; eauto.
  Qed.

  Lemma mem_pred_possible_crash_trans : forall m m1 m2 cs bm,
    possible_crash m m1 ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred cs bm) m1 m2 ->
    possible_crash m1 m2.
  Proof.
    intros.
    replace m2 with m1.
    apply possible_crash_refl.
    eapply possible_crash_synced; eauto.
    eapply mem_pred_cachepred_eq; eauto.
    eapply possible_crash_synced; eauto.
  Qed.


  Lemma crash_xform_rep_r: forall m m' cs' bm,
    possible_crash m m' ->
    rep cs' m' bm =p=> crash_xform (rep (cache0 (CSMaxCount cs')) m bm).
  Proof.
    unfold rep; intros.
    cancel.
    xform_normr.
    cancel.
    unfold pimpl, crash_xform; intros.
    eexists; split.
    eapply mem_pred_cachepred_refl; eauto.
    apply possible_crash_mem_match; auto.
    eapply possible_crash_trans.
    eauto.
    eapply mem_pred_possible_crash_trans; eauto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
  Qed.

  Lemma crash_xform_rep_r_pred : forall cs m bm (F : pred),
    (crash_xform F)%pred m ->
    rep cs m bm =p=> exists m', crash_xform (rep (cache0 (CSMaxCount cs)) m' bm) * [[ F m' ]].
  Proof.
    intros.
    unfold crash_xform in H; deex.
    rewrite crash_xform_rep_r by eauto.
    cancel.
  Qed.




  Theorem sync_invariant_arrayN_subset : forall vs a,
    sync_invariant (arrayN ptsto_subset a vs).
  Proof.
    induction vs; simpl; auto.
  Qed.

  Lemma arrayN_subset_oob': forall l a i m,
    i >= length l
    -> arrayN ptsto_subset a l m
    -> m (a + i) = None.
  Proof.
    induction l; intros; auto; simpl in *.
    destruct (eq_nat_dec i 0); auto.
    subst; simpl in *; omega.

    unfold sep_star in H0; rewrite sep_star_is in H0; unfold sep_star_impl in H0.
    repeat deex.
    unfold mem_union.
    unfold ptsto_subset in H2.
    destruct_lift H2.
    unfold ptsto in H1; destruct H1.
    pose proof (IHl (S a0) (i - 1)).
    replace (S a0 + (i - 1)) with (a0 + i) in H3 by omega.
    destruct (m1 (a0 + i)) eqn:?.
    contradict Heqo.
    rewrite H2; try congruence.
    omega.
    apply H3.
    omega.
    auto.
  Qed.

  Lemma arrayN_subset_oob: forall l i m,
    i >= length l
    -> arrayN ptsto_subset 0 l m
    -> m i = None.
  Proof.
    intros.
    replace i with (0 + i) by omega.
    eapply arrayN_subset_oob'; eauto.
  Qed.


  Lemma crash_xform_arrayN_subset: forall l st,
    crash_xform (arrayN ptsto_subset st l) =p=>
      exists l', [[ possible_crash_list l l' ]] *
      arrayN ptsto_subset st (synced_list l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto. auto.

    xform.
    rewrite IHl.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset, synced_list.
    cancel; [ instantiate (1 := v' :: l') | .. ]; simpl; auto; try cancel;
    destruct i; simpl; auto;
    destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_subset_r: forall l l' st,
    possible_crash_list l' l ->
    arrayN ptsto_subset st (synced_list l) =p=>
     crash_xform (arrayN ptsto_subset st l').
  Proof.
    unfold possible_crash_list.
    induction l; simpl; intros; auto.
    - intuition; destruct l'; simpl in *; try congruence.
      apply crash_invariant_emp_r.
    - intuition; destruct l'; simpl in *; try congruence.
      pose proof (H1 0) as H1'. simpl in H1'.
      rewrite IHl.
      rewrite crash_xform_sep_star_dist.
      rewrite <- crash_xform_ptsto_subset_r with (v := a) by (apply H1'; omega).
      rewrite ptsto_subset_pimpl_ptsto.
      apply pimpl_refl.
      intuition.
      specialize (H1 (S i)). simpl in H1. apply H1. omega.
  Qed.

  Hint Resolve incl_refl.

  Lemma crash_xform_synced_arrayN_subset: forall l st,
    Forall (fun x => snd x = nil) l ->
    crash_xform (arrayN ptsto_subset st l) =p=> arrayN ptsto_subset st l.
  Proof.
    induction l; simpl; auto; intros.
    xform.
    rewrite IHl.
    cancel; subst.
    rewrite crash_xform_ptsto_subset; unfold ptsto_subset.
    cancel.
    inversion H; simpl in *; subst; auto.
    inversion H; simpl in *; subst.
    inversion H0.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma crash_xform_arrayN_subset_combine_nils: forall (l : list tagged_block) st,
    crash_xform (arrayN ptsto_subset st (List.combine l (repeat nil (length l)))) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

  Lemma crash_xform_arrayN_subset_synced: forall (l : list tagged_block) st,
    crash_xform (arrayN ptsto_subset st (synced_list l)) =p=>
    arrayN ptsto_subset st (List.combine l (repeat nil (length l))).
  Proof.
    intros.
    apply crash_xform_synced_arrayN_subset.
    rewrite Forall_forall; intros.
    induction l; simpl in *.
    inversion H.
    inversion H; subst; simpl; auto.
  Qed.

  Lemma write_array_xcrash_ok : forall cs d bm F a i v vs,
    (F * arrayN ptsto_subset a vs)%pred d ->
    i < length vs ->
    crash_xform (rep cs d bm) =p=>
    crash_xform (exists cs' d', rep cs' d' bm *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]).
  Proof.
    intros.
    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.

    edestruct arrayN_selN_subset with (a := a + i); eauto; try omega; intuition.
    replace (a + i - a) with i in * by omega.
    edestruct possible_crash_sel_exis; eauto; intuition.
    
    xcrash.
    2: apply arrayN_subset_memupd; eauto.
    rewrite <- crash_xform_rep_r; eauto.
    unfold rep; cancel; eauto.    
    eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    apply incl_tl.
    apply incl_cons2; auto.

     2: apply arrayN_subset_memupd; eauto.
    rewrite <- crash_xform_rep_r; eauto.
    unfold rep; cancel; eauto.    
    eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    apply incl_tl.
    apply incl_cons2; auto.    
  Qed.

  Lemma vsupd_range_xcrash_firstn' : forall l F a n vs cs' d' bm',
    (F * arrayN ptsto_subset a (vsupd_range vs (firstn n l)))%pred d' ->
    length l <= length vs ->
    crash_xform (rep cs' d' bm') =p=>
    crash_xform (exists cs d, rep cs d bm' * 
      [[ (F * arrayN ptsto_subset a (vsupd_range vs l))%pred d ]]).
  Proof.
    induction l using rev_ind; simpl; intros.
    rewrite firstn_nil in H; cbn in *.
    apply crash_xform_pimpl; cancel.
    destruct (le_dec n (S (length l))).
    destruct (le_dec n (length l)).
    - rewrite app_length in *; simpl in *.
      rewrite firstn_app_l in H by auto.
      rewrite IHl; eauto; try omega.
      rewrite vsupd_range_app_tl; eauto.
      xform_norm.
      rewrite write_array_xcrash_ok with (i := length l); eauto.
      2: rewrite vsupd_range_length; try omega; rewrite firstn_length, app_length, Nat.min_l; simpl; omega.
      xform_norm; cancel.
      apply crash_xform_pimpl.
      cancel.
    - assert (n = length l + 1) by omega; subst.
      rewrite app_length in *; simpl in *.
      rewrite firstn_oob in H by (rewrite app_length; simpl; omega).
      apply crash_xform_pimpl.
      cancel.
    - rewrite firstn_oob in H.
      apply crash_xform_pimpl; cancel.
      rewrite app_length; simpl; omega.
  Qed.

  Lemma vsupd_range_xcrash_firstn : forall F a n l vs bm,
    length l <= length vs ->
    crash_xform (exists cs' d', rep cs' d' bm *
      [[ (F * arrayN ptsto_subset a (vsupd_range vs (firstn n l)))%pred d' ]]) =p=>
    crash_xform (exists cs d, rep cs d bm * 
      [[ (F * arrayN ptsto_subset a (vsupd_range vs l))%pred d ]]).
  Proof.
    intros.
    xform_norm.
    erewrite vsupd_range_xcrash_firstn'; eauto.
    xform_norm.
    do 2 (xform_normr; cancel).
  Qed.
