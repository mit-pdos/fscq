Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred.
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
    intros; rewrite sync_xform_listpred'; eauto.
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

Hint Resolve sync_invariant_arrayS.


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








