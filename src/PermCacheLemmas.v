Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred.
Require Import WordAuto.
Require Import Omega.
Require Import AsyncDisk.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.
Require Export PermCacheDef.
Require Import ADestructPair DestructVarname.

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

Lemma mem_pred_cachepred_remove_absorb : forall csmap d a w bm,
    d a = Some w ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred csmap bm) (mem_except d a) * a |-> w =p=>
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
    find a (HCSMap cs) = None ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred (HCSMap cs) bm) d =p=>
      mem_pred (HighAEQ:= addr_eq_dec) (cachepred (remove a (HCSMap cs)) bm) d.
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
    addr_clean (HCSMap cs) a ->
    (F * a |-> vs)%pred d ->
    mem_pred (HighAEQ:= addr_eq_dec) (cachepred (HCSMap cs) bm) d =p=>
      mem_pred (HighAEQ:= addr_eq_dec) (cachepred (remove a (HCSMap cs)) bm) d.
  Proof.
    unfold addr_clean; intros.
    apply ptsto_valid' in H0; cleanup.
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

  Lemma addr_valid_ptsto_exists:
      forall a b cs d,
        addr_valid d (HCSMap cs) ->
        find a (HCSMap cs) = Some b ->
        exists F tb, (sep_star (AEQ:=addr_eq_dec) F (a|->tb))%pred d.
    Proof.
      unfold rep, addr_valid; intros.
      destruct_lift H.
      assert (A: find a (HCSMap cs) <> None ).
      intuition; congruence.
      apply MapFacts.in_find_iff in A.
      specialize (H _ A).
      destruct (d a) eqn:D; try congruence.
      do 2 eexists.
      apply any_sep_star_ptsto; eauto.
    Qed.

  Lemma size_valid_remove : forall cs a,
    size_valid cs ->
    Map.In a (HCSMap cs) ->
    size_valid (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs) (HCSCount cs - 1) (HCSEvict cs)).
  Proof.
    unfold size_valid in *; intuition simpl.
    rewrite map_remove_cardinal by eauto; congruence.
    eapply le_trans.
    apply map_cardinal_remove_le; auto.
    auto.
  Qed.

  Lemma size_valid_remove_notin : forall cs a,
    size_valid cs ->
    ~ Map.In a (HCSMap cs) ->
    size_valid (mk_cs (Map.remove a (HCSMap cs)) (HCSMaxCount cs) (HCSCount cs) (HCSEvict cs)).
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
    Map.In a (HCSMap cs) ->
    Map.cardinal (Map.remove a (HCSMap cs)) < HCSMaxCount cs.
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
    cardinal (HCSMap cs) < HCSMaxCount cs ->
    Map.find a (HCSMap cs) = None ->
    size_valid cs ->
    size_valid (mk_cs (add a vv (HCSMap cs)) (HCSMaxCount cs) (HCSCount cs + 1) evictor).
  Proof.
    unfold size_valid; intuition; simpl.

    destruct (find a0 (HCSMap cs)) eqn:?; try congruence.
    rewrite map_add_cardinal. omega.
    intuition repeat deex.
    apply MapFacts.find_mapsto_iff in H3; congruence.

    destruct (Map.find a0 (HCSMap cs)) eqn:?.
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
     mem_pred (HighAEQ:= addr_eq_dec) (cachepred csmap bm) (mem_except d a) ✶ a |-> tb =p=>
     mem_pred (HighAEQ:= addr_eq_dec) (cachepred (Map.add a (h, false) csmap) (upd bm h tb)) d.
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
  destruct (find a (HCSMap cs)); [| cancel];
  destruct p; destruct b;
  cancel;
  destruct (Nat.eq_dec h0 h); subst;
  try congruence; rewrite upd_ne; auto.
Qed.