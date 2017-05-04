Require Import List.
Require Import FMapFacts.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Import ListNotations.
Set Implicit Arguments.


Module MapDefs (OT : UsualOrderedType) (M : S with Module E := OT).

  Module Map := M.
  Module MapFacts := WFacts_fun OT Map.
  Module MapProperties := WProperties_fun OT Map.
  Module MapOrdProperties := OrdProperties Map.

  Section MapUtilsFacts.

  Variable V : Type.

  Definition KIn := InA (@Map.eq_key V).
  Definition KNoDup := NoDupA (@Map.eq_key V).
  Definition map0 := Map.empty V.
  Definition map_keys (m : Map.t V) := map fst (Map.elements m).

  Lemma KNoDup_map_elements : forall (m : Map.t V) ,
     KNoDup (Map.elements m).
  Proof.
    intros; apply Map.elements_3w.
  Qed.
  Hint Resolve KNoDup_map_elements.

  Lemma mapsto_add : forall a v v' (m : Map.t V),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
  Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; hnf; auto).
    congruence.
  Qed.

  Lemma map_remove_cardinal : forall (m : Map.t V) k,
    (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
  Proof.
    intros. destruct H as [v].
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m) (m':=m) (x:=k) (e:=v).
    omega.
    apply Map.remove_1; hnf; auto.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma map_add_cardinal : forall (m : Map.t V) k v, ~ (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m + 1.
  Proof.
    intros.
    erewrite MapProperties.cardinal_2 with (m:=m).
    omega.
    eauto.
    intro.
    reflexivity.
  Qed.


  Lemma map_add_dup_cardinal' : forall (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal (Map.remove k m) + 1.
  Proof.
    intros. destruct H.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    omega.
    apply Map.remove_1; hnf; auto.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      rewrite MapFacts.add_eq_o; auto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.add_neq_o; try omega; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma map_add_dup_cardinal : forall (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m.
  Proof.
    intros.
    replace (Map.cardinal m) with ((Map.cardinal m - 1) + 1).
    erewrite <- map_remove_cardinal; eauto.
    apply map_add_dup_cardinal'; auto.
    destruct H.
    assert (Map.cardinal m <> 0); try omega.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    omega.
    apply Map.remove_1; reflexivity.
    intro.
    destruct (OT.eq_dec k y); unfold OT.eq in *; subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma map_elements_hd_in : forall (m : Map.t V) k w l,
    Map.elements m = (k, w) :: l ->
    Map.In k m.
  Proof.
    intros.
    eexists; apply Map.elements_2.
    rewrite H.
    apply InA_cons_hd.
    constructor; hnf; eauto.
  Qed.

  Lemma mapeq_elements : forall m1 m2,
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

  Hint Resolve MapProperties.eqke_equiv.

  Lemma KNoDup_NoDup: forall (l : list (Map.key * V)),
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

  Lemma NoDupA_cons_inv : forall T (l : list T) m a,
    NoDupA m (a :: l) -> NoDupA m l.
  Proof.
    intros.
    rewrite <- app_nil_l.
    eapply NoDupA_split.
    rewrite app_nil_l. intuition eauto.
  Qed.

  Lemma KNoDup_cons_inv : forall l k,
    KNoDup (k :: l) -> KNoDup l.
  Proof.
    unfold KNoDup; intros.
    eapply NoDupA_cons_inv; eauto.
  Qed.

  Lemma map_fst_nodup: forall (ms : Map.t V),
    NoDup (map fst (Map.elements ms)).
  Proof.
    intros.
    apply KNoDup_NoDup.
    apply Map.elements_3w.
  Qed.


  Lemma InA_eqke_In : forall a v l,
    InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
  Proof.
    induction l; intros; auto; inversion H; subst.
    inversion H1.
    destruct a0; simpl in *; hnf in *; subst; auto.
    simpl. right.
    apply IHl; auto.
  Qed.

  Lemma is_empty_eq_map0 : forall (m : Map.t V),
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

  Lemma In_KIn : forall a (v : V) l,
    In a (map fst l) -> InA (@Map.eq_key V) (a, v) l.
  Proof.
    intros.
    apply in_map_fst_exists_snd in H.
    destruct H.
    apply InA_alt.
    exists (a, x).
    split; auto.
    hnf; auto.
  Qed.


  Lemma In_fst_KIn : forall a (l : list (Map.key * V)),
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

  Lemma KIn_fst_In : forall a (l : list (Map.key * V)),
    KIn a l -> In (fst a) (map fst l).
  Proof.
    intros; destruct a; simpl in *.
    unfold KIn in *.
    apply InA_alt in H.
    inversion H.
    destruct x.
    intuition.
    unfold Map.eq_key in H1; simpl in *.
    rewrite H1.
    replace k0 with (fst (k0, v0)) by auto.
    eapply in_map; eauto.
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
    destruct x0; simpl in *; hnf in *; subst.
    generalize dependent (Map.elements m).
    induction l; intros; simpl; auto.
    inversion H1; intuition.
    destruct a; inversion H.
    tauto.
  Qed.


  Lemma map_add_comm : forall A k1 k2 (v1 v2 : A) m,
    k1 <> k2 ->
    Map.Equal (Map.add k1 v1 (Map.add k2 v2 m)) (Map.add k2 v2 (Map.add k1 v1 m)).
  Proof.
    intros; hnf; intro.
    destruct (OT.eq_dec y k1); destruct (OT.eq_dec y k2); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    setoid_rewrite MapFacts.add_eq_o at 2; auto.
    rewrite MapFacts.add_neq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.


  Lemma map_add_repeat : forall a (v v' : V) m,
    Map.Equal (Map.add a v (Map.add a v' m)) (Map.add a v m).
  Proof.
    intros; hnf; intros.
    destruct (OT.eq_dec y a); subst; try congruence.
    rewrite MapFacts.add_eq_o by auto.
    rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.add_neq_o by auto.
    repeat rewrite MapFacts.add_neq_o; auto.
  Qed.


  Lemma eq_key_dec : forall (a b : Map.key * V),
    {Map.eq_key a b} + {~ Map.eq_key a b}.
  Proof.
    intros; destruct a, b.
    destruct (OT.eq_dec k k0); subst.
    left; hnf; auto.
    right; hnf. tauto.
  Qed.

  Lemma map_empty_find_exfalso : forall a m (v : V),
    Map.find a m = Some v ->
    Map.Empty m -> False.
  Proof.
    intros.
    rewrite MapFacts.elements_o in H.
    apply MapProperties.elements_Empty in H0.
    rewrite H0 in H; simpl in H.
    congruence.
  Qed.

  Lemma map_remove_not_in_equal : forall a (m : Map.t V),
    ~ Map.In a m ->
    Map.Equal (Map.remove a m) m.
  Proof.
    intros.
    apply MapFacts.Equal_mapsto_iff; intros; split; intro.
    eapply Map.remove_3; eauto.
    apply MapFacts.remove_mapsto_iff; intuition.
    contradict H; subst.
    apply MapFacts.in_find_iff.
    apply Map.find_1 in H0.
    congruence.
  Qed.

  Lemma map_remove_not_in_elements_eq : forall a (m : Map.t V),
    ~ Map.In a m ->
    Map.elements (Map.remove a m) = Map.elements m.
  Proof.
    intros.
    erewrite mapeq_elements; eauto.
    apply map_remove_not_in_equal; auto.
  Qed.

  Lemma map_empty_find_none : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.find a m = None.
  Proof.
    intros.
    rewrite MapFacts.elements_o.
    apply MapProperties.elements_Empty in H.
    rewrite H; simpl; auto.
  Qed.

  Lemma map_empty_not_In : forall (m : Map.t V) a,
    Map.Empty m ->
    ~ Map.In a m.
  Proof.
    intros.
    apply MapFacts.not_find_in_iff.
    apply map_empty_find_none; auto.
  Qed.

  Lemma find_none_empty : forall (m : Map.t V),
    (forall a, Map.find a m = None) ->
    Map.Empty m.
  Proof.
    intros; cbv; intros.
    eapply Map.find_1 in H0.
    congruence.
  Qed.

  Lemma map_remove_empty : forall (m : Map.t V) a,
    Map.Empty m ->
    Map.Empty (Map.remove a m).
  Proof.
    intros.
    eapply find_none_empty; intros.
    rewrite MapFacts.remove_o.
    destruct (OT.eq_dec a a0); auto.
    apply map_empty_find_none; auto.
  Qed.

  Lemma not_In_not_InA : forall a v (m : Map.t V),
    ~ Map.In a m ->
    ~ InA (@Map.eq_key_elt V) (a, v) (Map.elements m).
  Proof.
    intros.
    apply MapFacts.not_find_in_iff in H.
    intuition.
    eapply Map.elements_2 in H0.
    apply Map.find_1 in H0.
    congruence.
  Qed.

  Lemma map_remove_elements_not_in : forall m a (v : V),
    ~ InA (@Map.eq_key_elt V) (a, v) (Map.elements (Map.remove a m)).
  Proof.
    intros.
    apply not_In_not_InA.
    apply Map.remove_1; hnf; auto.
  Qed.

  Lemma not_in_remove_not_in : forall x y (m : Map.t V),
    ~ Map.In x m ->
    ~ Map.In x (Map.remove y m).
  Proof.
    intros.
    destruct (OT.eq_dec x y); hnf in *; subst.
    apply Map.remove_1; hnf; auto.
    destruct (MapFacts.In_dec (Map.remove y m) x).
    contradict H.
    eapply MapFacts.remove_neq_in_iff; eauto.
    auto.
  Qed.

  Lemma MapsTo_In : forall m a (v : V),
    Map.MapsTo a v m -> Map.In a m.
  Proof.
    intros.
    apply MapFacts.find_mapsto_iff in H.
    apply MapFacts.in_find_iff.
    congruence.
  Qed.

  Lemma In_MapsTo : forall (m : Map.t V) a,
    Map.In a m -> exists v, Map.MapsTo a v m.
  Proof.
    intros.
    apply MapFacts.in_find_iff.
    apply MapFacts.in_find_iff in H; auto.
  Qed.

  Lemma KIn_exists_elt_InA : forall l x,
    KIn x l ->
    exists v, InA (@Map.eq_key_elt V) (fst x, v) l.
  Proof.
    intros.
    apply InA_alt in H.
    destruct H as [y [? ?]].
    destruct x, y.
    cbv in H; subst.
    exists v0; simpl.
    apply In_InA; auto.
  Qed.


  Lemma length_elements_cardinal_gt : forall V (m : Map.t V) n,
    length (Map.elements m) > n ->
    Map.cardinal m > n.
  Proof.
    intros; rewrite Map.cardinal_1; auto.
  Qed.

  Lemma InA_filter : forall ents a f,
    InA (@Map.eq_key V) a (filter f ents) ->
    InA (@Map.eq_key V) a ents.
  Proof.
    induction ents; simpl; auto; intros.
    apply InA_cons.
    destruct (eq_key_dec a0 a); intuition.
    right; eapply IHents.
    destruct (f a); eauto.
    inversion H; subst; try congruence.
  Qed.

  Lemma KNoDup_filter : forall ents f,
    KNoDup ents ->
    KNoDup (filter f ents).
  Proof.
    induction ents; simpl; auto; intros.
    inversion H; subst.
    destruct (f a); intros; eauto.
    constructor.
    contradict H2.
    eapply InA_filter; eauto.
    apply IHents; eauto.
  Qed.


  Lemma map_cardinal_remove_le : forall (m : Map.t V) a,
    Map.cardinal (Map.remove a m) <= Map.cardinal m.
  Proof.
    intros.
    destruct (Map.find a m) eqn: Heq.
    rewrite map_remove_cardinal.
    omega.
    eexists; eapply Map.find_2; eauto.
    erewrite MapProperties.cardinal_m; eauto.
    apply map_remove_not_in_equal.
    apply MapFacts.not_find_in_iff; auto.
  Qed.

  End MapUtilsFacts.



  (* Coq bug : instance doesn't work well with section arguments *)
  Instance map_elements_proper {V} :
    Proper (Map.Equal ==> eq) (@Map.elements V).
  Proof.
    unfold Proper, respectful; intros; subst.
    apply mapeq_elements; auto.
  Qed.


End MapDefs.



Require Import FMapAVL.

Module AddrMap_AVL := FMapAVL.Make(Nat_as_OT).
Module AddrMap := MapDefs Nat_as_OT AddrMap_AVL.

Require Import MSetAVL.
Require Import Structures.OrdersEx.
Module AddrSet := MSetAVL.Make (OrdersEx.Nat_as_OT).
