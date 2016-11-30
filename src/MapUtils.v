Require Import List.
Require Import FMapFacts.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import ProofIrrelevance.
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

  Lemma map_empty : forall T (f : V -> T) m, Map.Empty m -> Map.Equal (Map.map f m) (Map.empty T).
  Proof.
    unfold Map.Equal. intros.
    rewrite MapFacts.empty_o.
    destruct Map.find eqn:H'; auto.
    rewrite MapFacts.map_o in H'.
    rewrite map_empty_find_none in H' by auto.
    simpl in H'. discriminate.
  Qed.

  Ltac smash_equal :=
    unfold Map.Equal; intros;
    repeat rewrite ?MapFacts.remove_o, ?MapFacts.add_o;
    repeat destruct Map.E.eq_dec; auto;
    try solve [exfalso; eauto | congruence].

  Lemma map_map_add_comm : forall T (f : V -> T) m k v,
    Map.Equal (Map.map f (Map.add k v m)) (Map.add k (f v) (Map.map f m)).
  Proof.
    intros.
    smash_equal.
    rewrite MapFacts.map_o, MapFacts.add_eq_o; auto.
    rewrite MapFacts.map_o, MapFacts.add_neq_o; auto.
    eauto using MapFacts.map_o.
  Qed.

  Lemma map_map_remove_comm : forall T (f : V -> T) m k,
    Map.Equal (Map.map f (Map.remove k m)) (Map.remove k (Map.map f m)).
    intros. smash_equal.
    rewrite MapFacts.map_o, MapFacts.remove_eq_o; auto.
    rewrite MapFacts.map_o, MapFacts.remove_neq_o; auto.
    eauto using MapFacts.map_o.
  Qed.

  Lemma map_add_remove_equal : forall m k (v : V), Map.MapsTo k v m ->
    Map.Equal m (Map.add k v (Map.remove k m)).
  Proof.
    intros.
    smash_equal. eauto using M.MapsTo_1, M.find_1.
  Qed.

  End MapUtilsFacts.

  Lemma map_cardinal_map_eq : forall V T (f : V -> T) m,
    Map.cardinal (Map.map f m) = Map.cardinal m.
  Proof.
    intros.
    remember (Map.cardinal m) as n.
    generalize dependent m.
    induction n; intros; subst.
    - rewrite map_empty.
      apply MapProperties.cardinal_Empty, Map.empty_1.
      apply MapOrdProperties.P.cardinal_Empty. auto.
    - assert (Map.cardinal m <> 0) as H' by omega.
      apply MapProperties.cardinal_inv_2b in H'.
      destruct H' as [[k v] H']; simpl in H'.
      rewrite map_add_remove_equal with (k := k) (v := v) by auto.
      rewrite map_map_add_comm.
      rewrite map_add_cardinal.
      rewrite IHn; rewrite ?map_remove_cardinal; solve [omega | eauto].
      intro H''. destruct H'' as [? H''].
      rewrite map_map_remove_comm in H''.
      rewrite MapProperties.F.remove_mapsto_iff in H''.
      intuition.
  Qed.

  Lemma map_elements_map_key_eq : forall V T (f : V -> T) m,
    eqlistA (@Map.eq_key _) (Map.elements (Map.map f m))
                             (map (fun x => (fst x, f (snd x))) (Map.elements m)).
  Proof.
    intros.
    eapply sorted_nodup_eq with (ltA := @Map.lt_key _); eauto with *.
    - split; intros.
      rewrite InA_alt in *. destruct H as [x0]. exists x0. intuition.
      destruct x0. eapply In_InA, Map.elements_2 in H1.
      eapply MapFacts.map_mapsto_iff in H1. destruct H1.
      intuition subst. eapply in_map_iff. eexists (_, _); simpl; intuition.
      eapply Map.elements_1, InA_alt in H2. destruct H2. intuition.
      destruct x1. unfold Map.eq_key_elt, Map.E.eq in *.
      simpl in *. intuition congruence.
      auto with *.
      rewrite InA_alt in *. destruct H as [x0]. exists x0. intuition.
      apply in_map_iff in H1.
      destruct H1 as [[]], x, x0. simpl in H.
      intuition. inversion H1; simpl in *; subst.
      eapply In_InA, Map.elements_2, Map.map_1 with (f := f),
        Map.elements_1, InA_alt in H2; eauto with *.
      destruct H2 as [[]]. intuition idtac. inversion H2.
      unfold Map.eq_key_elt, Map.E.eq in H2; simpl in *; intuition subst. auto.
    - eapply Map.elements_3w.
    - eapply nodup_map. apply Map.elements_3w.
    - eapply Map.elements_3.
    - apply sorted_map. unfold Map.lt_key, Map.E.lt. simpl.
      apply Map.elements_3.
    - apply eq_key_dec.
    - intros. destruct (OT.compare (fst x) (fst y)); intuition eauto.
  Qed.

  Lemma map_elements_map_eq : forall V T (f : V -> T) m,
    Map.elements (Map.map f m) = map (fun x => (fst x, f (snd x))) (Map.elements m).
  Proof.
    intros.
    eapply eqlistA_eq with (R := @Map.eq_key_elt _).
    unfold Map.eq_key_elt, Map.E.eq; intuition. destruct y.
    simpl in *; congruence.
    eapply eqlistA_strengthen; [ | | eapply map_elements_map_key_eq].
    auto with *.
    intros x y; destruct x, y; intros.
    eapply Map.elements_2 in H.
    rewrite InA_alt in H0. destruct H0.
    unfold Map.eq_key_elt, Map.eq_key, Map.E.eq in *. simpl in *.
    intuition subst.
    apply in_map_iff in H3. destruct H3 as [[]]; intuition subst.
    simpl in *.
    eapply In_InA in H2. eapply M.elements_2, M.map_1 in H2.
    eapply MapProperties.F.MapsTo_fun; eauto.
    auto with *.
  Qed.

  (* Coq bug : instance doesn't work well with section arguments *)
  Instance map_elements_proper {V} :
    Proper (Map.Equal ==> eq) (@Map.elements V).
  Proof.
    unfold Proper, respectful; intros; subst.
    apply mapeq_elements; auto.
  Qed.



End MapDefs.

Require Import FMapList.

Module AddrMap_List := FMapList.Make(Nat_as_OT).
Module AddrMap := MapDefs Nat_as_OT AddrMap_List.

Local Hint Resolve AddrMap_List.Raw.PX.ltk_strorder.

Ltac addrmap_unfold :=
  unfold AddrMap_List.Raw.PX.ltk, Nat_as_OT.lt, Nat_as_OT.eq in *;
  simpl in *.

Lemma hdrel_map_raw_find_none : forall T k v l,
  HdRel (@AddrMap_List.Raw.PX.ltk T) (k, v) l ->
  AddrMap_List.Raw.find k l = None.
Proof.
  intros T k v l H.
  induction l as [|a l']; inversion H; simpl; auto.
  destruct a; unfold AddrMap_List.Raw.PX.ltk in *; simpl in *.
  destruct Nat_as_OT.compare; addrmap_unfold; try omega; auto.
Qed.

Lemma build_slist_inj : forall T l1 l2 p1 p2,
  l1 = l2 ->
  @AddrMap_List.Build_slist T l1 p1 = @AddrMap_List.Build_slist T l2 p2.
Proof.
  intros; subst.
  setoid_rewrite proof_irrelevance. eauto.
  Grab Existential Variables.
  eauto.
Qed.

Theorem addrmap_equal_eq : forall T (m1 m2 : AddrMap_List.t T),
  AddrMap_List.Equal m1 m2 -> m1 = m2.
Proof.
  intros T m1 m2 H.
  destruct m1, m2.
  eapply build_slist_inj.
  generalize dependent this0.
  induction this; intros; destruct this0; eauto.
  - unfold AddrMap_List.Equal in H. destruct p.
    specialize (H n).
    unfold AddrMap_List.find in H. simpl in H.
    destruct Nat_as_OT.compare; addrmap_unfold; try omega.
    discriminate.
  - unfold AddrMap_List.Equal in H. destruct a.
    specialize (H n).
    unfold AddrMap_List.find in H. simpl in H.
    destruct Nat_as_OT.compare; addrmap_unfold; try omega.
    discriminate.
  - repeat match goal with
    | [h : Sorted _ (_ :: ?l) |- _] =>
      match goal with
      | [h' : Sorted _ l |- _] => fail 1
      | _ => inversion h
      end; subst
    | [h : _ |- _ ] => specialize (IHthis h)
    | [x : _ * _ |- _ ] => destruct x
    end; subst.
    match type of IHthis with
    | ?a -> ?b => enough b
    end; subst.
    specialize (H n).
    unfold AddrMap_List.find in *. simpl in *.
    repeat destruct Nat_as_OT.compare in H; addrmap_unfold;
      try discriminate; try omega.
    inversion H; subst. auto.
    f_equal.
    erewrite hdrel_map_raw_find_none in H by eauto. discriminate.
    apply IHthis.
    (* from the enough above *)
    intro y.
    pose proof (H y) as H'. unfold AddrMap_List.find in *.
    simpl in *.
    repeat destruct Nat_as_OT.compare; addrmap_unfold; try congruence; subst;
      repeat erewrite hdrel_map_raw_find_none in * by
        (eapply InfA_ltA; eauto; addrmap_unfold; simpl in *; omega); eauto.
    inversion H'; subst.
    repeat erewrite hdrel_map_raw_find_none; eauto.
    all : match goal with
      [n : nat |- _ ] => solve [specialize (H n); unfold AddrMap_List.find in H;
        simpl in *; repeat destruct Nat_as_OT.compare;
        addrmap_unfold; try congruence; try omega]
      end.
  Grab Existential Variables.
  all : eauto.
Qed.
