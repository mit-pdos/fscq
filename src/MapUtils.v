Require Import List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Import ListNotations.
Set Implicit Arguments.

Module Map := FMapAVL.Make(Nat_as_OT).
Module MapFacts := WFacts_fun Nat_as_OT Map.
Module MapProperties := WProperties_fun Nat_as_OT Map.
Module MapOrdProperties := OrdProperties Map.


Definition KIn V := InA (@Map.eq_key V).
Definition KNoDup V := NoDupA (@Map.eq_key V).
Definition map0 V := Map.empty V.
Definition map_keys V (m : Map.t V) := map fst (Map.elements m).


Lemma mapsto_add : forall V a v v' (m : Map.t V),
  Map.MapsTo a v (Map.add a v' m) -> v' = v.
Proof.
  intros.
  apply Map.find_1 in H.
  erewrite Map.find_1 in H by (apply Map.add_1; auto).
  congruence.
Qed.

Lemma map_remove_cardinal : forall V (m : Map.t V) k, (exists v, Map.MapsTo k v m) ->
  Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
Proof.
  intros. destruct H as [v].
  erewrite MapProperties.cardinal_2 with (m:=Map.remove k m) (m':=m) (x:=k) (e:=v).
  omega.
  apply Map.remove_1; auto.
  intro.
  destruct (Nat_as_OT.eq_dec k y); subst.
  - rewrite MapFacts.add_eq_o; auto.
    erewrite Map.find_1; eauto.
  - rewrite MapFacts.add_neq_o; auto.
    rewrite MapFacts.remove_neq_o; auto.
Qed.

Lemma map_add_cardinal : forall V (m : Map.t V) k v, ~ (exists v, Map.MapsTo k v m) ->
  Map.cardinal (Map.add k v m) = Map.cardinal m + 1.
Proof.
  intros.
  erewrite MapProperties.cardinal_2 with (m:=m).
  omega.
  eauto.
  intro.
  reflexivity.
Qed.

Lemma map_add_dup_cardinal' : forall V (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
  Map.cardinal (Map.add k v m) = Map.cardinal (Map.remove k m) + 1.
Proof.
  intros. destruct H.
  erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
  omega.
  apply Map.remove_1; auto.
  intro.
  destruct (Nat_as_OT.eq_dec k y); subst.
  - rewrite MapFacts.add_eq_o; auto.
    rewrite MapFacts.add_eq_o; auto.
  - rewrite MapFacts.add_neq_o; auto.
    rewrite MapFacts.add_neq_o; try omega.
    rewrite MapFacts.remove_neq_o; auto.
Qed.

Lemma map_add_dup_cardinal : forall V (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
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
  destruct (Nat_as_OT.eq_dec k y); subst.
  - rewrite MapFacts.add_eq_o; auto.
    erewrite Map.find_1; eauto.
  - rewrite MapFacts.add_neq_o; auto.
    rewrite MapFacts.remove_neq_o; auto.
Qed.

Lemma map_elements_hd_in : forall V (m : Map.t V) k w l,
  Map.elements m = (k, w) :: l ->
  Map.In k m.
Proof.
  intros.
  eexists; apply Map.elements_2.
  rewrite H.
  apply InA_cons_hd.
  constructor; eauto.
Qed.

Lemma mapeq_elements : forall V m1 m2,
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

Lemma KNoDup_NoDup: forall V (l : list (Map.key * V)),
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

Lemma map_fst_nodup: forall V (ms : Map.t V),
  NoDup (map fst (Map.elements ms)).
Proof.
  intros.
  apply KNoDup_NoDup.
  apply Map.elements_3w.
Qed.


Lemma InA_eqke_In : forall V a v l,
  InA (Map.eq_key_elt (elt:=V)) (a, v) l -> In (a, v) l.
Proof.
  induction l; intros; auto; inversion H; subst.
  inversion H1.
  destruct a0; simpl in *; subst; auto.
  simpl. right.
  apply IHl; auto.
Qed.

Lemma is_empty_eq_map0 : forall V (m : Map.t V),
  Map.is_empty m = true -> Map.Equal m (map0 V).
Proof.
  unfold map0; intros.
  apply Map.is_empty_2 in H.
  hnf; intros.
  rewrite MapFacts.empty_o.
  apply MapFacts.not_find_in_iff.
  cbv in *; intros.
  destruct H0; eapply H; eauto.
Qed.

Lemma In_KIn : forall V a (v : V) l,
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


Lemma In_fst_KIn : forall V a (l : list (Map.key * V)),
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
  destruct x0; simpl in *.
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
  destruct (eq_nat_dec y k1); destruct (eq_nat_dec y k2); subst; try congruence.
  rewrite MapFacts.add_eq_o by auto.
  rewrite MapFacts.add_neq_o by auto.
  rewrite MapFacts.add_eq_o; auto.
  setoid_rewrite MapFacts.add_eq_o at 2; auto.
  rewrite MapFacts.add_neq_o by auto.
  rewrite MapFacts.add_eq_o; auto.
  repeat rewrite MapFacts.add_neq_o; auto.
Qed.


Lemma map_add_repeat : forall V a (v : V) m,
  Map.Equal (Map.add a v (Map.add a v m)) (Map.add a v m).
Proof.
  intros; hnf; intros.
  destruct (eq_nat_dec y a); subst; try congruence.
  rewrite MapFacts.add_eq_o by auto.
  rewrite MapFacts.add_eq_o; auto.
  rewrite MapFacts.add_neq_o by auto.
  repeat rewrite MapFacts.add_neq_o; auto.
Qed.


Lemma eq_key_dec : forall V (a b : Map.key * V),
  {Map.eq_key a b} + {~ Map.eq_key a b}.
Proof.
  intros; destruct a, b.
  destruct (eq_nat_dec k k0); subst.
  left; hnf; auto.
  right; hnf. tauto.
Qed.


