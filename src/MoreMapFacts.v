Require Import DecidableType DecidableTypeEx OrderedType Morphisms.
Require Export FMapFacts.

Set Implicit Arguments.

Module MoreFacts_fun (E:DecidableType)(Import M:WSfun E).

  Module Import MapFacts := FMapFacts.WFacts_fun(E)(M).
  Import M.

  Ltac smash_equal :=
    unfold Equal; intros;
    repeat rewrite ?remove_o, ?add_o;
    repeat destruct eq_dec; auto;
    try solve [exfalso; eauto].

  Definition respect_eq {V} P := forall a b (v : V),
    E.eq a b -> P (a, v) <-> P (b, v).

  Lemma respect_eq_rewrite : forall V P a b (v : V),
    respect_eq P -> E.eq a b ->
    P (a, v) <-> P (b, v).
  Proof.
    intros.
    unfold respect_eq in *.
    rewrite H; eauto.
  Qed.

  Lemma respect_eq_eq : forall V P,
    E.eq = eq -> @respect_eq V P.
  Proof.
    unfold respect_eq. intros.
    rewrite H in H0. subst.
    split; auto.
  Qed.

  Hint Resolve respect_eq_eq.

  Lemma in_add : forall V k (v : V) m,
    In k (add k v m).
  Proof.
    intros.
    apply add_in_iff. auto.
  Qed.

  Lemma mapsto_elements : forall V k (v : V) m,
    MapsTo k v m -> exists k', E.eq k k' /\ List.In (k', v) (elements m).
  Proof.
    intros.
    apply elements_1 in H.
    generalize dependent k. generalize dependent v.
    induction (elements m); intros.
    inversion H.
    inversion H; subst. destruct a; simpl in *.
    unfold eq_key_elt in *; simpl in *.
    intuition. eexists. split; subst; eauto.
    simpl. edestruct IHl; eauto.
    intuition. eexists. split; subst; eauto.
  Qed.

  Lemma in_remove : forall V x k (m : t V),
    In x (remove k m) -> In x m.
  Proof.
    intros.
    unfold In in *. destruct H. eexists.
    apply remove_mapsto_iff in H.
    intuition. eauto.
  Qed.

  Lemma Forall_elements : forall V P (m : t V),
    respect_eq P ->
    Forall P (elements m) <-> forall k v, MapsTo k v m -> P (k, v).
  Proof.
    split; intros.
    apply mapsto_elements in H1. repeat destruct H1.
    rewrite Forall_forall in H0.
    rewrite respect_eq_rewrite; eauto.
    apply Forall_forall. intros.
    destruct x.
    rewrite respect_eq_rewrite. apply H0.
    Search elements MapsTo.
    apply elements_2.
    Search InA List.In.
    apply InA_alt.
    eexists.
    split; eauto.
    unfold eq_key_elt; simpl.
    all : eauto.
  Qed.

  Lemma Forall_elements_add : forall V P k (v : V) m,
                                respect_eq P ->
                                Forall P (elements (add k v m)) <->
                                P (k, v) /\ Forall P (elements (remove k m)).
  Proof.
    split; intros.
    pose proof (add_1 m v (E.eq_refl k)).
    apply mapsto_elements in H1.
    repeat destruct H1.
    split.
    rewrite Forall_forall in H0.
    apply H0 in H2. rewrite respect_eq_rewrite; eassumption.

    apply Forall_elements; auto.
    rewrite Forall_elements in H0 by auto.
    intros.
    apply H0.
    apply remove_mapsto_iff in H3; intuition.

    intuition.
    apply Forall_elements; auto.
    rewrite Forall_elements in H2; auto.
    intros.
    rewrite add_mapsto_iff in H0.
    destruct H0; intuition. subst.
    rewrite respect_eq_rewrite; eauto.
  Qed.

  (* TODO: Setoid rewriting? *)
  Lemma Forall_elements_equal: forall V P (m1 m2 : t V),
                                 respect_eq P ->
                                 Forall P (elements m1) ->
                                 Equal m2 m1 ->
                                 Forall P (elements m2).
  Proof.
    intros.
    rewrite Forall_elements in * by auto. intros.
    rewrite Equal_mapsto_iff in H1.
    firstorder.
  Qed.
  Hint Resolve Forall_elements_equal : mapfacts.

  Lemma add_remove_comm : forall V k1 k2 (v : V) m,
                            ~E.eq k1 k2 ->
                            Equal (add k2 v (remove k1 m)) (remove k1 (add k2 v m)).
  Proof.
    smash_equal.
  Qed.

  Lemma add_remove_comm' : forall V k1 k2 (v : V) m,
                             ~E.eq k1 k2 ->
                             Equal (remove k1 (add k2 v m)) (add k2 v (remove k1 m)).
  Proof.
    smash_equal.
  Qed.

  Lemma add_remove_same : forall V k (v : V) m,
                            Equal (remove k (add k v m)) (remove k m).
  Proof.
    smash_equal.
  Qed.

  Lemma add_add_comm : forall V k1 k2 v1 v2 (m : t V),
                         ~E.eq k1 k2 ->
                         Equal (add k2 v2 (add k1 v1 m))
                                         (add k1 v1 (add k2 v2 m)).
  Proof.
    smash_equal.
  Qed.

  Lemma add_same : forall V k (v v0 : V) m,
                            Equal (add k v (add k v0 m)) (add k v m).
  Proof.
    smash_equal.
  Qed.

  Lemma remove_remove_comm : forall V k1 k2 (m : t V),
                               ~E.eq k1 k2 ->
                               Equal (remove k2 (remove k1 m)) (remove k1 (remove k2 m)).
  Proof.
    smash_equal.
  Qed.

  Lemma Forall_elements_remove_weaken : forall V P k (m : t V),
                                          respect_eq P ->
                                          Forall P (elements m) ->
                                          Forall P (elements (remove k m)).
  Proof.
    intros.
    rewrite Forall_elements in * by auto. intros.
    apply H0.
    eapply remove_3. eauto.
  Qed.

  Lemma forall_In_Forall_elements : forall V (P : _ -> Prop) m,
                                      (forall k (v : V), find k m = Some v -> P (k, v)) ->
                                      Forall P (elements m).
  Proof.
    intros.
    apply Forall_forall. intros.
    destruct x. apply H.
    apply find_1.
    apply elements_2.
    apply InA_alt.
    eexists. unfold eq_key_elt. intuition; eauto.
  Qed.

  Lemma Forall_elements_forall_In : forall V (P : _ -> Prop) m,
                                      respect_eq P ->
                                      Forall P (elements m) ->
                                      (forall k (v : V), find k m = Some v -> P (k, v)).
  Proof.
    intros.
    rewrite Forall_elements in H0 by auto.
    apply H0.
    apply find_2; auto.
  Qed.

  Lemma remove_empty : forall V k,
                         Equal (remove k (empty V)) (empty V).
  Proof.
    intros. intro.
    rewrite remove_o. destruct (eq_dec k y); eauto using empty_o.
  Qed.
  Hint Resolve remove_empty : mapfacts.

  Lemma Forall_elements_empty : forall V P,
                                  Forall P (elements (empty V)).
  Proof.
    intros.
    apply forall_In_Forall_elements; intros.
    rewrite empty_o in *.
    inversion H.
  Qed.

  Lemma Forall_false : forall T (l : list T), Forall (fun _ => False) l -> l = nil.
  Proof.
    intros.
    destruct l. auto.
    inversion H. contradiction.
  Qed.

  Lemma elements_empty_nil : forall V, elements (empty V) = nil.
  Proof.
    intros.
    pose proof (@Forall_elements_empty V (fun _ => False)).
    apply Forall_false. auto.
  Qed.

  Hint Resolve Forall_elements_empty : mapfacts.
End MoreFacts_fun.