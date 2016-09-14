Require Import DecidableType DecidableTypeEx OrderedType Morphisms.
Require Export FMapFacts.

Set Implicit Arguments.

Module MoreFacts_fun (E:DecidableType)(Import M:WSfun E).

  Module Import MapFacts := FMapFacts.WFacts_fun(E)(M).
  Import M.

  Lemma Forall_elements_add : forall V P k (v : V) m,
                                Forall P (elements (add k v m)) <->
                                P (k, v) /\ Forall P (elements (remove k m)).
  Admitted.

  (* TODO: Setoid rewriting? *)
  Lemma Forall_elements_equal: forall V P (m1 m2 : t V),
                                 Forall P (elements m1) ->
                                 Equal m2 m1 ->
                                 Forall P (elements m2).
  Admitted.
  Hint Resolve Forall_elements_equal : mapfacts.

  Lemma add_remove_comm : forall V k1 k2 (v : V) m,
                            k1 <> k2 ->
                            Equal (add k2 v (remove k1 m)) (remove k1 (add k2 v m)).
  Admitted.

  Lemma add_remove_comm' : forall V k1 k2 (v : V) m,
                             k1 <> k2 ->
                             Equal (remove k1 (add k2 v m)) (add k2 v (remove k1 m)).
  Admitted.

  Lemma add_remove_same : forall V k (v : V) m,
                            Equal (remove k (add k v m)) (remove k m).
  Admitted.

  Lemma add_add_comm : forall V k1 k2 v1 v2 (m : t V),
                         k1 <> k2 ->
                         Equal (add k2 v2 (add k1 v1 m))
                                         (add k1 v1 (add k2 v2 m)).
  Admitted.

  Lemma add_same : forall V k (v v0 : V) m,
                            Equal (add k v (add k v0 m)) (add k v m).
  Admitted.

  Lemma remove_remove_comm : forall V k1 k2 (m : t V),
                               k1 <> k2 ->
                               Equal (remove k2 (remove k1 m)) (remove k1 (remove k2 m)).
  Admitted.

  Lemma Forall_elements_remove_weaken : forall V P k (m : t V),
                                          Forall P (elements m) ->
                                          Forall P (elements (remove k m)).
  Proof.
  Admitted.

  Lemma forall_In_Forall_elements : forall V (P : _ -> Prop) m,
                                      (forall k (v : V), find k m = Some v -> P (k, v)) ->
                                      Forall P (elements m).
  Proof.
  Admitted.

  Lemma Forall_elements_forall_In : forall V (P : _ -> Prop) m,
                                      Forall P (elements m) ->
                                      (forall k (v : V), find k m = Some v -> P (k, v)).
  Proof.
  Admitted.

  Lemma remove_empty : forall V k,
                         Equal (remove k (empty V)) (empty V).
  Proof.
    intros. intro.
    rewrite remove_o. destruct (eq_dec k y); eauto using empty_o.
  Qed.
  Hint Resolve remove_empty : mapfacts.

  Lemma elements_empty : forall V, elements (empty V) = nil.
  Proof.
  Admitted.

  Lemma Forall_elements_empty : forall V P,
                                  Forall P (elements (empty V)).
  Proof.
    intros.
    rewrite elements_empty.
    auto.
  Qed.
  Hint Resolve Forall_elements_empty : mapfacts.
End MoreFacts_fun.