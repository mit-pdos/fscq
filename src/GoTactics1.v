Require Export VerdiTactics.
Require Import Pred Hoare.
Require Import GoSepAuto ADestructPair.
Require Import GoSemantics.

Ltac set_hyp_evars :=
  repeat match goal with
  | [ H : context[?e] |- _ ] =>
    is_evar e;
    let H := fresh in
    set (H := e) in *
  end.


Ltac invert_trivial H :=
  match type of H with
    | ?con ?a = ?con ?b =>
      let H' := fresh in
      assert (a = b) as H' by exact (match H with eq_refl => eq_refl end); clear H; rename H' into H
  end.

Ltac clear_trivial_eq :=
  repeat match goal with
         | [ H: ?x = ?y |- _ ] =>
           let x := constr:(eq_refl : x = y) in
           clear H
         end.

Ltac destruct_type T :=
  match goal with
  | [ H: T |- _ ] => destruct H
  end.

Ltac destruct_pairs :=
  repeat (simpl in *; try destruct_pair_once).


Lemma pair_inj :
  forall A B (a1 a2 : A) (b1 b2 : B), (a1, b1) = (a2, b2) -> a1 = a2 /\ b1 = b2.
Proof.
  intros. find_inversion. auto.
Qed.


Lemma some_inj :
  forall A (x y : A), Some x = Some y -> x = y.
Proof.
  intros. find_inversion. auto.
Qed.

Lemma Val_type_inj :
  forall t1 t2 v1 v2, Go.Val t1 v1 = Go.Val t2 v2 -> t1 = t2.
Proof.
  intros. find_inversion. auto.
Qed.

Lemma Here_inj :
  forall T (a b : T), Go.Here a = Go.Here b -> a = b.
Proof.
  intros. find_inversion. auto.
Qed.

Ltac find_inversion_safe :=
  match goal with
  | [ H : ?X ?a = ?X ?b |- _ ] =>
    (unify a b; fail 1) ||
    let He := fresh in
    assert (a = b) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; subst
  | [ H : ?X ?a1 ?a2 = ?X ?b1 ?b2 |- _ ] =>
    (unify a1 b1; unify a2 b2; fail 1) ||
    let He := fresh in
    assert (a1 = b1 /\ a2 = b2) as He by solve [inversion H; auto with equalities | invert_trivial H; auto with equalities]; clear H; destruct He as [? ?]; subst
  | [ H : (?a, ?b) = (?c, ?d) |- _ ] =>
    apply pair_inj in H; destruct H; try (subst a || subst c); try (subst b || subst d)
  end.

Ltac find_inversion_go :=
  match goal with
  | [ H : Some ?x = Some ?y |- _ ] => apply some_inj in H; try (subst x || subst y)
  | [H:Go.Val ?t ?a = Go.Val ?t ?b |- _ ] =>
        (unify a b; fail 1) ||
          assert (a = b) by (eapply (Go.value_inj H));
         try (subst a || subst b);
         try discriminate; try find_inversion_safe
  | [ H : Go.Here ?a = Go.Here ?b |- _ ] =>
    apply Here_inj in H; try (subst a || subst b)
  | [ H: Go.Val ?ta _ = Go.Val ?tb _,
      H':?ta = ?tb |- _ ] => fail 1 (* Don't bother if the equality exists *)
  | [ H: Go.Val ?ta _ = Go.Val ?tb _ |- _ ] =>
    (unify ta tb; fail 2) ||
     (assert (ta = tb) by (eapply Val_type_inj; eauto);
     try (subst ta || subst tb);
     try discriminate; try find_inversion_safe)
  end || find_inversion_safe.