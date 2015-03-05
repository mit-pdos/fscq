Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg Array.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Section BIJECTION.

  Variables A B : Type.
  Definition injective (f : A -> B) := forall x y : A, f x = f y -> x = y.
  Definition surjective (f : A -> B) := forall y : B, {x : A | f x = y}.

  Inductive bijective (f : A -> B) : Type :=
    is_bijective : injective f -> surjective f -> bijective f.

  Definition left_inverse (f : A -> B) (f' : B -> A) := 
    forall x : A, f' (f x) = x.

  Definition right_inverse (f : A -> B) (f' : B -> A) := 
    forall y : B, f (f' y) = y.

  Definition inverse f f' := 
    left_inverse f f' /\ right_inverse f f'.

  Lemma left_inv_inj f f' : left_inverse f f' -> injective f.
  Proof.
    intros H x y H0.
    rewrite <- (H x).
    rewrite H0.
    apply H.
  Qed.

  Lemma right_inv_surj f f' : right_inverse f f' -> surjective f.
  Proof.
    intros H y.
    rewrite <- (H y).
    exists (f' y); auto.
  Qed.

  Lemma inv2bij f f' : inverse f f' -> bijective f.
  Proof.
    intros [H1 H2].
    constructor.
    eapply left_inv_inj; eauto.
    eapply right_inv_surj; eauto.
  Qed.

  Lemma bij2inj f a b :
    bijective f -> f a = f b -> a = b.
  Proof.
    intros.
    apply X; auto.
  Qed.

End BIJECTION.



Section MEMMATCH.

  Variable AT1 : Type.
  Variable AEQ1 : DecEq AT1.
  Variable V1 : Type.
  Variable AT2 : Type.
  Variable AEQ2 : DecEq AT2.
  Variable V2 : Type.
  Variable atrans : AT1 -> AT2.
  Variable vprd : V1 -> V2 -> Prop.
  Hypothesis atrans_bijective : bijective atrans.

  Definition mem_trans_a (m1 : @mem AT1 AEQ1 V1) (m2 : @mem AT2 AEQ2 V1) :=
    forall a1, m1 a1 = m2 (atrans a1).

  Definition mem_match_v (m1 : @mem AT1 AEQ1 V1) (m2 : @mem AT1 AEQ1 V2) :=
    forall a, (m1 a = None /\ m2 a = None) \/
              (exists v1 v2, m1 a = Some v1 /\ m2 a = Some v2 /\ vprd v1 v2).

  (**
   * XXX fill in theorems as needed..
   *)

End MEMMATCH.
