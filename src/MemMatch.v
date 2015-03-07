Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg Array.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.

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


(* bijection on restricted domain *)

Section BIJECTION_SIG.

  Variables A B : Type.
  Variable f : A -> B.
  Variable PA : A -> Prop.
  Variable PB : B -> Prop.

  Definition cond_injective :=
    forall x y : A, PA x -> PA y -> f x = f y -> x = y.

  Definition cond_surjective :=
    forall y : B, PB y -> {x : A | PA x /\ f x = y}.

  Inductive cond_bijective :=
    CondBijective : cond_injective -> cond_surjective -> cond_bijective.

  Section BIJECTION_INVERSION.

    Variable f' : B -> A.

    Definition cond_left_inverse := 
      forall x : A, PA x -> PB (f x) /\ f' (f x) = x.

    Definition cond_right_inverse := 
      forall y : B, PB y -> PA (f' y) /\ f (f' y) = y.

    Definition cond_inverse := 
      cond_left_inverse /\ cond_right_inverse.

    Lemma cond_left_inv_inj : cond_left_inverse -> cond_injective.
    Proof.
      intros H x y P1 P2 H0.
      pose proof (H x P1) as [P3 P4].
      rewrite <- P4.
      rewrite H0.
      apply H.
      auto.
    Qed.

    Lemma cond_right_inv_surj : cond_right_inverse -> cond_surjective.
    Proof.
      intros H y P1.
      pose proof (H y P1) as [P2 P3].
      rewrite <- P3.
      exists (f' y); intuition.
    Qed.

    Lemma cond_inv2bij : cond_inverse -> cond_bijective.
    Proof.
      intros [H1 H2].
      constructor.
      eapply cond_left_inv_inj; eauto.
      eapply cond_right_inv_surj; eauto.
    Qed.

    Lemma cond_inv_rewrite_right : forall y,
      cond_inverse -> PB y -> f (f' y) = y.
    Proof.
      intros; apply H; auto.
    Qed.

    Lemma cond_inv_rewrite_left : forall x,
      cond_inverse -> PA x -> f' (f x) = x.
    Proof.
      intros; apply H; auto.
    Qed.

  End BIJECTION_INVERSION.

End BIJECTION_SIG.


Section MEMMATCH.

  Variable AT1 : Type.
  Variable AT2 : Type.
  Variable atrans : AT1 -> AT2.

  Variable AEQ1 : DecEq AT1.
  Variable AEQ2 : DecEq AT2.
  Variable V : Type.
  Variable m1 : @mem AT1 AEQ1 V.
  Variable m2 : @mem AT2 AEQ2 V.


  (* restrictions on atrans' domain and codomain *)
  Variable AP1 : AT1 -> Prop.
  Variable AP2 : AT2 -> Prop.

  Definition mem_atrans :=
    forall a1, m1 a1 = m2 (atrans a1).

  Lemma mem_atrans_any : forall a1 x, 
    mem_atrans
    -> m1 a1 = x
    -> m2 (atrans a1) = x.
  Proof.
    intros.
    rewrite <- (H a1); auto.
  Qed.

  Lemma mem_atrans_indomain : forall a1,
    mem_atrans
    -> indomain a1 m1
    -> indomain (atrans a1) m2.
  Proof.
    unfold indomain; intros.
    rewrite <- (H a1); auto.
  Qed.

  Lemma mem_atrans_notindomain : forall a1,
    mem_atrans
    -> notindomain a1 m1
    -> notindomain (atrans a1) m2.
  Proof.
    unfold notindomain; intros.
    apply mem_atrans_any; auto.
  Qed.

  Lemma mem_ainv_any : forall ainv a2 x
    (HInv   : cond_inverse atrans AP1 AP2 ainv)
    (HTrans : mem_atrans)
    (HAP    : AP2 a2)
    (HM1    : m1 (ainv a2) = x),
    m2 a2 = x.
  Proof.
    intros.
    replace a2 with (atrans (ainv a2)).
    rewrite <- (HTrans (ainv a2)); auto.
    apply HInv; auto.
  Qed.

  Lemma mem_atrans_inv_ptsto : forall F ainv (a : AT2) v,
    cond_inverse atrans AP1 AP2 ainv
    -> AP2 a
    -> (F * (ainv a) |-> v)%pred m1
    -> mem_atrans -> (any * a |-> v)%pred m2.
  Proof.
    intros.
    apply any_sep_star_ptsto.
    eapply mem_ainv_any; eauto.
    eapply ptsto_valid'; eauto.
  Qed.

  Lemma mem_atrans_inv_notindomain : forall ainv (a : AT2),
    cond_inverse atrans AP1 AP2 ainv
    -> AP2 a
    -> notindomain (ainv a) m1
    -> mem_atrans -> notindomain a m2.
  Proof.
    unfold notindomain; intros.
    eapply mem_ainv_any; eauto.
  Qed.

End MEMMATCH.



