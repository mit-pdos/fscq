Set Implicit Arguments.

(** STAR provides a type star to represent repeated applications of
    an arbitrary binary relation R over values in A.

    We will use star here to represent the transitive closure of an
    action; that is, star a is an action where there is some sequence
    m1 m2 ... mN where a m1 m2, a m2 m3, ... a mN-1 mN hold. *)
Section STAR.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Infix "-->" := R (at level 40).

  Reserved Notation "s1 -->* s2" (at level 50).

  Inductive star : A -> A -> Prop :=
  | star_refl : forall s,
    s -->* s
  | star_step : forall s1 s2 s3,
    s1 --> s2 ->
    s2 -->* s3 ->
    s1 -->* s3
  where "s1 -->* s2" := (star s1 s2).

  Hint Constructors star.

  Reserved Notation "s1 ==>* s2" (at level 50).

  Inductive star_r : A -> A -> Prop :=
  | star_r_refl : forall s,
    s ==>* s
  | star_r_step : forall s1 s2 s3,
    s1 ==>* s2 ->
    s2 --> s3 ->
    s1 ==>* s3
  where "s2 ==>* s1" := (star_r s1 s2).

  Hint Constructors star_r.

  Lemma star_r_trans : forall s0 s1 s2,
    s1 ==>* s2 ->
    s0 ==>* s1 ->
    s0 ==>* s2.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve star_r_trans.

  Lemma star_trans : forall s0 s1 s2,
    s0 -->* s1 ->
    s1 -->* s2 ->
    s0 -->* s2.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve star_trans.

  Theorem star_lr_eq : forall s s',
    s -->* s' <-> s ==>* s'.
  Proof.
    intros.
    split; intros;
      induction H; eauto.
  Qed.

  Theorem star_invariant : forall (P : _ -> Prop) (Q : _ -> _ -> Prop),
      (forall s s', P s -> s --> s' -> Q s s') ->
      (forall s, P s -> Q s s) ->
      (forall s s', Q s s' -> P s') ->
      (forall s s' s'', Q s s' -> Q s' s'' -> Q s s'') ->
      forall s s',
        P s -> s -->* s' -> Q s s'.
  Proof.
    intros.
    match goal with
    | [ H : star _ _ |- _ ] =>
      induction H
    end; eauto 10.
  Qed.

End STAR.

Hint Constructors star.
Hint Constructors star_r.