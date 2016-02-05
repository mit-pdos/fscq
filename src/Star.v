Set Implicit Arguments.

(** STAR provides a type star to represent repeated applications of
    an arbitrary binary relation R over values in A.

    We will use star here to represent the transitive closure of an
    action; that is, star a is an action where there is some sequence
    m1 m2 ... mN where a m1 m2, a m2 m3, ... a mN-1 mN hold. *)
Section STAR.

  Variable A : Type.
  Definition relation := A -> A -> Prop.
  Variable R : relation.

  Infix "-->" := R (at level 55).

  Reserved Notation "s1 -->* s2" (at level 50).

  Inductive star : relation :=
  | star_refl : forall s,
    s -->* s
  | star_step : forall s1 s2 s3,
    s1 --> s2 ->
    s2 -->* s3 ->
    s1 -->* s3
  where "s1 -->* s2" := (star s1 s2).

  Hint Constructors star.

  Reserved Notation "s1 ==>* s2" (at level 50).

  Inductive star_r : relation :=
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

  Theorem star_one_step : forall s s',
      R s s' ->
      star s s'.
  Proof.
    eauto.
  Qed.

  Theorem star_invariant : forall (P : A -> Prop) (Q : relation),
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

Theorem star_impl : forall A (r1 r2 : A -> A -> Prop) s1 s2,
  (forall p q, r1 p q -> r2 p q) ->
  star r1 s1 s2 ->
  star r2 s1 s2.
Proof.
  induction 2; eauto.
Qed.

Require Import Morphisms.

Definition rimpl {A} (r1 r2: relation A) :=
  forall s s', r1 s s' -> r2 s s'.

Instance star_rimpl_proper {A} :
  Proper (rimpl ==> eq ==> eq ==> Basics.impl) (@star A).
Proof.
  unfold Proper, Basics.impl, respectful, rimpl; intros.
  subst.
  match goal with
  | [ H: star _ _ _ |- _ ] =>
    induction H; eauto
  end.
Qed.

Section RewriteExample.

Require Import Setoid.

(* example of rewriting under star *)
Goal forall A (R1 R2 : relation A),
  rimpl R1 R2 ->
  forall s s',
  star R1 s s' ->
  star R2 s s'.
Proof.
  intros.
  rewrite H in H0.
  assumption.
  Fail idtac "no more goals".
Abort.

End RewriteExample.