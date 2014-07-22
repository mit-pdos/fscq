Require Import CpdtTactics.
Require Import List.
Require Import Arith.
Import ListNotations.

Set Implicit Arguments.

Section CLOSURES.

Variable state: Type.
Variable step: state -> state -> Prop.

Inductive star: state -> state -> Prop :=
  | star_refl: forall s,
      star s s
  | star_step: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> star s1 s3.

Hint Constructors star.

Lemma star_one:
  forall s1 s2, step s1 s2 -> star s1 s2.
Proof.
  eauto.
Qed.

Lemma star_two:
  forall s1 s2 s3,
  step s1 s2 -> step s2 s3 -> star s1 s3.
Proof.
  eauto.
Qed.

Lemma star_three:
  forall s1 s2 s3 s4,
  step s1 s2 -> step s2 s3 -> step s3 s4 -> star s1 s4.
Proof.
  eauto.
Qed.

Lemma star_trans:
  forall s1 s2, star s1 s2 ->
  forall s3, star s2 s3 -> star s1 s3.
Proof.
  induction 1; eauto.
Qed.

Lemma star_right:
  forall s1 s2 s3,
  star s1 s2 -> step s2 s3 -> star s1 s3.
Proof.
  eauto using star_trans.
Qed.

Section determ.
Hypothesis step_determ : (forall s t t', step s t -> step s t' -> t = t').

Ltac determ :=
  match goal with
    | [ H : step ?X _, H' : step ?X _ |- _ ] =>
      eapply step_determ in H; [ | apply H' ]; subst
  end.

Lemma star_inv:
  forall s1 s2 s3,
  star s1 s3 -> step s1 s2 -> s1 <> s3 -> star s2 s3.  (* old version *)
  (* XXX star s1 s3 -> s1 <> s3 -> step s1 s2 -> star s2 s3.  new version *)
Proof.
  inversion_clear 1; intuition; determ; auto.
Qed.

Lemma star_stuttering:
  forall s1 s2,
  star s1 s2 -> step s1 s1 -> s1 = s2.
Proof.
  induction 1; intuition; determ; auto.
Qed.

End determ.

Inductive plus : state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> plus s1 s3.

Inductive starN : nat -> state -> state -> Prop :=
  | starN_refl: forall s,
      starN O s s
  | starN_step: forall n s s' s'',
      step s s' -> starN n s' s'' ->
      starN (S n) s s''.

Hint Constructors plus starN.

Remark starN_star:
  forall n s s', starN n s s' -> star s s'.
Proof.
  induction 1; eauto.
Qed.

Remark star_starN:
  forall s s', star s s' -> exists n, starN n s s'.
Proof.
  induction 1; firstorder eauto.
Qed.

Ltac apphyp :=
  match goal with
    | [ H1 : forall x, _, H2 : _ |- _ ] => apply H1 in H2; clear H1
  end.

Lemma starN_last':
  forall {n s2 s3},
  starN n s2 s3 ->
  forall {s1}, step s1 s2 ->
  exists s2', starN n s1 s2' /\ step s2' s3.
Proof.
  induction 1; intuition eauto; apphyp; firstorder eauto.
Qed.

Lemma starN_last:
  forall {n s1 s2 s3},
  step s1 s2 -> starN n s2 s3 ->
  exists s2', starN n s1 s2' /\ step s2' s3.
Proof.
  eauto using starN_last'.
Qed.

Lemma starN_trans:
  forall s1 s2 n1, starN n1 s1 s2 ->
  forall s3 n2, starN n2 s2 s3 -> starN (n1+n2) s1 s3.
Proof.
  induction 1; simpl; eauto using starN_step.
Qed.

Lemma star_last:
  forall {s1 s2 s3},
  step s1 s2 -> star s2 s3 ->
  exists s2', star s1 s2' /\ step s2' s3.
Proof.
  intros; edestruct star_starN; eauto; edestruct @starN_last;
    intuition eauto using starN_star.
Qed.

Definition opposite_rel := fun b a => step a b.

End CLOSURES.

Section hints.
Hint Constructors star plus starN.

Remark opposite_star:
  forall (A:Type) (a b:A) step,
  star step a b -> star (opposite_rel step) b a.
Proof.
  induction 1; eauto using star_trans.
Qed.

Lemma starN_endstep : forall A (step:A -> A -> _) n s s' s'',
  starN step n s s' -> step s' s'' ->
  starN step (S n) s s''.
Proof.
  induction 1; eauto.
Qed.

Remark opposite_starN:
  forall (A:Type) (a b:A) (n:nat) step,
  starN step n a b -> starN (opposite_rel step) n b a.
Proof.
  induction 1; eauto using starN_endstep.
Qed.

Lemma starN_proj:
  forall (A:Type) (B:Type) (step1:A->A->Prop) (step2:B->B->Prop) (proj:A->B),
  (forall x y, step1 x y -> step2 (proj x) (proj y)) ->
  forall a b n, starN step1 n a b -> starN step2 n (proj a) (proj b).
Proof.
  induction 2; eauto.
Qed.
End hints.
