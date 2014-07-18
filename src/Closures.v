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

Lemma star_one:
  forall s1 s2, step s1 s2 -> star s1 s2.
Proof.
  intros. eapply star_step; eauto. apply star_refl.
Qed.

Lemma star_two:
  forall s1 s2 s3,
  step s1 s2 -> step s2 s3 -> star s1 s3.
Proof.
  intros. eapply star_step; eauto. apply star_one; auto. 
Qed.

Lemma star_three:
  forall s1 s2 s3 s4,
  step s1 s2 -> step s2 s3 -> step s3 s4 -> star s1 s4.
Proof.
  intros. eapply star_step; eauto. eapply star_two; eauto.
Qed.

Lemma star_trans:
  forall s1 s2, star s1 s2 ->
  forall s3, star s2 s3 -> star s1 s3.
Proof.
  induction 1; intros.
  simpl. auto.
  eapply star_step; eauto.
Qed.

Lemma star_right:
  forall s1 s2 s3,
  star s1 s2 -> step s2 s3 -> star s1 s3.
Proof.
  intros. eapply star_trans. eauto. apply star_one. eauto.
Qed.

Hypothesis step_determ : (forall s t t', step s t -> step s t' -> t = t').

Lemma star_inv:
  forall s1 s2 s3,
  star s1 s3 -> step s1 s2 -> s1 <> s3 -> star s2 s3.  (* old version *)
  (* XXX star s1 s3 -> s1 <> s3 -> step s1 s2 -> star s2 s3.  new version *)
Proof.
  intros; inversion H. contradiction.
  subst; assert (s2=s4). eapply step_determ; eauto. subst; auto.
Qed.

Lemma star_stuttering:
  forall s1 s2,
  star s1 s2 -> step s1 s1 -> s1 = s2.
Proof.
  intros s1 s2.
  induction 1; intros; auto.
  assert (s1=s2); [ eapply step_determ; eauto | subst ].
  apply IHstar; auto.
Qed.

Inductive plus : state -> state -> Prop :=
  | plus_left: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> plus s1 s3.

Inductive starN : nat -> state -> state -> Prop :=
  | starN_refl: forall s,
      starN O s s
  | starN_step: forall n s s' s'',
      step s s' -> starN n s' s'' ->
      starN (S n) s s''.

Remark starN_star:
  forall n s s', starN n s s' -> star s s'.
Proof.
  induction 1; econstructor; eauto.
Qed.

Remark star_starN:
  forall s s', star s s' -> exists n, starN n s s'.
Proof.
  induction 1. 
  exists O; constructor.
  destruct IHstar as [n P]. exists (S n); econstructor; eauto.
Qed.

Lemma starN_last:
  forall {n s1 s2 s3},
  step s1 s2 -> starN n s2 s3 ->
  exists s2', starN n s1 s2' /\ step s2' s3.
Proof.
  induction n; intros; inversion H0; subst.
  - exists s1. split; [ constructor | auto ].
  - destruct (IHn s2 s' s3); auto.
    exists x. split; intuition. eapply starN_step; eauto.
Qed.

Lemma starN_trans:
  forall s1 s2 n1, starN n1 s1 s2 ->
  forall s3 n2, starN n2 s2 s3 -> starN (n1+n2) s1 s3.
Proof.
  induction 1; intros.
  simpl. auto.
  eapply starN_step; eauto.
Qed.

Lemma star_last:
  forall {s1 s2 s3},
  step s1 s2 -> star s2 s3 ->
  exists s2', star s1 s2' /\ step s2' s3.
Proof.
  intros.
  destruct (star_starN H0).
  destruct (starN_last H H1).
  exists x0.
  split; try apply starN_star with (n:=x); intuition.
Qed.

Definition opposite_rel := fun b a => step a b.

End CLOSURES.

Remark opposite_star:
  forall (A:Type) (a b:A) step,
  star step a b -> star (opposite_rel step) b a.
Proof.
  intros; induction H; subst.
  - constructor.
  - apply star_trans with (s2:=s2); auto.
    apply star_step with (s2:=s1). auto. constructor.
Qed.

Remark opposite_starN:
  forall (A:Type) (a b:A) (n:nat) step,
  starN step n a b -> starN (opposite_rel step) n b a.
Proof.
  intros; induction H; subst.
  - constructor.
  - assert (S n = n+1) as HSn. crush. rewrite HSn.
    eapply starN_trans. eauto.
    eapply starN_step. unfold opposite_rel. eauto. constructor.
Qed.

Lemma starN_proj:
  forall (A:Type) (B:Type) (step1:A->A->Prop) (step2:B->B->Prop) (proj:A->B),
  (forall x y, step1 x y -> step2 (proj x) (proj y)) ->
  forall a b n, starN step1 n a b -> starN step2 n (proj a) (proj b).
Proof.
  intros.
  induction H0.
  - constructor.
  - eapply starN_step.
    apply H. exact H0.
    auto.
Qed.
