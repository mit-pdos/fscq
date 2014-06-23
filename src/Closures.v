Require Import List.
Require Import Arith.
Import ListNotations.

Section CLOSURES.

Variable state: Type.
Variable step: state -> state -> Prop.

Inductive star: state -> state -> Prop :=
  | star_refl: forall s,
      star s s
  | star_step: forall s1 s2 s3,
      step s1 s2 -> star s2 s3 -> star s1 s3
  .

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
  star s1 s3 -> s1 <> s3 -> step s1 s2 -> star s2 s3.
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
      step s1 s2 -> star s2 s3 -> plus s1 s3
  .

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

End CLOSURES.
