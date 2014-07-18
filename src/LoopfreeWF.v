Require Import CpdtTactics.
Require Import Closures.

Set Implicit Arguments.

Section LOOPFREE.

Variable A: Type.
Variable step: A -> A -> Prop.
Variable WF: well_founded step.
Hint Resolve WF.

Theorem wf_norefl:
  forall (a:A),
  ~step a a.
Proof.
  unfold not; intros; assert (Acc step a); auto.
  induction H0; eapply H1; apply H.
Qed.

Lemma wf_loopfree':
  forall (x y:A),
  step x y -> star step y x -> False.
Proof.
  unfold not; intro x; assert (Acc step x); auto.
  induction H; intros.
  inversion H2; subst.
  - exact (wf_norefl H1).
  - destruct (star_last H3 H4).
    apply H0 with (y:=x0) (y0:=x); intuition.
    eapply star_step; eauto.
Qed.

Lemma wf_loopfree:
  forall (x y:A),
  star step x y -> star step y x -> x = y.
Proof.
  intros; inversion H; auto; subst.
  assert (star step s2 x). eapply star_trans; eauto.
  destruct (wf_loopfree' H1 H3).
Qed.

End LOOPFREE.
