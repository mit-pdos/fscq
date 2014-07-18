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

Lemma wf_loopfreeN':
  forall (x y:A) (n:nat),
  step x y -> starN step n y x -> False.
Proof.
  unfold not; intro x; assert (Acc step x); auto.
  induction H; intros.
  inversion H2; subst.
  - exact (wf_norefl H1).
  - destruct (starN_last H3 H4).
    apply H0 with (y:=x0) (y0:=x) (n:=(S n0)); intuition.
    eapply starN_step; eauto.
Qed.

Lemma wf_loopfreeN:
  forall (x y:A) (n0 n1:nat),
  starN step n0 x y -> starN step n1 y x -> n0 = 0 /\ n1 = 0.
Proof.
  intros. inversion H; subst.
  - split; auto.
    destruct n1; auto.
    inversion H0; subst.
    destruct (wf_loopfreeN' H2 H3).
  - assert (starN step (n+n1) s' x). eapply starN_trans; eauto.
    destruct (wf_loopfreeN' H1 H3).
Qed.

Lemma wf_loopfree:
  forall (x y:A),
  star step x y -> star step y x -> x = y.
Proof.
  intros.
  destruct (star_starN H).
  destruct (star_starN H0).
  destruct (wf_loopfreeN H1 H2).
  subst. inversion H2. auto.
Qed.

End LOOPFREE.
