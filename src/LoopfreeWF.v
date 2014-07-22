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
  intro a; hnf; induction (WF a); eauto.
Qed.

Theorem wf_norefl':
  forall (a:A),
  step a a -> False.
Proof.
  exact wf_norefl.
Qed.

Lemma wf_loopfreeN':
  forall (x y:A) (n:nat),
  step x y -> starN step n y x -> False.
Proof.
  intro x; induction (WF x); inversion 2; subst;
    eauto using wf_norefl';
      edestruct starN_last; [ | eassumption | ]; intuition eauto.
Qed.

Lemma wf_loopfreeN:
  forall (x y:A) (n0 n1:nat),
  starN step n0 x y -> starN step n1 y x -> n0 = 0 /\ n1 = 0.
Proof.
  destruct 1; inversion 1; subst; intuition;
    exfalso; eauto using wf_loopfreeN', starN_trans.
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
