Require Import CpdtTactics.

Set Implicit Arguments.
Load Closures.

Inductive myprog :=
  | PHalt
  | PNext (cont: nat->myprog).

Record state := St {
  StProg: myprog;
  StVal: nat;
  StCount: nat }.

Inductive step: state -> state -> Prop :=
  | Halt: forall v c, step (St PHalt v c) (St PHalt v (S c))
  | Next: forall v c cont, step (St (PNext cont) v c) (St (cont v) (S v) (S c)).

Lemma counter_increment:
  forall a b,
  step a b -> StCount a < StCount b.
Proof.
  intros.  inversion H; crush.
Qed.

Lemma counter_monotonic:
  forall a b,
  star step a b -> StCount a <= StCount b.
Proof.
  intros.
  induction H.
  - crush.
  - cut (StCount s1 < StCount s2).  crush.  apply counter_increment; crush.
Qed.

Theorem step_loopfree:
  forall a b, star step a b -> star step b a -> a = b.
Proof.
  intros.  inversion H; clear H; inversion H0; clear H0.
  - auto.
  - assert (StCount b < StCount s2); [ apply counter_increment | idtac ]; crush.
  - assert (StCount a < StCount s2); [ apply counter_increment | idtac ]; crush.
  - assert (StCount a < StCount s2); [ apply counter_increment; crush | idtac ].
    assert (StCount s2 <= StCount b); [ apply counter_monotonic; crush | idtac ].
    assert (StCount b < StCount s4); [ apply counter_increment; crush | idtac ].
    assert (StCount s4 <= StCount a); [ apply counter_monotonic; crush | idtac ].
    crush.
Qed.
