Require Import CpdtTactics.
Require Import Closures.

Section CountersImplyLoopfree.

Variable STATE: Type.
Variable STEP: STATE -> STATE -> Prop.
Variable COUNTER: STATE -> nat.
Variable INCR: forall a b, STEP a b -> COUNTER a < COUNTER b.

Hint Resolve INCR.

Ltac clear_step := match goal with
  | [ H: STEP ?a ?b |- _ ] => assert (COUNTER a < COUNTER b); [ crush | clear H ]; []
  end.

Lemma counter_monotonic:
  forall a b,
  star STEP a b -> COUNTER a <= COUNTER b.
Proof.
  induction 1; repeat clear_step; crush.
Qed.
Hint Resolve counter_monotonic.

Ltac clear_star_step :=
  match goal with
  | [ H: star STEP ?a ?b |- _ ] => assert (COUNTER a <= COUNTER b); [ crush | clear H]; []
  end.

Theorem star_step_loopfree:
  forall a b,
  star STEP a b -> star STEP b a -> a = b.
Proof.
  inversion 1; inversion 1; repeat clear_step; repeat clear_star_step; crush.
Qed.

End CountersImplyLoopfree.
