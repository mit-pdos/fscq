Require Import Hoare.
Require Import Prog.
Require Import Pred.

Parameter recover : prog -> prog.
Parameter rpre : pred.
Parameter rpost : pred.
Parameter rpost2 : pred.

Definition preserves_precondition (pre : pred) p :=
  forall m m' out, pre m -> exec m p m' out -> pre m' /\ out <> Failed.

Axiom recover_preserves: forall rx, preserves_precondition rpre (recover rx).

Theorem idempotent_ok : forall p p1 p2,
  preserves_precondition rpre p ->
  p1 = p ->
  p2 = p ->
  {{ rpre
  }} p1 >> p2.
Proof.
  unfold corr at 1.
  intros.

  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => induction H; subst; auto
  end.

  edestruct H; eauto; congruence.
  apply IHexec_recover; auto.
  edestruct H; eauto.
Qed.
