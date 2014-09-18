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

Theorem recover_recursive : forall p,
  preserves_precondition rpre p ->
  {{ rpre
  }} p >> p.
Proof.
  unfold corr at 1.
  intros.
(*
  apply sep_star_lift2and in H.
  destruct H.
  unfold lift in *.
*)

  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => induction H; auto
  end.

(*
  edestruct H.
  eauto.

eauto. congruence.

  edestruct recover_ok; eauto. congruence.
*)

admit.

  apply IHexec_recover; auto.

  remember (recover_ok after) as Hok. clear HeqHok.
  unfold corr at 1 in Hok.

