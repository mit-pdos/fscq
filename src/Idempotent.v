Require Import Hoare.
Require Import Prog.
Require Import Pred.

Definition preserves_precondition (pre : pred) p :=
  forall m m' out, pre m -> exec m p m' out -> pre m' /\ out <> Failed.

Theorem idempotent_ok' : forall p p1 p2 pre,
  preserves_precondition pre p ->
  p1 = p ->
  p2 = p ->
  {{ pre }} p1 >> p2.
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

Theorem idempotent_ok : forall p pre,
  preserves_precondition pre p ->
  {{ pre }} p >> p.
Proof.
  intros.
  eapply idempotent_ok'; eauto.
Qed.

Parameter recover : prog -> prog.
Parameter rpre : pred.

Axiom recover_preserves : forall rx, preserves_precondition rpre (recover rx).

Theorem recover_idempotent : forall rx,
  {{ rpre }} recover rx >> recover rx.
Proof.
  intros.
  apply idempotent_ok.
  apply recover_preserves.
Qed.

Theorem corr_to_pp : forall p1 p2 pre1 pre2,
  {{ pre1 }} p1 >> p2 ->
  (pre1 ==> [ {{ pre2 }} p2 >> p2 ]) ->
  (pre1 ==> [ pre2 ==> pre1 ]) ->
  preserves_precondition pre1 p1.
Proof.
  unfold preserves_precondition.
  intros.
  unfold corr in H.
  