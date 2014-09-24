Require Import Hoare.
Require Import Prog.
Require Import Pred.

Definition preserves_precondition (pre : pred) p :=
  forall m m' out, pre m -> exec m p m' out -> pre m' /\ out <> Failed.

Theorem pp_lift : forall pre P p,
  preserves_precondition pre p ->
  preserves_precondition (pre * [[ P ]]) p.
Proof.
  unfold preserves_precondition; intros.
  apply sep_star_lift2and in H0; destruct H0.
  edestruct H; clear H; eauto.
  intuition.
  apply sep_star_and2lift.
  split; eauto.
Qed.

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
  destruct out.
  - assert (Failed = Finished); try discriminate.
    eapply H.
    eauto.
    eauto.
  - split; try discriminate.
    assert (exec m p1 m' Crashed) by ( eapply prog_can_crash; eauto ).
    admit.

  - split; try discriminate.
    assert ({{ pre2 }} p2 >> p2) by firstorder.
    unfold corr in H4.

    destruct (exec_recover_can_terminate p2 p2 m').
    destruct H5.

    assert (x0 = Finished); subst.
    eapply H.
    eauto.
    eapply XRCrashed.
    eauto.
    eauto.

    (* XXX what i really want here is for [{{ pre2 }} p2 >> p2] to be
     * a necessary -- not just sufficient -- precondition for getting
     * a Finished outcome from p2.  then i could prove that indeed
     * p1 establishes pre2 at every crash point, and thus implies that
     * p1 is precondition-preserving.
     *)

    admit.

Qed.
