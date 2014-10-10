Require Import Hoare.
Require Import Prog.
Require Import Pred.

Definition preserves_precondition (pre : pred) p :=
  forall m m' out, pre m -> exec m p m' out -> pre m' /\ out <> Failed.

Theorem pp_add_lift : forall pre P p,
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

Theorem pp_drop_lift : forall pre (P : Prop) p,
  P ->
  preserves_precondition (pre * [[ P ]]) p ->
  preserves_precondition pre p.
Proof.
  unfold preserves_precondition; intros.
  edestruct H0; clear H0; eauto.
  apply sep_star_and2lift. split; eauto.
  apply sep_star_lift2and in H3; destruct H3.
  eauto.
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

(*
Theorem corr_to_pp : forall p1 p2 pre1 pre2,
  {{ pre1 }} p1 >> Check pre2 ;; p2 ->
  (pre1 ==> [ pre2 ==> pre1 ]) ->
  preserves_precondition pre1 p1.
Proof.
  unfold preserves_precondition.
  intros.
  unfold corr in H.
  destruct out.
  - exfalso.
    destruct (H m RFailed); eauto.
  - do 2 eexists; split; eauto.

    assert (exec m p1 (Stopped m0 Crashed)) by ( eapply prog_can_crash; eauto ).
    clear H2.

    assert (forall out, exec m0 (Check pre2 ;; p2) out -> out <> Failed).
    + unfold not in *; intros; subst; eauto.
    + destruct (exec_need_not_crash (Check pre2 ;; p2) m0).
      destruct H4.
      inversion H4; subst.
      * exfalso. edestruct H2; eauto.
      * eapply H0; eauto.
Qed.
*)

(* Sketch of how we might prove recover's idempotence *)

Parameter xrecover : prog -> prog.
Parameter log_intact : mem -> pred.
Parameter recovered : mem -> pred.

Theorem recover_base_ok : forall rx id,
  {{ exists m, log_intact m
   * [[ guardcond (Done id tt) = log_intact m ]]
   * [[ {{ recovered m }} rx >> Done id tt ]]
  }} xrecover rx >> Done id tt.
Admitted.

Theorem recover_preserves : forall rx,
  preserves_precondition
    (log_intact
   * [[ {{ recovered }} rx >> Check log_intact ;; Done tt ]])
    (xrecover rx).
Proof.
  intros.
  eapply corr_to_pp.
  eapply pimpl_ok. apply recover_base_ok. apply pimpl_refl.
  repeat ( apply sep_star_lift_l; intros ).
  unfold lift, pimpl; intros.
  repeat ( apply sep_star_and2lift; unfold lift; split; eauto ).
Qed.

Theorem recover_idempotent_ok : forall rx,
  {{ log_intact
   * [[ {{ recovered }} rx >> Check log_intact ;; Done tt ]]
  }} xrecover rx >> xrecover rx.
Proof.
  intros.
  apply idempotent_ok.
  apply recover_preserves.
Qed.
