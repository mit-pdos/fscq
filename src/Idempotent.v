Require Import Hoare.
Require Import Prog.
Require Import Pred.
Require Import SepAuto.
Require Import Eqdep.

Ltac do_inj_pair2 :=
  repeat match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; subst
  end.

Theorem corr3_from_corr2: forall p r ppre rpre, {{ ppre }} p
    -> {{ rpre }} r
    -> {{ fun done crashdone => exists crash,
          (ppre done crash * [[ crash ==> rpre crashdone crash ]]) }} p >> r.
Proof.
  unfold corr3; intros.
  edestruct H1. apply sep_star_lift2and in H3. unfold lift in H3; destruct H3.
  inversion H2; subst.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - repeat eexists; intuition eauto; try congruence.
    edestruct H; eauto; repeat deex; try congruence.
    inversion H8; subst; do_inj_pair2; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    exfalso.
    clear H H1 H2 H3 H5 ppre p done m. 
    assert (exists x, x = r) as Hx by eauto. destruct Hx.
    rewrite <- H in H6 at 1.
    assert (exists x, x = RFailed) as Hx by eauto. destruct Hx.
    rewrite <- H1 in H6.
    induction H6; subst; try congruence.
    + edestruct H0; eauto; repeat deex; try congruence.
    + eapply IHexec_recover; eauto.
      edestruct H0; eauto; repeat deex; try congruence.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 H3 H5 ppre p m.
    assert (exists x, x = r) as Hx by eauto. destruct Hx.
    rewrite <- H in H6 at 1.
    assert (exists x, x = RFinished c m'' v) as Hx by eauto. destruct Hx.
    rewrite <- H1 in H6.
    induction H6; intros; subst; try congruence.
    + inversion H1; clear H1; subst; do_inj_pair2.
      repeat eexists; intros; try congruence.
      edestruct H0; eauto; repeat deex; try congruence.
      admit.
      (* inversion H4; subst; do_inj_pair2.
      eauto. *)
    + inversion H1; clear H1; subst; do_inj_pair2.
      destruct c0.
      * clear IHexec_recover.
        inversion H6; clear H6; subst; do_inj_pair2.
        edestruct H0; [| eapply H7 | .. ].
        eapply H4; clear H7.
        edestruct H0; eauto; repeat deex; try congruence.
        repeat deex. inversion H1; subst; do_inj_pair2.
        repeat eexists; intuition eauto; try congruence.
        repeat deex; try congruence.
      * eapply IHexec_recover; eauto.
        edestruct H0; eauto; repeat deex; try congruence.
Qed.
