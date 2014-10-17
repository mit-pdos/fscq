Require Import Hoare.
Require Import Prog.
Require Import Pred.
Require Import SepAuto.
Require Import Eqdep.

Ltac do_inj_pair2 :=
  repeat match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H; subst
  end.

Theorem corr2_from_corr3: forall p pre, {{ pre }} p >> Done tt
  -> {{ fun done crash => pre done (fun _ _ => crash) }} p.
Proof.
  unfold corr2; intros.
  destruct out.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - edestruct H; eauto; repeat deex.
    inversion H3; subst; do_inj_pair2.
    left. repeat eexists; eauto.
  - edestruct H; eauto; repeat deex.
    inversion H3; subst; do_inj_pair2.
    right. repeat eexists; eauto.
Qed.

Theorem corr3_from_corr2: forall p r ppre rpre, {{ ppre }} p
  -> {{ rpre }} r
  -> {{ fun done crashdone => exists crash,
        ppre done crash * [[ crash ==> rpre crashdone crash ]] }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H1. rename x into crash.
  apply sep_star_lift2and in H1; unfold lift in H1; destruct H1.
  inversion H2; subst.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - repeat eexists; intuition eauto; try congruence.
    edestruct H; eauto; repeat deex; try congruence.
    inversion H7; subst; do_inj_pair2; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H7; clear H7; subst.
    exfalso.
    clear H H1 H2 H4 ppre p done m.
    assert (exists x, x = r) as Hx by eauto. destruct Hx.
    rewrite <- H in H5 at 1.
    assert (exists x, x = RFailed) as Hx by eauto. destruct Hx.
    rewrite <- H1 in H5.
    induction H5; subst; try congruence.
    + edestruct H0; eauto; repeat deex; try congruence.
    + eapply IHexec_recover; eauto.
      edestruct H0; eauto; repeat deex; try congruence.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H7; clear H7; subst.
    clear H H1 H2 H4 ppre p m.
    assert (exists x, x = r) as Hx by eauto. destruct Hx.
    rewrite <- H in H5 at 1.
    assert (exists x, x = RFinished c m'' v) as Hx by eauto. destruct Hx.
    rewrite <- H1 in H5.
    induction H5; intros; subst; try congruence.
    + inversion H1; clear H1; subst; do_inj_pair2.
      repeat eexists; intros; try congruence.
      edestruct H0; eauto; repeat deex; try congruence.
      inversion H4; subst; do_inj_pair2.
      eauto.
    + inversion H1; clear H1; subst; do_inj_pair2.
      destruct c0.
      * clear IHexec_recover.
        inversion H5; clear H5; subst; do_inj_pair2.
        edestruct H0; [| eapply H7 | .. ].
        eapply H3; clear H7.
        edestruct H0; eauto; repeat deex; try congruence.
        repeat deex. inversion H1; subst; do_inj_pair2.
        repeat eexists; intuition eauto; try congruence.
        repeat deex; try congruence.
      * eapply IHexec_recover; eauto.
        edestruct H0; eauto; repeat deex; try congruence.
Qed.
