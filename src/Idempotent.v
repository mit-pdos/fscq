Require Import Hoare.
Require Import Prog.
Require Import Pred.
Require Import SepAuto.

Theorem corr2_from_corr3: forall T (p: prog T) pre, {{ pre }} p >> Done tt
  -> {{ fun done crash => pre done (fun _ => crash) }} p.
Proof.
  unfold corr2; intros.
  destruct out.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - edestruct H; eauto; repeat deex.
    + inversion H3; subst.
      left. repeat eexists; eauto.
    + inversion H3; subst.
  - edestruct H; eauto; repeat deex.
    + inversion H3; subst.
    + inversion H3; subst.
      right. repeat eexists; eauto.
Qed.

Lemma corr3_from_corr2_failed:
  forall (TF TR: Type) m (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r,
  exec_recover m p r out
  -> TF = TR
  -> crash m
  -> (crash =p=> ppre crashdone_p crash)
  -> (crash =p=> rpre crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out <> RFailed TF TR.
Proof.
  intros.
  induction H; try congruence.
  - edestruct H4; eauto.
    destruct H6. destruct H6. destruct H6. congruence.
    destruct H6. destruct H6. congruence.
  - rewrite H0. eapply IHexec_recover; eauto.
    edestruct H4; eauto.
    destruct H7. destruct H7. destruct H7. congruence.
    destruct H7. destruct H7. inversion H7. congruence.
Qed.

Lemma corr3_from_corr2_finished:
  forall (TF TR: Type) m (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r m' v,
  exec_recover m p r out
  -> TF = TR
  -> crash m
  -> (crash =p=> ppre crashdone_p crash)
  -> (crash =p=> rpre crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RFinished TR m' v
  -> crashdone_p v m'.
Proof.
  intros.
  induction H; try congruence.
  edestruct H4; eauto.
  - destruct H7. destruct H7. destruct H7.
    inversion H7. congruence.
  - destruct H7. destruct H7. congruence.
Qed.

Lemma corr3_from_corr2_recovered:
  forall (TF TR: Type) m (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r m' v,
  exec_recover m p r out
  -> TF = TR
  -> crash m
  -> (crash =p=> ppre crashdone_p crash)
  -> (crash =p=> rpre crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RRecovered TF m' v
  -> crashdone_r v m'.
Proof.
  intros.
  induction H; try congruence.
  - eapply corr3_from_corr2_finished; eauto; try congruence.
    clear IHexec_recover H7.
    edestruct H4; eauto.
    + destruct H7. destruct H7. destruct H7. congruence.
    + destruct H7. destruct H7. congruence.
  - eapply IHexec_recover; eauto; clear IHexec_recover H7.
    + edestruct H4; eauto.
      * destruct H7. destruct H7. destruct H7. congruence.
      * destruct H7. destruct H7. congruence.
    + inversion H6. auto.
Qed.

Theorem corr3_from_corr2: forall TF TR (p: prog TF) (r: prog TR) ppre rpre, {{ ppre }} p
  -> {{ rpre }} r
  -> {{ fun done crashdone => exists crash,
        ppre done crash * [[ crash =p=> rpre crashdone crash ]] }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H1. rename x into crash.
  apply sep_star_lift2and in H1; unfold lift in H1; destruct H1.
  inversion H2; subst.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - repeat eexists; intuition eauto; try congruence.
    edestruct H; eauto; repeat deex; try congruence.
    inversion H6; subst; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H7; clear H7; subst.
    exfalso.
    clear H H1 H2 H4 ppre p done m.
    eapply corr3_from_corr2_failed; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H7; clear H7; subst.
    clear H H1 H2 H4 ppre p m.
    right. exists m''; exists v. intuition.
    eapply corr3_from_corr2_finished; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H7; clear H7; subst.
    clear H H1 H2 H4 ppre p m.
    right. exists m''; exists v. intuition.
    eapply corr3_from_corr2_recovered; eauto.
Qed.
