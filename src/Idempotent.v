Require Import Hoare.
Require Import Prog.
Require Import Pred PredCrash.
Require Import SepAuto.

Lemma corr3_from_corr2_failed:
  forall (TF TR: Type) m mr hmr (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r,
  exec_recover mr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash m
  -> (crash_xform crash =p=> ppre crashdone_p crash)
  -> (crash_xform crash =p=> rpre crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out <> RFailed TF TR.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    apply H3. eapply crash_xform_apply; eauto.
    repeat (destruct H7; try congruence).
    repeat (destruct H7; try congruence).
  - rewrite H0. eapply IHexec_recover.
    eauto. eauto. eauto. eauto. eauto. eauto.
    edestruct H5; eauto.
    apply H3. eapply crash_xform_apply; eauto.
    repeat (destruct H9; try congruence).
    repeat (destruct H9; try congruence).
Qed.

Lemma corr3_from_corr2_finished:
  forall (TF TR: Type) m mr hmr (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r m' hm' v,
  exec_recover mr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash m
  -> (crash_xform crash =p=> ppre crashdone_p crash)
  -> (crash_xform crash =p=> rpre crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RFinished TR m' hm' v
  -> crashdone_p v m'.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - apply H3. eapply crash_xform_apply; eauto.
  - destruct H8. destruct H8. destruct H8.
    inversion H8. congruence.
  - repeat (destruct H8; try congruence).
Qed.

Lemma corr3_from_corr2_recovered:
  forall (TF TR: Type) m mr hmr (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r m' hm' v,
  exec_recover mr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash m
  -> (crash_xform crash =p=> ppre crashdone_p crash)
  -> (crash_xform crash =p=> rpre crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RRecovered TF m' hm' v
  -> crashdone_r v m'.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - eapply corr3_from_corr2_finished; eauto.
    clear IHexec_recover H2.
    edestruct H5; eauto.
    + apply H3. eapply crash_xform_apply; eauto.
    + repeat (destruct H2; try congruence).
    + repeat (destruct H2; try congruence).
    + instantiate (hm':=hm'). congruence.
  - eapply IHexec_recover; eauto; clear IHexec_recover H2.
    + inversion H7. auto.
    + edestruct H5; eauto.
      * apply H3. eapply crash_xform_apply; eauto.
      * repeat (destruct H2; try congruence).
      * repeat (destruct H2; try congruence).
Qed.

Theorem corr3_from_corr2: forall TF TR (p: prog TF) (r: prog TR) ppre rpre, {{ ppre }} p
  -> {{ rpre }} r
  -> {{ fun done crashdone => exists crash,
        ppre done crash * [[ crash_xform crash =p=> rpre crashdone crash ]] }} p >> r.
Proof.
  unfold corr3, corr3'; intros.
  destruct H1 as [crash H1].
  destruct_lift H1.
  inversion H2; subst.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - left.
    repeat eexists.
    edestruct H; eauto; repeat deex; try congruence.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 H3 ppre p done m.
    eapply corr3_from_corr2_failed; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 H3 ppre p m.
    right. repeat eexists. intuition.
    eapply corr3_from_corr2_finished; eauto.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 H3 ppre p m.
    right. repeat eexists. intuition.
    eapply corr3_from_corr2_recovered; eauto.
Qed.

Theorem corr3_from_corr2_rx :
  forall TF TR RF RR (p: _ -> prog TF) (r: _ -> prog TR)
         (rxp : RF -> prog TF) (rxr : RR -> prog TR)
         ppre rpre,
  {{ ppre }} progseq p rxp
  -> {{ rpre }} progseq r rxr
  -> {{ fun done crashdone => exists crash,
        ppre done crash * [[ crash_xform crash =p=> rpre crashdone crash ]] }} p rxp >> r rxr.
Proof.
  unfold progseq; intros.
  apply corr3_from_corr2; eauto.
Qed.
