Require Import Hoare.
Require Import Prog.
Require Import Pred PredCrash.
Require Import SepAuto.
Require Import Hashmap.

Lemma exec_crashed_hashmap_subset : forall T m m' hm hm' p out,
  exec m hm p out
  -> out = Crashed T m' hm'
  -> exists l, hashmap_subset l hm hm'.
Proof.
  intros.
  induction H; intuition.
  - inversion H; subst; auto.
    inversion H2; subst.
    assert (Hhm: exists l, hashmap_subset l hm (upd_hashmap' hm (hash_fwd buf) buf)).
      econstructor. solve_hashmap_subset.
    inversion Hhm.
    solve_hashmap_subset.
  - inversion H0.
  - inversion H0. solve_hashmap_subset.
  - inversion H0.
Qed.

Ltac solve_hashmap_subset' :=
  match goal with
  | [ H: exec _ _ _ (Crashed _ _ _), Hpre: forall (_ : hashmap), _ =p=> ?pre _ _ _
      |- forall (_ : hashmap), _ =p=> ?pre _ _ _ ]
    => eapply exec_crashed_hashmap_subset in H as H'; eauto;
        intros;
        eapply pimpl_trans; try apply Hpre;
        autorewrite with crash_xform; cancel
  | [ |- context[hashmap_subset] ]
        => pred_apply; cancel
  end; try solve [
    repeat match goal with
    | [ H: forall (_ : hashmap), _ =p=> _ |- _ ] => clear H
    end; solve_hashmap_subset
  ].

Lemma corr3_from_corr2_failed:
  forall (TF TR: Type) m mr hmr (p: prog TF) (r: prog TR) out
         (crash: pred) ppre rpre crashdone_p crashdone_r,
  exec_recover mr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash m
  -> (forall hm', crash_xform (crash
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out <> RFailed TF TR.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    apply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    repeat econstructor.
    repeat (destruct H7; try congruence).
    repeat (destruct H7; try congruence).
  - rewrite H0. eapply IHexec_recover; eauto.
    + eapply exec_crashed_hashmap_subset with (hm':=hm') in H as H'.
      intros.
      eapply pimpl_trans; try apply H4.
      autorewrite with crash_xform; cancel.
      inversion H11; inversion H'.
      eexists. clear H3. solve_hashmap_subset.
      eauto.
    + solve_hashmap_subset'.
    + edestruct H5; eauto.
      apply H3. eapply crash_xform_apply; eauto.
      solve_hashmap_subset'.
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
  -> (forall hm', crash_xform (crash
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre hm' crashdone_p crash)
  -> (forall hm', (crash_xform crash
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RFinished TR m' hm' v
  -> crashdone_p v m'.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - apply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    eexists. econstructor.
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
  -> (forall hm', crash_xform (crash
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre hm' crashdone_r crash)
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
      pred_apply; cancel.
      eexists. clear H3. solve_hashmap_subset.
    + repeat (destruct H2; try congruence).
    + destruct H2. destruct H2. destruct H2.
      inversion H2. eauto.
    + solve_hashmap_subset'.
    + solve_hashmap_subset'.
    + instantiate (1:=hm'). congruence.
  - eapply IHexec_recover; eauto; clear IHexec_recover H2.
    + solve_hashmap_subset'.
    + solve_hashmap_subset'.
    + inversion H7. auto.
    + edestruct H5; eauto.
      * apply H3. eapply crash_xform_apply; eauto.
        solve_hashmap_subset'.
      * repeat (destruct H2; try congruence).
      * repeat (destruct H2; try congruence).
Qed.

Theorem corr3_from_corr2: forall TF TR (p: prog TF) (r: prog TR) ppre rpre, {{ ppre }} p
  -> {{ rpre }} r
  -> {{ fun hm done crashdone => exists crash,
        ppre hm done crash
        * [[ forall hm',
          crash_xform crash
          * [[ exists l, hashmap_subset l hm hm' ]]
          =p=> rpre hm' crashdone crash ]] }} p >> r.
Proof.
  unfold corr3; intros.
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
    eapply corr3_from_corr2_failed; eauto.
    solve_hashmap_subset'.
    solve_hashmap_subset'.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 ppre.
    right. repeat eexists.
    eapply corr3_from_corr2_finished; eauto.
    solve_hashmap_subset'.
    solve_hashmap_subset'.
  - edestruct H; eauto; repeat deex; try congruence.
    inversion H8; clear H8; subst.
    clear H H1 H2 ppre.
    right. repeat eexists.
    eapply corr3_from_corr2_recovered; eauto.
    solve_hashmap_subset'.
    solve_hashmap_subset'.
Qed.

Theorem corr3_from_corr2_rx :
  forall TF TR RF RR (p: _ -> prog TF) (r: _ -> prog TR)
         (rxp : RF -> prog TF) (rxr : RR -> prog TR)
         ppre rpre,
  {{ ppre }} progseq p rxp
  -> {{ rpre }} progseq r rxr
  -> {{ fun hm done crashdone => exists crash,
        ppre hm done crash
        * [[ forall hm',
          crash_xform crash
          * [[ exists l, hashmap_subset l hm hm' ]]
          =p=> rpre hm' crashdone crash ]] }} p rxp >> r rxr.
Proof.
  unfold progseq; intros.
  apply corr3_from_corr2; eauto.
Qed.
