Require Import Hoare.
Require Import Prog ProgMonad.
Require Import Pred PredCrash.
Require Import SepAuto.
Require Import AsyncDisk.
Require Import Hashmap.

Lemma step_hashmap_subset : forall T m vm hm p m' vm' hm' (v: T),
    step m vm hm p m' vm' hm' v ->
    exists l, hashmap_subset l hm hm'.
Proof.
  inversion 1; eauto.
Qed.

Hint Resolve step_hashmap_subset.

Lemma hashmap_subset_some_list_trans : forall hm hm' hm'',
    (exists l, hashmap_subset l hm hm') ->
    (exists l, hashmap_subset l hm' hm'') ->
    exists l, hashmap_subset l hm hm''.
Proof.
  eauto.
Qed.

Lemma finished_val_eq : forall T m vm hm (v:T),
    exists v', Finished m vm hm v = Finished m vm hm v'.
Proof. eauto. Qed.

Hint Resolve finished_val_eq.

Lemma exec_crashed_hashmap_subset' : forall T m m' vm vm' hm hm' p out,
  exec m vm hm p out
  -> (out = Crashed T m' hm' \/ exists v, out = Finished m' vm' hm' v)
  -> exists l, hashmap_subset l hm hm'.
Proof.
  intros.
  generalize dependent vm'.
  generalize dependent hm'.
  generalize dependent m'.
  induction H; subst; intuition; repeat deex; try congruence;
    try match goal with
        | [ H: @eq (outcome _) _ _ |- _ ] =>
          inversion H; subst
        end;
    eauto.

  eauto 7 using hashmap_subset_some_list_trans.
  eauto 7 using hashmap_subset_some_list_trans.

Unshelve.
  all: eauto.
Qed.

Lemma exec_crashed_hashmap_subset : forall T m m' vm hm hm' p out,
  exec m vm hm p out
  -> out = Crashed T m' hm'
  -> exists l, hashmap_subset l hm hm'.
Proof.
  intros.
  eapply exec_crashed_hashmap_subset'; eauto.

Unshelve.
  all: eauto.
Qed.

Ltac solve_hashmap_subset' :=
  match goal with
  | [ H: exec _ _ _ _ (Crashed _ _ _), Hpre: forall (_ : hashmap), _ =p=> ?pre _ _ _
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
  forall (TF TR: Type) m mr vmr hmr (p: prog TF) (r: prog TR) out
         (crash: hashmap -> pred) ppre rpre crashdone_p crashdone_r,
  exec_recover mr vmr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash hmr m
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre vmr hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre Mem.empty_mem hm' crashdone_r crash)
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
    repeat (destruct H7; try congruence).
    repeat (destruct H7; try congruence).
  - rewrite H0. eapply IHexec_recover; eauto.
    + eapply exec_crashed_hashmap_subset with (hm':=hm') in H as H'.
      intros.
      eapply pimpl_trans; try apply H4.
      autorewrite with crash_xform; cancel.
      eauto.
    + solve_hashmap_subset'.
    + edestruct H5; eauto.
      apply H3. eapply crash_xform_apply; eauto.
      solve_hashmap_subset'.
      repeat (destruct H9; try congruence).
      repeat (destruct H9; try congruence).
Qed.

Lemma corr3_from_corr2_finished:
  forall (TF TR: Type) m mr vmr hmr (p: prog TF) (r: prog TR) out
         (crash: hashmap -> pred) ppre rpre crashdone_p crashdone_r m' vm' hm' v,
  exec_recover mr vmr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash hmr m
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre vmr hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre Mem.empty_mem hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RFinished TR m' vm' hm' v
  -> crashdone_p vm' hm' v m'.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - apply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
  - destruct H8. destruct H8. destruct H8. destruct H8.
    inversion H8. congruence.
  - repeat (destruct H8; try congruence).
Qed.

Lemma corr3_from_corr2_recovered:
  forall (TF TR: Type) m mr vmr hmr (p: prog TF) (r: prog TR) out
         (crash: hashmap -> pred) ppre rpre crashdone_p crashdone_r m' vm' hm' v,
  exec_recover mr vmr hmr p r out
  -> TF = TR
  -> possible_crash m mr
  -> crash hmr m
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> ppre vmr hm' crashdone_p crash)
  -> (forall hm', crash_xform (crash hm'
      * [[ exists l, hashmap_subset l hmr hm' ]])
      =p=> rpre Mem.empty_mem hm' crashdone_r crash)
  -> {{ ppre }} p
  -> {{ rpre }} r
  -> out = RRecovered TF m' vm' hm' v
  -> crashdone_r vm' hm' v m'.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - eapply corr3_from_corr2_finished; eauto.
    clear IHexec_recover H2.
    edestruct H5; eauto.
    + apply H3. eapply crash_xform_apply; eauto.
      pred_apply; cancel.
    + repeat (destruct H2; try congruence).
    + destruct H2. destruct H2. destruct H2.
      inversion H2. eauto.
    + solve_hashmap_subset'.
    + solve_hashmap_subset'.
    + congruence.
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
  -> {{ fun vm hm done crashdone => exists crash,
        ppre vm hm done crash
        * [[ forall hm',
          crash_xform (crash hm'
          * [[ exists l, hashmap_subset l hm hm' ]])
          =p=> rpre Mem.empty_mem hm' crashdone crash ]] }} p >> r.
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
  forall TF TR RF RR (p: prog TF) (r:  prog TR)
         (rxp : TF -> prog RF) (rxr : TR -> prog RR)
         ppre rpre,
  {{ ppre }} Bind p rxp
  -> {{ rpre }} Bind r rxr
  -> {{ fun vm hm done crashdone => exists crash,
        ppre vm hm done crash
        * [[ forall hm',
          crash_xform (crash hm'
          * [[ exists l, hashmap_subset l hm hm' ]])
          =p=> rpre Mem.empty_mem hm' crashdone crash ]] }} Bind p rxp >> Bind r rxr.
Proof.
  intros.
  apply corr3_from_corr2; eauto.
Qed.
