Require Import Mem Hoare.
Require Import Prog ProgMonad.
Require Import Pred PredCrash.
Require Import SepAuto.
Require Import AsyncDisk.
Require Import Hashmap.

Lemma finished_val_eq : forall T d dm bm (v:T),
    exists v', Finished d bm dm v = Finished d bm dm v'.
Proof. eauto. Qed.

Hint Resolve finished_val_eq.


Lemma exec_crashed_blockmem_subset' : forall T (p: prog T) d dm d' dm' bm bm' out tr pr,
  exec pr d bm dm p out tr
  -> (out = Crashed d' bm' dm' \/ exists v, out = Finished d' bm' dm' v)
  -> bm c= bm'.
Proof.
  intros.
  generalize dependent bm'.
  generalize dependent dm'.
  generalize dependent d'.
  
  
    induction H; subst; try solve [ intuition; repeat deex; try congruence;
    try match goal with
        | [ H: @eq (result) _ _ |- _ ] =>
          inversion H; subst
        end;
    eauto; solve_hashmap_subset].

    intros.
    split_ors.    
    eauto 10.
    eauto 7.
Qed.

Lemma exec_crashed_blockmem_subset : forall T (p: prog T) d dm d' dm' bm bm' out tr pr,
  exec pr d bm dm p out tr
  -> out = Crashed d' bm' dm'
  -> bm c= bm'.
Proof.
  intros.
  eapply exec_crashed_blockmem_subset'; eauto.
Qed.

Lemma corr3_from_corr2_failed:
  forall (TF TR: Type) pr tr m mr bmr hmr (p: prog TF) (r: prog TR) out
         (crash: taggedmem -> domainmem -> pred) ppre rpre crashdone_p crashdone_r,
  exec_recover pr mr empty_mem hmr p r out tr
  -> TF = TR
  -> possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> ppre crashdone_p crash empty_mem hm')
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> rpre crashdone_r crash empty_mem hm')
  -> {{ pr | ppre }} p
  -> {{ pr | rpre }} r
  -> out <> RFailed TF TR.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    eapply H3. eapply crash_xform_apply; eauto.
    repeat (destruct H7; try congruence).
Qed.

Lemma corr3_from_corr2_finished:
  forall (TF TR: Type) pr tr m mr bmr hmr (p: prog TF) (r: prog TR) out
    (crash: taggedmem -> domainmem -> pred) ppre rpre crashdone_p crashdone_r m' bm' hm' v,
  exec_recover pr mr empty_mem hmr p r out tr
  -> TF = TR
  -> possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> ppre crashdone_p crash empty_mem hm')
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> rpre crashdone_r crash empty_mem hm')
  -> {{ pr | ppre }} p
  -> {{ pr | rpre }} r
  -> out = RFinished TR m' bm' hm' v
  -> crashdone_p m' bm' hm' v /\ only_public_operations tr.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - eapply H3. eapply crash_xform_apply; eauto.
  - cleanup; split_ors; cleanup; try congruence; split; eauto; try congruence.
Qed.


Lemma corr3_from_corr2_recovered:
  forall (TF TR: Type) mr (p: prog TF) (r: prog TR) out bm hm
         (crash: taggedmem -> domainmem -> pred) ppre rpre crashdone_p crashdone_r m' bm' hm' v pr tr,
  exec_recover pr mr bm hm p r out tr
  -> out = RRecovered TF m' bm' hm' v  
  -> TF = TR
  -> forall m bmr hmr,
    possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm' hm'', crash_xform (crash bm' hm')
      =p=> ppre crashdone_p crash bm hm'')
  -> (forall bm' hm' hm'', crash_xform (crash bm' hm')
      =p=> rpre crashdone_r crash empty_mem hm'')
  -> {{ pr | ppre }} p
  -> {{ pr | rpre }} r
  -> crashdone_r m' bm' hm' v /\ only_public_operations tr.
Proof.
  induction 1; intros; try congruence.
  - inversion H2; subst; clear H2.
    edestruct H8; eauto.
    eapply H6; eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    inversion H1; subst.
    edestruct H9; eauto.
    
    eapply H7; eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    split; eauto.
    apply only_public_operations_app_merge; eauto.
    
  - inversion H2; subst; clear H2.
    edestruct H8; eauto.
    eapply H6; eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    edestruct IHexec_recover; eauto.
    split; eauto.
    apply only_public_operations_app_merge; eauto.
Qed.


Theorem corr3_from_corr2:
  forall TF TR (p: prog TF) (r: prog TR) pr ppre rpre,
    {{ pr | ppre }} p
  -> {{ pr | rpre }} r                 
  -> {{ pr | fun bm hm done crashdone => exists crash,
        ppre done crash bm hm
        * [[ forall bm' hm' hm'',
          crash_xform (crash bm' hm')
          =p=> rpre crashdone crash empty_mem hm'' ]] }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H1 as [crash H1].
  destruct_lift H1.
  inversion H2; subst.
  - edestruct H; eauto.
    split; eauto.
    cleanup; split_ors; cleanup; try congruence.
    do 3 eexists; left; repeat eexists; eauto.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - edestruct H; eauto; try congruence.
    cleanup; split_ors; cleanup; try congruence.
    clear H H1 H2 ppre.    
    inversion H6; subst.
    edestruct H0; eauto.
    eapply H5.
    eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    split.
    do 3 eexists; right; repeat eexists; eauto.
    apply only_public_operations_app_merge; eauto.
    
  - edestruct H; eauto; try congruence.
    cleanup; split_ors; cleanup; try congruence.
    clear H H1 H2 ppre.
    edestruct corr3_from_corr2_recovered.
    apply H6.
    all: eauto.

    split; eauto.
    do 3 eexists; right; repeat eexists; eauto.
    apply only_public_operations_app_merge; eauto.
Qed.


Theorem corr3_from_corr2_rx :
  forall TF TR RF RR pr (p: prog TF) (r:  prog TR)
         (rxp : TF -> prog RF) (rxr : TR -> prog RR)
         ppre rpre,
  {{ pr | ppre }} Bind p rxp
  -> {{ pr | rpre }} Bind r rxr
  -> {{ pr | fun bm hm done crashdone => exists crash,
        ppre done crash bm hm        
        * [[ forall bm' hm',
          crash_xform (crash bm' hm')
          =p=> rpre crashdone crash empty_mem hm']] }} Bind p rxp >> Bind r rxr.
Proof.
  intros.
  apply corr3_from_corr2; eauto.
Qed.






Lemma corr3_weak_from_corr2_weak_failed:
  forall (TF TR: Type) pr tr m mr bmr hmr (p: prog TF) (r: prog TR) out
         (crash: taggedmem -> domainmem -> pred) ppre rpre crashdone_p crashdone_r,
  exec_recover pr mr empty_mem hmr p r out tr
  -> TF = TR
  -> possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> ppre crashdone_p crash empty_mem hm')
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> rpre crashdone_r crash empty_mem hm')
  -> {{W pr | ppre W}} p
  -> {{W pr | rpre W}} r
  -> out <> RFailed TF TR.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    eapply H3. eapply crash_xform_apply; eauto.
    repeat (destruct H7; try congruence).
Qed.

Lemma corr3_weak_from_corr2_weak_finished:
  forall (TF TR: Type) pr tr m mr bmr hmr (p: prog TF) (r: prog TR) out
    (crash: taggedmem -> domainmem -> pred) ppre rpre crashdone_p crashdone_r m' bm' hm' v,
  exec_recover pr mr empty_mem hmr p r out tr
  -> TF = TR
  -> possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> ppre crashdone_p crash empty_mem hm')
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> rpre crashdone_r crash empty_mem hm')
  -> {{W pr | ppre W}} p
  -> {{W pr | rpre W}} r
  -> out = RFinished TR m' bm' hm' v
  -> crashdone_p m' bm' hm' v /\ trace_secure pr tr.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - eapply H3. eapply crash_xform_apply; eauto.
  - cleanup; split_ors; cleanup; try congruence; split; eauto; congruence.
Qed.


Lemma corr3_weak_from_corr2_weak_recovered:
  forall (TF TR: Type) mr (p: prog TF) (r: prog TR) out bm hm
         (crash: taggedmem -> domainmem -> pred) ppre rpre crashdone_p crashdone_r m' bm' hm' v pr tr,
  exec_recover pr mr bm hm p r out tr
  -> out = RRecovered TF m' bm' hm' v  
  -> TF = TR
  -> forall m bmr,
    possible_crash m mr
  -> crash bmr hm m
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> ppre crashdone_p crash bm hm')
  -> (forall bm' hm', crash_xform (crash bm' hm')
      =p=> rpre crashdone_r crash empty_mem hm')
  -> {{W pr | ppre W}} p
  -> {{W pr | rpre W}} r
  -> crashdone_r m' bm' hm' v /\ trace_secure pr tr.
Proof.
  induction 1; intros; try congruence.
  - inversion H2; subst; clear H2.
    edestruct H8; eauto.
    eapply H6; eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    inversion H1; subst.
    edestruct H9; eauto.
    
    eapply H7; eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    split; eauto.
    apply trace_secure_app; eauto.
    
  - inversion H2; subst; clear H2.
    edestruct H8; eauto.
    eapply H6; eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    edestruct IHexec_recover; eauto.
    split; eauto.
    apply trace_secure_app; eauto.
Qed.

Theorem corr3_weak_from_corr2_weak:
  forall TF TR (p: prog TF) (r: prog TR) pr ppre rpre,
    {{W pr | ppre W}} p
  -> {{W pr | rpre W}} r                 
  -> {{W pr | fun bm hm done crashdone => exists crash,
        ppre done crash bm hm
        * [[ forall bm' hm',
          crash_xform (crash bm' hm')
          =p=> rpre crashdone crash empty_mem hm' ]] W}} p >> r.
Proof.
  unfold corr3_weak; intros.
  destruct H1 as [crash H1].
  destruct_lift H1.
  inversion H2; subst.
  - edestruct H; eauto.
    split; eauto.
    cleanup; split_ors; cleanup; try congruence.
    do 3 eexists; left; repeat eexists; eauto.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
  - edestruct H; eauto; try congruence.
    cleanup; split_ors; cleanup; try congruence.
    clear H H1 H2 ppre.    
    inversion H6; subst.
    edestruct H0; eauto.
    eapply H5.
    eapply crash_xform_apply; eauto.
    cleanup; split_ors; cleanup; try congruence.
    split.
    do 3 eexists; right; repeat eexists; eauto.
    apply trace_secure_app; eauto.
    
  - edestruct H; eauto; try congruence.
    cleanup; split_ors; cleanup; try congruence.
    clear H H1 H2 ppre.
    edestruct corr3_weak_from_corr2_weak_recovered.
    apply H6.
    all: eauto.

    split; eauto.
    do 3 eexists; right; repeat eexists; eauto.
    apply trace_secure_app; eauto.
Qed.


Theorem corr3_weak_from_corr2_weak_rx :
  forall TF TR RF RR pr (p: prog TF) (r:  prog TR)
         (rxp : TF -> prog RF) (rxr : TR -> prog RR)
         ppre rpre,
  {{W pr | ppre W}} Bind p rxp
  -> {{W pr | rpre W}} Bind r rxr
  -> {{W pr | fun bm hm done crashdone => exists crash,
        ppre done crash bm hm        
        * [[ forall bm' hm',
          crash_xform (crash bm' hm')
          =p=> rpre crashdone crash empty_mem hm']] W}} Bind p rxp >> Bind r rxr.
Proof.
  intros.
  apply corr3_weak_from_corr2_weak; eauto.
Qed.

Ltac recover_ro_ok :=
  intros;
  repeat match goal with
         | [ |- forall_helper _ ] => unfold forall_helper; intros; eexists; intros
         | [ |- corr3 _ ?pre' _ _ ] => eapply corr3_from_corr2_rx; eauto with prog
         | [ |- corr3 _ _ _ _ ] => eapply pimpl_ok3; intros
         | [ |- corr2 _ _ _ ] => step
         | [ |- corr3_weak _ ?pre' _ _ ] => eapply corr3_weak_from_corr2_weak_rx; eauto with prog
         | [ |- corr3_weak _ _ _ _ ] => eapply pimpl_ok3_weak; intros
         | [ |- corr2_weak _ _ _ ] => weakstep
         | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
         | [ H: diskIs _ _ |- _ ] => unfold diskIs in *
         | [ |- pimpl (crash_xform _) _ ] => progress autorewrite with crash_xform
         end.
