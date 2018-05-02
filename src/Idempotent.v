Require Import Hoare.
Require Import Prog ProgMonad.
Require Import Pred PredCrash.
Require Import SepAuto.
Require Import AsyncDisk.
Require Import Hashmap.


Lemma hashmap_subset_some_list_trans : forall hm hm' hm'',
    (exists l, hashmap_subset l hm hm') ->
    (exists l, hashmap_subset l hm' hm'') ->
    exists l, hashmap_subset l hm hm''.
Proof.
  intros; solve_hashmap_subset.
Qed.

Lemma finished_val_eq : forall T m vm hm (v:T),
    exists v', Finished m vm hm v = Finished m vm hm v'.
Proof. eauto. Qed.

Hint Resolve finished_val_eq.

Lemma exec_crashed_hashmap_subset' : forall T (p: prog T) m m' bm bm' hm hm' out tr pr,
  exec pr m bm hm p out tr
  -> (out = Crashed m' bm' hm' \/ exists v, out = Finished m' bm' hm' v)
  -> exists l, hashmap_subset l hm hm'.
Proof.
  intros.
  generalize dependent bm'.
  generalize dependent hm'.
  generalize dependent m'.
  
  
    induction H; subst; try solve [ intuition; repeat deex; try congruence;
    try match goal with
        | [ H: @eq (result) _ _ |- _ ] =>
          inversion H; subst
        end;
    eauto; solve_hashmap_subset].

    intros.
    split_ors.    
    eauto 10 using hashmap_subset_some_list_trans.
    eauto 7 using hashmap_subset_some_list_trans.
Qed.

Lemma exec_crashed_blockmem_subset' : forall T (p: prog T) m m' bm bm' hm hm' out tr pr,
  exec pr m bm hm p out tr
  -> (out = Crashed m' bm' hm' \/ exists v, out = Finished m' bm' hm' v)
  -> bm c= bm'.
Proof.
  intros.
  generalize dependent bm'.
  generalize dependent hm'.
  generalize dependent m'.
  
  
    induction H; subst; try solve [ intuition; repeat deex; try congruence;
    try match goal with
        | [ H: @eq (result) _ _ |- _ ] =>
          inversion H; subst
        end;
    eauto; solve_hashmap_subset].

    intros.
    split_ors.    
    eauto 10 using hashmap_subset_some_list_trans.
    eauto 7 using hashmap_subset_some_list_trans.
Qed.

Lemma exec_crashed_hashmap_subset : forall T (p: prog T) pr tr m m' bm hm bm' hm' out,
  exec pr m bm hm p out tr
  -> out = Crashed  m' bm' hm'
  -> exists l, hashmap_subset l hm hm'.
Proof.
  intros.
  eapply exec_crashed_hashmap_subset'; eauto.
Qed.

Lemma exec_crashed_blockmem_subset : forall T (p: prog T) pr tr m m' bm hm bm' hm' out,
  exec pr m bm hm p out tr
  -> out = Crashed  m' bm' hm'
  -> bm c= bm'.
Proof.
  intros.
  eapply exec_crashed_blockmem_subset'; eauto.
Qed.

(*
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
 *)

Lemma corr3_from_corr2_failed:
  forall (TF TR: Type) pr tr m mr bmr hmr (p: prog TF) (r: prog TR) out
         (crash: block_mem -> hashmap -> pred) ppre rpre crashdone_p crashdone_r,
  exec_recover pr mr bmr hmr p r out tr
  -> TF = TR
  -> possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm'
     * [[ exists l, hashmap_subset l hmr hm' ]] *
     [[ bmr c= bm' ]])
      =p=> ppre crashdone_p crash bm' hm')
  -> (forall bm' hm', crash_xform (crash bm' hm'
      * [[ exists l, hashmap_subset l hmr hm' ]] *
     [[ bmr c= bm' ]])
      =p=> rpre crashdone_r crash bm' hm')
  -> {{ pr | ppre }} p
  -> {{ pr | rpre }} r
  -> forall mx bmx hmx, out <> RFailed TF TR mx bmx hmx.
Proof.
  intros.
  generalize dependent m.
  induction H; intros; try congruence.
  - edestruct H5; eauto.
    eapply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    solve_hashmap_subset.
    repeat (destruct H7; try congruence).
Qed.

Lemma corr3_from_corr2_finished:
  forall (TF TR: Type) pr tr m mr bmr hmr (p: prog TF) (r: prog TR) out
    (crash: block_mem -> hashmap -> pred) ppre rpre crashdone_p crashdone_r m' bm' hm' v,
  exec_recover pr mr bmr hmr p r out tr
  -> TF = TR
  -> possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm'
     * [[ exists l, hashmap_subset l hmr hm' ]] *
     [[ bmr c= bm' ]])
      =p=> ppre crashdone_p crash bm' hm')
  -> (forall bm' hm', crash_xform (crash bm' hm'
      * [[ exists l, hashmap_subset l hmr hm' ]] *
     [[ bmr c= bm' ]])
      =p=> rpre crashdone_r crash bm' hm')
  -> {{ pr | ppre }} p
  -> {{ pr | rpre }} r
  -> out = RFinished TR m' bm' hm' v
  -> crashdone_p m' bm' hm' v /\ only_public_operations tr.
Proof.
  intros.
  induction H; try congruence.
  edestruct H5; eauto.
  - eapply H3. eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    solve_hashmap_subset.
  - split_ors; cleanup; try congruence; split; eauto; congruence.
Qed.

Lemma corr3_from_corr2_recovered:
  forall (TF TR: Type) mr bmr hmr (p: prog TF) (r: prog TR) out
         (crash: block_mem -> hashmap -> pred) ppre rpre crashdone_p crashdone_r m' bm' hm' v pr tr,
  exec_recover pr mr bmr hmr p r out tr
  -> out = RRecovered TF m' bm' hm' v  
  -> TF = TR
  -> forall m,
    possible_crash m mr
  -> crash bmr hmr m
  -> (forall bm' hm', crash_xform (crash bm' hm'
     * [[ exists l, hashmap_subset l hmr hm' ]] *
     [[ bmr c= bm' ]])
      =p=> ppre crashdone_p crash bm' hm')
  -> (forall bm' hm', crash_xform (crash bm' hm'
     * [[ exists l, hashmap_subset l hmr hm' ]]
     * [[ bmr c= bm' ]])
      =p=> rpre crashdone_r crash bm' hm')
  -> {{ pr | ppre }} p
  -> {{ pr | rpre }} r
  -> crashdone_r m' bm' hm' v /\ only_public_operations tr.
Proof.
  induction 1; intros; try congruence.
  - inversion H2; subst; clear H2.
    edestruct H8; eauto.
    eapply H6; eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    solve_hashmap_subset.
    split_ors; cleanup; try congruence.
    inversion H1; subst.
    edestruct H9; eauto.
    
    eapply H7; eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    eapply exec_crashed_hashmap_subset; eauto.
    eapply exec_crashed_blockmem_subset; eauto.
    split_ors; cleanup; try congruence.
    split; eauto.
    apply only_public_operations_app_merge; eauto.
    
  - inversion H2; subst; clear H2.
    edestruct H8; eauto.
    eapply H6; eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    solve_hashmap_subset.
    split_ors; cleanup; try congruence.
    edestruct IHexec_recover; eauto.

    intros.
    repeat rewrite crash_xform_sep_star_dist.
    xcrash.
    rewrite <- H7; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    eapply hashmap_subset_some_list_trans; eauto.
    eapply exec_crashed_hashmap_subset; eauto.
    intros _ _.
    eapply block_mem_subset_trans.
    eapply exec_crashed_blockmem_subset; eauto.
    eauto.

    intros.
    repeat rewrite crash_xform_sep_star_dist.
    xcrash.
    rewrite <- H7; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    eapply hashmap_subset_some_list_trans; eauto.
    eapply exec_crashed_hashmap_subset; eauto.
    intros _ _.
    eapply block_mem_subset_trans.
    eapply exec_crashed_blockmem_subset; eauto.
    eauto.
    
    split; eauto.
    apply only_public_operations_app_merge; eauto.
    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
Qed.

Theorem corr3_from_corr2:
  forall TF TR (p: prog TF) (r: prog TR) pr ppre rpre,
    {{ pr | ppre }} p
  -> {{ pr | rpre }} r                 
  -> {{ pr | fun bm hm done crashdone => exists crash,
        ppre done crash bm hm
        * [[ forall bm' hm',
          crash_xform (crash bm' hm'
          * [[ exists l, hashmap_subset l hm hm' ]]
          * [[ bm c= bm' ]])
          =p=> rpre crashdone crash bm' hm' ]] }} p >> r.
Proof.
  unfold corr3; intros.
  destruct H1 as [crash H1].
  destruct_lift H1.
  inversion H2; subst.
  - edestruct H; eauto.
    split; eauto.
    split_ors; cleanup; try congruence.
    left; repeat eexists; eauto.
  - exfalso.
    edestruct H; eauto; repeat deex; try congruence.
    split_ors; cleanup; try congruence.
  - edestruct H; eauto; repeat deex; try congruence.
    split_ors; cleanup; try congruence.
    clear H H1 H2 ppre.    
    inversion H6; subst.
    edestruct H0; eauto.
    eapply H5.
    eapply crash_xform_apply; eauto.
    pred_apply; cancel.
    eauto.
    eapply exec_crashed_hashmap_subset; eauto.
    eapply exec_crashed_blockmem_subset; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; repeat eexists; eauto.
    apply only_public_operations_app_merge; eauto.
    
  - edestruct H; eauto; repeat deex; try congruence.
    split_ors; cleanup; try congruence.
    clear H H1 H2 ppre.
    edestruct corr3_from_corr2_recovered.
    apply H6.
    all: eauto.

    intros.
    repeat rewrite crash_xform_sep_star_dist.
    xcrash.
    rewrite <- H5; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    eapply hashmap_subset_some_list_trans; eauto.
    eapply exec_crashed_hashmap_subset; eauto.
    intros _ _.
    eapply block_mem_subset_trans.
    eapply exec_crashed_blockmem_subset; eauto.
    eauto.

    intros.
    repeat rewrite crash_xform_sep_star_dist.
    xcrash.
    rewrite <- H5; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    rewrite crash_xform_sep_star_dist.
    cancel.
    repeat rewrite crash_xform_lift_empty; cancel.
    eapply hashmap_subset_some_list_trans; eauto.
    eapply exec_crashed_hashmap_subset; eauto.
    intros _ _.
    eapply block_mem_subset_trans.
    eapply exec_crashed_blockmem_subset; eauto.
    eauto.
    
    split; eauto.
    right; repeat eexists; eauto.
    apply only_public_operations_app_merge; eauto.

    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
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
          crash_xform (crash bm' hm'
          * [[ exists l, hashmap_subset l hm hm' ]]
          * [[ bm c= bm' ]])
          =p=> rpre crashdone crash bm' hm']] }} Bind p rxp >> Bind r rxr.
Proof.
  intros.
  apply corr3_from_corr2; eauto.
Qed.

  Ltac recover_ro_ok := intros;
    repeat match goal with
      | [ |- forall_helper _ ] => unfold forall_helper; intros; eexists; intros
      | [ |- corr3 _ ?pre' _ _ ] => eapply corr3_from_corr2_rx; eauto with prog
      | [ |- corr3 _ _ _ _ ] => eapply pimpl_ok3; intros
      | [ |- corr2 _ _ _ ] => step
      | [ H: crash_xform ?x =p=> ?x |- context [ crash_xform ?x ] ] => rewrite H
      | [ H: diskIs _ _ |- _ ] => unfold diskIs in *
      | [ |- pimpl (crash_xform _) _ ] => progress autorewrite with crash_xform
    end.