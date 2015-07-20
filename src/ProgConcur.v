Require Import Mem.
Require Import Prog.
Require Import Word.
Require Import Hoare.
Require Import Pred.
Require Import RG.
Require Import Arith.
Require Import SepAuto.
Require Import List.

Import ListNotations.

Set Implicit Arguments.


Section STAR.

  Variable state : Type.
  Variable prog : Type.
  Variable step : state -> prog -> state -> prog -> Prop.

  Inductive star : state -> prog -> state -> prog -> Prop :=
  | star_refl : forall s p,
    star s p s p
  | star_step : forall s1 s2 s3 p1 p2 p3,
    step s1 p1 s2 p2 ->
    star s2 p2 s3 p3 ->
    star s1 p1 s3 p3.

  Lemma star_trans : forall s0 p0 s1 p1 s2 p2,
    star s0 p0 s1 p1 ->
    star s1 p1 s2 p2 ->
    star s0 p0 s2 p2.
  Proof.
    induction 1; eauto.
    intros.
    eapply star_step; eauto.
  Qed.

End STAR.

Lemma star_impl :
  forall state prog s0 p0 s1 p1 (step1 step2 : state -> prog -> state -> prog -> Prop),
  (forall s p s' p', step1 s p s' p' -> step2 s p s' p') ->
  star step1 s0 p0 s1 p1 ->
  star step2 s0 p0 s1 p1.
Proof.
  intros.
  induction H0.
  - constructor.
  - econstructor; eauto.
Qed.


Section ExecConcurOne.

  Inductive env_outcome (T: Type) :=
  | EFailed
  | EFinished (m: @mem addr (@weq addrlen) valuset) (v: T).

  Inductive env_step_label :=
  | StepThis (m m' : @mem addr (@weq addrlen) valuset)
  | StepOther (m m' : @mem addr (@weq addrlen) valuset).

  Inductive env_exec (T: Type) : mem -> prog T -> list env_step_label -> env_outcome T -> Prop :=
  | EXStepThis : forall m m' p p' out events,
    step m p m' p' ->
    env_exec m' p' events out ->
    env_exec m p ((StepThis m m') :: events) out
  | EXFail : forall m p, (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    env_exec m p nil (EFailed T)
  | EXStepOther : forall m m' p out events,
    env_exec m' p events out ->
    env_exec m p ((StepOther m m') :: events) out
  | EXDone : forall m v,
    env_exec m (Done v) nil (EFinished m v).

  Definition env_corr2 (pre : forall (done : donecond nat),
                              forall (rely : @action addr (@weq addrlen) valuset),
                              forall (guarantee : @action addr (@weq addrlen) valuset),
                              @pred addr (@weq addrlen) valuset)
                       (p : prog nat) : Prop :=
    forall done rely guarantee m,
    pre done rely guarantee m ->
    forall events out,
    env_exec m p events out ->
    (forall m0 m1, In (StepOther m0 m1) events -> rely m0 m1) ->
    (forall m0 m1, In (StepThis m0 m1) events -> guarantee m0 m1) /\
    (exists md vd, out = EFinished md vd /\ done vd md).

End ExecConcurOne.

Hint Constructors env_exec.


Notation "{C pre C} p" := (env_corr2 pre%pred p) (at level 0, p at level 60, format
  "'[' '{C' '//' '['   pre ']' '//' 'C}'  p ']'").


Lemma env_exec_progress :
  forall T (p : prog T) m, exists events out,
  env_exec m p events out.
Proof.
  intros T p.
  induction p; simpl; intros.
  - do 2 eexists. apply EXDone.
  - case_eq (m a); try destruct p; intros.
    + edestruct H. edestruct H1.
      do 2 eexists.
      eapply EXStepThis. eauto. eauto.
    + do 2 eexists.
      eapply EXFail; intuition; repeat deex.
      inversion H1; congruence.
      congruence.
  - case_eq (m a); try destruct p; intros.
    + edestruct H. edestruct H1.
      do 2 eexists.
      eapply EXStepThis. eauto. eauto.
    + do 2 eexists.
      eapply EXFail; intuition; repeat deex.
      inversion H1; congruence.
      congruence.
  - case_eq (m a); try destruct p; intros.
    + edestruct H. edestruct H1.
      do 2 eexists.
      eapply EXStepThis. eauto. eauto.
    + do 2 eexists.
      eapply EXFail; intuition; repeat deex.
      inversion H1; congruence.
      congruence.
  - case_eq (m a); try destruct p; intros.
    + edestruct H. edestruct H1.
      do 2 eexists.
      eapply EXStepThis. eauto. eauto.
    + do 2 eexists.
      eapply EXFail; intuition; repeat deex.
      inversion H1; congruence.
      congruence.
  Grab Existential Variables.
  eauto.
Qed.

Lemma env_exec_append_event :
  forall T m (p : prog T) events m' m'' v,
  env_exec m p events (EFinished m' v) ->
  env_exec m p (events ++ [StepOther m' m'']) (EFinished m'' v).
Proof.
  intros.
  remember (EFinished m' v) as out.
  induction H; simpl; eauto.
  congruence.
  inversion Heqout; eauto.
Qed.

Example rely_just_before_done :
  forall pre p,
  {C pre C} p ->
  forall done rely guarantee m,
  pre done rely guarantee m ->
  forall events out,
  env_exec m p events out ->
  (forall m0 m1, In (StepOther m0 m1) events -> rely m0 m1) ->
  exists vd md, out = EFinished md vd /\ done vd md /\
  (forall md', rely md md' -> done vd md').
Proof.
  unfold env_corr2.
  intros.
  specialize (H _ _ _ _ H0).
  assert (H' := H).
  specialize (H' _ _ H1 H2).
  intuition.
  repeat deex.
  do 2 eexists; intuition.
  specialize (H (events ++ [StepOther md md']) (EFinished md' vd)).
  destruct H.
  - eapply env_exec_append_event; eauto.
  - intros.
    apply in_app_or in H; intuition.
    inversion H5; try congruence.
    inversion H.
  - repeat deex.
    congruence.
Qed.


Section ExecConcurMany.

  Inductive threadstate :=
  | TNone
  | TRunning (p : prog nat).

  Definition threadstates := forall (tid : nat), threadstate.
  Definition results := forall (tid : nat), nat.

  Definition upd_prog (ap : threadstates) (tid : nat) (p : threadstate) :=
    fun tid' => if eq_nat_dec tid' tid then p else ap tid'.

  Lemma upd_prog_eq : forall ap tid p, upd_prog ap tid p tid = p.
  Proof.
    unfold upd_prog; intros; destruct (eq_nat_dec tid tid); congruence.
  Qed.

  Lemma upd_prog_eq' : forall ap tid p tid', tid = tid' -> upd_prog ap tid p tid' = p.
  Proof.
    intros; subst; apply upd_prog_eq.
  Qed.

  Lemma upd_prog_ne : forall ap tid p tid', tid <> tid' -> upd_prog ap tid p tid' = ap tid'.
  Proof.
    unfold upd_prog; intros; destruct (eq_nat_dec tid' tid); congruence.
  Qed.

  Inductive coutcome :=
  | CFailed
  | CFinished (m : @mem addr (@weq addrlen) valuset) (rs : results).

  Inductive cexec : mem -> threadstates -> coutcome -> Prop :=
  | CStep : forall tid ts m m' (p : prog nat) p' out,
    ts tid = TRunning p ->
    step m p m' p' ->
    cexec m' (upd_prog ts tid (TRunning p')) out ->
    cexec m ts out
  | CFail : forall tid ts m (p : prog nat),
    ts tid = TRunning p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    cexec m ts CFailed
  | CDone : forall ts m (rs : results),
    (forall tid r, ts tid = TRunning (Done r) -> rs tid = r) ->
    cexec m ts (CFinished m rs).

  Definition corr_threads (pres : forall (tid : nat),
                                  forall (done : donecond nat),
                                  forall (rely : @action addr (@weq addrlen) valuset),
                                  forall (guarantee : @action addr (@weq addrlen) valuset),
                                  @pred addr (@weq addrlen) valuset)
                          (ts : threadstates) :=
    forall dones relys guarantees m out,
    (forall tid, (pres tid) (dones tid) (relys tid) (guarantees tid) m) ->
    cexec m ts out ->
    exists m' rs, out = CFinished m' rs /\
    (forall tid, (exists p, ts tid = TRunning p) -> (dones tid) (rs tid) m').

End ExecConcurMany.

Definition pres_step (pres : forall (tid : nat),
                                  forall (done : donecond nat),
                                  forall (rely : @action addr (@weq addrlen) valuset),
                                  forall (guarantee : @action addr (@weq addrlen) valuset),
                                  @pred addr (@weq addrlen) valuset)
                      m m' :=
  fun tid d r g (mthis : @mem addr (@weq addrlen) valuset) =>
  (pres tid) d r g m /\ mthis = m'.

Hint Resolve in_eq.
Hint Resolve in_cons.

Lemma ccorr2_step : forall pres tid m m' p p',
  {C pres tid C} p ->
  step m p m' p' ->
  {C (pres_step pres m m') tid C} p'.
Proof.
  unfold pres_step, env_corr2.
  intros.
  intuition; subst;
    eapply H with (events := StepThis m m' :: events);
    eauto; intros.

  apply H3.
  inversion H5; congruence.

  apply H3.
  inversion H1; congruence.
Qed.

Lemma ccorr2_stable_step : forall pres tid m m'
  (p p' p'' : prog nat),
  {C pres tid C} p ->
  step m p' m' p'' ->
  (forall d r g, pres tid d r g m -> r m m' /\ stable (pres tid d r g) r) ->
  {C (pres_step pres m m') tid C} p.
Proof.
  unfold pres_step, env_corr2, stable.
  intros.
  intuition.
  eapply H.
  2: eauto.
  2: eauto.
  2: eauto.
  subst.
  eapply H1; eauto.
  eapply H1; eauto.
  eapply H; eauto.
  intros; auto.
  subst.
  edestruct H2; eauto.
  inversion H6; subst.
  eapply H1; eauto.
Qed.

Ltac compose_helper :=
  match goal with
  | [ H: context[_ =a=> _] |- _ ] =>
    eapply H; [| | | eauto | eauto ]; eauto
  end.

Ltac upd_prog_case' tid tid' :=
  destruct (eq_nat_dec tid tid');
    try rewrite upd_prog_eq' in * by auto;
    try rewrite upd_prog_ne in * by auto.

Ltac upd_prog_case :=
  match goal with
  | [ H: upd_prog _ ?tid _ ?tid' = _ |- _] => upd_prog_case' tid tid'
  end.

Theorem ccorr2_no_fail : forall pre m p d r g,
  {C pre C} p ->
  pre d r g m ->
  env_exec m p nil (@EFailed nat) ->
  False.
Proof.
  unfold env_corr2.
  intros.
  edestruct H; eauto.
  intros; contradiction.
  repeat deex.
  congruence.
Qed.

Theorem compose :
  forall ts pres,
  (forall tid p, ts tid = TRunning p ->
   {C pres tid C} p /\
   forall tid' p' m d r g d' r' g', ts tid' = TRunning p' -> tid <> tid' ->
   (pres tid) d r g m ->
   (pres tid') d' r' g' m ->
   g =a=> r') ->
  corr_threads pres ts.
Proof.
  unfold corr_threads.
  intros.
  destruct out.

  - exfalso.
    generalize dependent pres.
    generalize dependent dones.
    generalize dependent relys.
    generalize dependent guarantees.
    remember (CFailed) as cfail.
    induction H1; simpl; intros.

    + (* thread [tid] did a legal step *)
      eapply IHcexec; clear IHcexec.
      eauto.
      instantiate (pres := pres_step pres m m').
      * intros.
        intuition.
        -- upd_prog_case.
          ++ edestruct H2; eauto.
             inversion H4; subst.
             eapply ccorr2_step; eauto.
          ++ eapply ccorr2_stable_step.
             edestruct H2; eauto.
             eauto.
             intros; intuition.
             assert ((guarantees tid) m m').
             assert ({C pres tid C} p).
             apply H2; auto.
             unfold env_corr2 in H6.
             eapply H6.
             eauto.
             eapply EXStepThis; eauto.
             3: auto.
             admit.
             admit.
             assert ((guarantees tid) =a=> r) by compose_helper.
             auto.
             (* need to add stability to ccorr2 *)
             admit.
        -- unfold pres_step in *.
           intuition.
           upd_prog_case; upd_prog_case; try congruence;
             subst;
             compose_helper.
      * unfold pres_step; auto.

    + (* thread [tid] failed *)
      edestruct H2; eauto.
      eapply ccorr2_no_fail; eauto.

    + congruence.

  - do 2 eexists; intuition.
  generalize dependent pres.
  generalize dependent dones.
  generalize dependent relys.
  generalize dependent guarantees.
  generalize dependent tid.
  remember (CFinished m0 rs) as cout.
    induction H1; intros; simpl.
       + (* thread [tid] did a legal step *)
      eapply IHcexec; clear IHcexec.
      eauto.
      instantiate (pres := fun tid' d r g mthis => (pres tid') d r g m /\ mthis = m').
      * deex.
        destruct (eq_nat_dec tid tid0); eexists.
        subst tid0; rewrite upd_prog_eq; eauto.
        rewrite upd_prog_ne by auto; eauto.
      * intros.
        intuition.
        -- destruct (eq_nat_dec tid1 tid); subst.
          ++ rewrite upd_prog_eq in H5. inversion H5. subst.
            specialize (H3 _ _ H). intuition.
            unfold env_corr2 in *.
            intros. destruct H3. subst.
            specialize (H6 _ _ _ _ H3).
            specialize (H6 ((StepThis m m') :: events) out).
            edestruct H6.
            ** eauto.
            ** intros.
              inversion H10; try congruence. eauto.
            ** intuition.
          ++ rewrite upd_prog_ne in H5 by auto.
            specialize (H3 _ _ H5).
            intuition.
            unfold env_corr2 in *; intros.
            eapply H6.
            3: eauto.
            2: eauto.
            intuition.
            (* STABILITY! *)
            admit.
        -- destruct (eq_nat_dec tid tid1);
           destruct (eq_nat_dec tid' tid).
          ++ congruence.
          ++ subst; try congruence;
             try rewrite upd_prog_eq in *;
             try rewrite upd_prog_ne in * by auto.
            specialize (H3 _ _ H). intuition.
            eapply H11 with (tid' := tid').
            eauto.
            eauto.
            eauto.
            eauto.
          ++ subst; try congruence;
             try rewrite upd_prog_eq in *;
             try rewrite upd_prog_ne in * by auto.
             specialize (H3 _ _ H5). intuition.
             eapply H11 with (tid' := tid).
             all: eauto.
          ++ subst; try congruence;
             try rewrite upd_prog_eq in *;
             try rewrite upd_prog_ne in * by auto.
            specialize (H3 _ _ H5). intuition.
            eapply H11 with (tid' := tid').
            all: eauto.
      * intros.
        simpl.
        eauto.
    + (* thread [tid] failed *)
      specialize (H3 _ _ H); intuition.
      specialize (H4 tid).

      unfold env_corr2 in H5.
      specialize (H5 _ _ _ _ H4).

      assert (env_exec m p nil (@EFailed nat)).
      apply EXFail; eauto.

      specialize (H5 _ _ H3).
      edestruct H5; intros.
      inversion H7.
      repeat deex.
      congruence.

    + inversion Heqcout; subst.
      deex.
      specialize (H0 _ _ H2).
      intuition.
      unfold env_corr2 in H3.
      specialize (H3 _ _ _ _ (H1 tid)).
      assert (env_exec m0 p nil (EFinished m0 (rs tid))).
Admitted.


Ltac inv_cstep :=
  match goal with
  | [ H: cstep _ _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Ltac inv_ts :=
  match goal with
  | [ H: TRunning _ = TRunning _ |- _ ] => inversion H; clear H; subst
  end.

Lemma star_cstep_tid : forall m ts m' ts' tid,
  star cstep_any m ts m' ts' ->
  (star (cstep_except tid) m ts m' ts') \/
  (exists m0 ts0 m1 ts1,
   star (cstep_except tid) m ts m0 ts0 /\
   cstep tid m0 ts0 m1 ts1 /\
   star cstep_any m1 ts1 m' ts').
Proof.
  induction 1.
  - left. constructor.
  - unfold cstep_any in H. destruct H as [tid' H].
    destruct (eq_nat_dec tid' tid); subst.
    + right. exists s1. exists p1. do 2 eexists.
      split; [ constructor | ].
      split; [ eauto | ].
      eauto.
    + intuition.
      * left. econstructor.
        unfold cstep_except; eauto.
        eauto.
      * repeat deex.
        right.
        do 4 eexists.
        intuition eauto.
        econstructor.
        unfold cstep_except; eauto.
        eauto.
Qed.

Lemma star_cstep_except_ts : forall m ts m' ts' tid,
  star (cstep_except tid) m ts m' ts' ->
  ts tid = ts' tid.
Proof.
  induction 1; eauto.
  rewrite <- IHstar.
  inversion H. destruct H1.
  inversion H2; rewrite upd_prog_ne in * by auto; congruence.
Qed.

Lemma cstep_except_cstep_any : forall m ts m' ts' tid,
  cstep_except tid m ts m' ts' ->
  cstep_any m ts m' ts'.
Proof.
  firstorder.
Qed.

Theorem write_cok : forall a vnew rx,
  {C
    fun done rely guarantee =>
    exists F v0 vrest,
    F * a |-> (v0, vrest) *
    [[ forall F0 F1 v, rely =a=> (F0 * a |-> v ~> F1 * a |-> v) ]] *
    [[ forall F x y, (F * a |-> x ~> F * a |-> y) =a=> guarantee ]] *
    [[ {C
         fun done_rx rely_rx guarantee_rx =>
         exists F', F' * a |-> (vnew, [v0] ++ vrest) *
         [[ done_rx = done ]] *
         [[ rely =a=> rely_rx ]] *
         [[ guarantee_rx =a=> guarantee ]]
       C} rx tt ]]
  C} Write a vnew rx.
Proof.
  unfold ccorr2; intros.
  destruct_lift H0.
  apply star_cstep_tid with (tid := tid) in H2. destruct H2.
  - (* No steps by [tid] up to this point. *)
    assert ((exists F', F' * a |-> (v1, vrest))%pred m) by ( pred_apply; cancel ).
    clear H0.

    assert ((exists F', F' * a |-> (v1, vrest))%pred m').
    {
      clear H6 H.
      induction H2; [ pred_apply; cancel | ].
      unfold cstep_except in *; deex.
      eapply IHstar; eauto; intros.
      eapply H1; [ | | eauto ]; eauto.
      econstructor; eauto. unfold cstep_any in *; intros. eauto.
      eapply H8 in H1; [ | econstructor | eauto | eauto ].
      destruct H1.
      pred_apply; cancel.
    }
    clear H4.
    destruct_lift H0.

    assert (ts tid = ts' tid) by ( eapply star_cstep_except_ts; eauto ).
    rewrite H4 in H; clear H4.

    inv_cstep.
    + (* cstep_step *)
      rewrite H in *. inv_ts.
      inv_step.
      intuition.
      * eapply H7.
        unfold act_bow. intuition.
        ** pred_apply; cancel.
        ** apply sep_star_comm. eapply ptsto_upd. pred_apply; cancel.
      * rewrite upd_prog_eq in *; congruence.
      * rewrite upd_prog_eq in *; congruence.
    + (* cstep_fail *)
      rewrite H in *. inv_ts.
      exfalso. apply H5. do 2 eexists.
      constructor.
      apply sep_star_comm in H0. apply ptsto_valid in H0. eauto.
    + (* cstep_done *)
      congruence.

  - (* [tid] made a step. *)
    destruct H2. destruct H2. destruct H2. destruct H2. destruct H2. destruct H4.
    assert (ts tid = x0 tid) by ( eapply star_cstep_except_ts; eauto ).
    rewrite H9 in H; clear H9.

    assert ((exists F', F' * a |-> (v1, vrest))%pred m) by ( pred_apply; cancel ).
    clear H0.

    assert ((exists F', F' * a |-> (v1, vrest))%pred x).
    {
      clear H6 H.
      induction H2; [ pred_apply; cancel | ].
      unfold cstep_except in *; deex.
      eapply IHstar; eauto; intros.
      eapply H1; [ | | eauto ]; eauto.
      econstructor; eauto. unfold cstep_any in *; intros. eauto.
      eapply H8 in H1; [ | econstructor | eauto | eauto ].
      destruct H1.
      pred_apply; cancel.
    }
    clear H9.
    destruct_lift H0.

    inversion H4.
    + (* cstep_step *)
      rewrite H in *. inv_ts.
      inv_step.
      apply ptsto_valid' in H0 as H0'. rewrite H0' in H16. inversion H16; subst; clear H16.
      eapply H6 with (ts := upd_prog x0 tid (TRunning (rx tt))); eauto.
      { rewrite upd_prog_eq; eauto. }
      {
        eapply pimpl_trans; [ cancel | | ].
        2: eapply ptsto_upd; pred_apply; cancel.
        cancel.
      }
      {
        intros.
        eapply H8.
        eapply H1; eauto.

        eapply star_trans.
        eapply star_impl. intros; eapply cstep_except_cstep_any; eauto.
        eauto.
        econstructor.
        unfold cstep_any; eauto.
        eauto.
      }
    + (* cstep_fail *)
      rewrite H in *. inv_ts.
      exfalso. apply H10. do 2 eexists.
      constructor.
      apply sep_star_comm in H0. apply ptsto_valid in H0. eauto.
    + (* cstep_done *)
      congruence.

  Grab Existential Variables.
  all: eauto.
Qed.

Theorem pimpl_cok : forall pre pre' (p : prog nat),
  {C pre' C} p ->
  (forall done rely guarantee, pre done rely guarantee =p=> pre' done rely guarantee) ->
  {C pre C} p.
Proof.
  unfold ccorr2; intros.
  eapply H; eauto.
  eapply H0.
  eauto.
Qed.

Definition write2 a b va vb (rx : prog nat) :=
  Write a va;;
  Write b vb;;
  rx.

Theorem parallel_composition : forall ts (dones : nat -> donecond nat) pres relys guars,
  (forall tid p, ts tid = TRunning p ->
    {C pres tid C} p) ->
  (forall tid tid', tid <> tid' ->
    guars tid' =a=> relys tid) ->
  forall m,
    (forall tid,
    (pres tid) (dones tid) (relys tid) (guars tid) m) ->
  forall out,
    cexec m ts out ->
    exists m' rs,
      out = CFinished m' rs /\
      forall tid, (dones tid) (rs tid) m'.
Proof.
  intros.
  generalize dependent H.
  induction H2; intros.
  - (* CStep *)
    admit.
  - (* CFail *)
    admit.
  - (* CDone *)
    admit.
Admitted.

Theorem write2_cok : forall a b vanew vbnew rx,
  {C
    fun done rely guarantee =>
    exists F va0 varest vb0 vbrest,
    F * a |-> (va0, varest) * b |-> (vb0, vbrest) *
    [[ forall F0 F1 va vb, rely =a=> (F0 * a |-> va * b |-> vb ~>
                                      F1 * a |-> va * b |-> vb) ]] *
    [[ forall F va va' vb vb', (F * a |-> va  * b |-> vb ~>
                                F * a |-> va' * b |-> vb') =a=> guarantee ]] *
    [[ {C
         fun done_rx rely_rx guarantee_rx =>
         exists F', F' * a |-> (vanew, [va0] ++ varest) * b |-> (vbnew, [vb0] ++ vbrest) *
         [[ done_rx = done ]] *
         [[ rely =a=> rely_rx ]] *
         [[ guarantee_rx =a=> guarantee ]]
       C} rx ]]
  C} write2 a b vanew vbnew rx.
Proof.
  unfold write2; intros.

  eapply pimpl_cok. apply write_cok.
  intros. cancel.

  eapply act_impl_trans; [ eapply H3 | ].
  (* XXX need some kind of [cancel] for actions.. *)
  admit.

  eapply act_impl_trans; [ | eapply H2 ].
  (* XXX need some kind of [cancel] for actions.. *)
  admit.

  eapply pimpl_cok. apply write_cok.
  intros; cancel.

  (* XXX hmm, the [write_cok] spec is too weak: it changes [F] in the precondition
   * with [F'] in the postcondition, and thus loses all information about blocks
   * other than the one being written to.  but really we should be using [rely].
   * how to elegantly specify this in separation logic?
   *)
  admit.

  (* XXX H5 seems backwards... *)
  admit.

  (* XXX H4 seems backwards... *)
  admit.

  eapply pimpl_cok. eauto.
  intros; cancel.

  (* XXX some other issue with losing information in [write_cok]'s [F] vs [F'].. *)
  admit.

  eapply act_impl_trans; eassumption.
  eapply act_impl_trans; eassumption.
Admitted.
