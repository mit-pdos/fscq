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

(** STAR provides a type star to represent repeated applications of
    an arbitrary binary relation R over values in A.

    We will use star here to represent the transitive closure of an
    action; that is, star a is an action where there is some sequence
    m1 m2 ... mN where a m1 m2, a m2 m3, ... a mN-1 mN hold. *)
Section STAR.

  Variable A : Type.
  Variable R : A -> A -> Prop.

  Infix "-->" := R (at level 40).

  Reserved Notation "s1 -->* s2" (at level 50).

  Inductive star : A -> A -> Prop :=
  | star_refl : forall s,
    s -->* s
  | star_step : forall s1 s2 s3,
    s1 --> s2 ->
    s2 -->* s3 ->
    s1 -->* s3
  where "s1 -->* s2" := (star s1 s2).

  Hint Constructors star.

  Reserved Notation "s1 ==>* s2" (at level 50).

  Inductive star_r : A -> A -> Prop :=
  | star_r_refl : forall s,
    s ==>* s
  | star_r_step : forall s1 s2 s3,
    s1 ==>* s2 ->
    s2 --> s3 ->
    s1 ==>* s3
  where "s2 ==>* s1" := (star_r s1 s2).

  Hint Constructors star_r.

  Lemma star_r_trans : forall s0 s1 s2,
    s1 ==>* s2 ->
    s0 ==>* s1 ->
    s0 ==>* s2.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve star_r_trans.

  Lemma star_trans : forall s0 s1 s2,
    s0 -->* s1 ->
    s1 -->* s2 ->
    s0 -->* s2.
  Proof.
    induction 1; eauto.
  Qed.

  Hint Resolve star_trans.

  Theorem star_lr_eq : forall s s',
    s -->* s' <-> s ==>* s'.
  Proof.
    intros.
    split; intros;
      induction H; eauto.
  Qed.


End STAR.

(* TODO: remove duplication *)
Hint Constructors star.
Hint Constructors star_r.

Theorem stable_star : forall AT AEQ V (p: @pred AT AEQ V) a,
  stable p a -> stable p (star a).
Proof.
  unfold stable.
  intros.
  induction H1; eauto.
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
    (* stability of precondition under rely *)
    (stable (pre done rely guarantee) rely) /\
    forall events out,
    env_exec m p events out ->
    (* any prefix where others satisfy rely,
       we will satisfy guarantee *)
    (forall n,
      let events' := firstn n events in
      (forall m0 m1, In (StepOther m0 m1) events' -> rely m0 m1) ->
      (forall m0 m1, In (StepThis m0 m1) events' -> guarantee m0 m1)) /\
    ((forall m0 m1, In (StepOther m0 m1) events -> rely m0 m1) ->
     exists md vd, out = EFinished md vd /\ done vd md).

End ExecConcurOne.

Ltac inv_label := match goal with
| [ H: StepThis ?m ?m' = StepThis _ _ |- _ ] => inversion H; clear H; subst m
| [ H: StepOther ?m ?m' = StepOther _ _ |- _ ] => inversion H; clear H; subst m
| [ H: StepThis _ _ = StepOther _ _ |- _ ] => now inversion H
| [ H: StepOther _ _ = StepThis _ _ |- _ ] => now inversion H
end.

Hint Constructors env_exec.


Notation "{C pre C} p" := (env_corr2 pre%pred p) (at level 0, p at level 60, format
  "'[' '{C' '//' '['   pre ']' '//' 'C}'  p ']'").

Theorem env_corr2_stable : forall pre p d r g m,
  {C pre C} p ->
  pre d r g m ->
  stable (pre d r g) r.
Proof.
  unfold env_corr2.
  intros.
  specialize (H _ _ _ _ H0).
  intuition.
Qed.

Lemma env_exec_progress :
  forall T (p : prog T) m, exists events out,
  env_exec m p events out.
Proof.
  intros T p.
  induction p; intros; eauto; case_eq (m a); intros.
  (* handle non-error cases *)
  all: try match goal with
  | [ _ : _ _ = Some ?p |- _ ] =>
    destruct p; edestruct H; repeat deex; repeat eexists; eauto
  end.
  (* handle error cases *)
  all: repeat eexists; eapply EXFail; intro; repeat deex;
  try match goal with
  | [ H : step _ _ _ _ |- _] => inversion H
  end; congruence.

  Grab Existential Variables.
  all: eauto.
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
  intuition.
  assert (H' := H4).
  specialize (H' _ _ H1).
  intuition.
  repeat deex.
  do 2 eexists; intuition.
  specialize (H4 (events ++ [StepOther md md']) (EFinished md' vd)).
  destruct H4.
  - eapply env_exec_append_event; eauto.
  - edestruct H6.
    intros.
    match goal with
    | [ H: In _ (_ ++ _) |- _ ] => apply in_app_or in H; destruct H;
      [| inversion H]
    end.
    apply H2; auto.
    congruence.
    contradiction.
    deex.
    congruence.
Qed.

Example rely_stutter_ok : forall pre p,
  {C pre C} p ->
  {C fun d r g => pre d (r \/ act_id_any)%act g C} p.
Proof.
  unfold env_corr2, act_or.
  intros.
  edestruct H; eauto.
  intuition.
  - (* stability *)
    unfold stable; intros.
    eauto.
  - eapply H2; eauto.
  - eapply H2; eauto.
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
    (forall tid p, ts tid = TRunning p -> p = Done (rs tid)) ->
    cexec m ts (CFinished m rs).

  Definition corr_threads (pres : forall (tid : nat),
                                  forall (done : donecond nat),
                                  forall (rely : @action addr (@weq addrlen) valuset),
                                  forall (guarantee : @action addr (@weq addrlen) valuset),
                                  @pred addr (@weq addrlen) valuset)
                          (ts : threadstates) :=
    forall dones relys guarantees m out,
    (forall tid p, ts tid = TRunning p ->
      (pres tid) (dones tid) (relys tid) (guarantees tid) m) ->
    cexec m ts out ->
    exists m' rs, out = CFinished m' rs /\
    (forall tid p, ts tid = TRunning p -> (dones tid) (rs tid) m').

End ExecConcurMany.

Ltac inv_ts :=
  match goal with
  | [ H: TRunning ?p = TRunning ?p' |- _ ] => inversion H; clear H;
      (* these might fail if p and/or p' are not variables *)
      try subst p; try subst p'
  end.

Ltac inv_coutcome :=
  match goal with
  | [ H: CFinished ?m ?rs = CFinished ?m' ?rs' |- _ ] => inversion H; clear H;
      try subst m; try subst rs;
      try subst m'; try subst rs'
  end.

Definition pres_step (pres : forall (tid : nat),
                                  forall (done : donecond nat),
                                  forall (rely : @action addr (@weq addrlen) valuset),
                                  forall (guarantee : @action addr (@weq addrlen) valuset),
                                  @pred addr (@weq addrlen) valuset)
                      (tid0:nat) m m' :=
  fun tid d r g (mthis : @mem addr (@weq addrlen) valuset) =>
    (pres tid) d r g m /\
    if (eq_nat_dec tid0 tid) then star r m' mthis
    else (pres tid) d r g mthis.

Lemma ccorr2_step : forall pres tid m m' p p',
  {C pres tid C} p ->
  step m p m' p' ->
  {C (pres_step pres tid m m') tid C} p'.
Proof.
  unfold pres_step, env_corr2.
  intros.
  destruct (eq_nat_dec tid tid); [|congruence].
  assert (H' := H).
  intuition; subst;
  specialize (H _ _ _ _ H2); intuition.

  - unfold stable; intros.
    intuition.
    eapply star_trans; eauto.

  - apply star_lr_eq in H3.
    generalize dependent events.
    generalize dependent n.
    induction H3; intros.
    * eapply H7 with (events := StepThis m s :: events) (n := S n);
      eauto; intros.
      simpl in H.
      destruct H; try congruence.
      apply H4; auto.
      simpl.
      intuition.
    * apply IHstar_r with (events := StepOther s2 s3 :: events)
        (n := S n); eauto.
      all: simpl; intuition; congruence.
 - apply star_lr_eq in H3.
    generalize dependent events.
    induction H3; intros.
    * eapply H' with (events := StepThis m s :: events); eauto.
      intros.
      inversion H; [congruence|].
      eauto.
    * eapply IHstar_r; eauto.
      intros ? ? Hin; inversion Hin.
      congruence.
      eauto.
Qed.

Lemma stable_and : forall AT AEQ V P (p: @pred AT AEQ V) a,
  stable p a ->
  stable (fun m => P /\ p m) a.
Proof.
  intros.
  unfold stable; intros.
  intuition eauto.
Qed.

Lemma ccorr2_stable_step : forall pres tid tid' m m' p,
  {C pres tid C} p ->
  tid <> tid' ->
  {C (pres_step pres tid' m m') tid C} p.
Proof.
  unfold pres_step, env_corr2.
  intros.
  destruct (eq_nat_dec tid' tid); [congruence|].
  inversion H1.
  match goal with
  | [ Hpre: pres _ _ _ _ m0 |- _ ] =>
    specialize (H _ _ _ _ Hpre)
  end.
  intuition.
  apply stable_and; auto.
Qed.

Ltac compose_helper :=
  match goal with
  | [ H: context[_ =a=> _] |- _ ] =>
    (* first solve a pre goal,
       then do the <>, then eauto *)
    (* TODO: re-write this with two matches *)
    eapply H; [| | | now eauto | ]; [| | eauto |]; eauto
  end.

Ltac upd_prog_case' tid tid' :=
  destruct (eq_nat_dec tid tid');
    [ rewrite upd_prog_eq' in * by auto; subst tid |
      rewrite upd_prog_ne in * by auto ].

Ltac upd_prog_case :=
  match goal with
  | [ H: upd_prog _ ?tid _ ?tid' = _ |- _] => upd_prog_case' tid tid'
  | [ |- upd_prog _ ?tid _ ?tid' = _ ] => upd_prog_case' tid tid'
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
  edestruct H3; eauto.
  destruct H5; eauto.
  intros; contradiction.
  repeat deex.
  congruence.
Qed.

Lemma ccorr2_single_step_guarantee : forall pre d r g p m p' m',
  {C pre C} p ->
  step m p m' p' ->
  pre d r g m ->
  g m m'.
Proof.
  intros.
  assert (Hprogress := env_exec_progress p' m').
  repeat deex.
  eapply H with (n := 1) (events := StepThis m m' :: events);
    eauto.
  all: simpl; intuition.
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
  generalize dependent pres.
  generalize dependent dones.
  generalize dependent relys.
  generalize dependent guarantees.
  induction H1; simpl; intros.

  + (* thread [tid] did a legal step *)
    edestruct IHcexec; clear IHcexec.
    instantiate (pres := pres_step pres tid m m').
    * intros.
      intuition.
      -- upd_prog_case.
        ++ inv_ts.
           eapply ccorr2_step; eauto.
           edestruct H2; eauto.
        ++ eapply ccorr2_stable_step; eauto.
           edestruct H2; eauto.
      -- unfold pres_step in *.
         upd_prog_case; upd_prog_case; try congruence;
           subst; intuition; try inv_ts.
         all: eapply H2 with (tid' := tid') (tid := tid0) (m := m); eauto.
    * unfold pres_step; intros.
    upd_prog_case; eauto.
    intuition eauto.

    eapply env_corr2_stable with (m := m); eauto.
    apply H2; eauto.
    (* turn the goal into proving tid's g *)
    assert (guarantees tid =a=> relys tid0) as Hguar by compose_helper;
      apply Hguar; clear Hguar.

    edestruct H2 with (tid := tid); eauto.
    eapply ccorr2_single_step_guarantee; eauto.

    * deex; repeat eexists; intros.
      (* we need to destruct first because the program running at tid0 will
         depend on whether tid = tid0 *)
      destruct (eq_nat_dec tid tid0);
        eapply H6.
      rewrite upd_prog_eq'; eauto.
      rewrite upd_prog_ne; eauto.

  + (* thread [tid] failed *)
    edestruct H2; eauto.
    exfalso.
    eapply ccorr2_no_fail; eauto.

  + do 2 eexists; intuition eauto.
    case_eq (ts tid); intros; [congruence|].
    edestruct H0; eauto.
    unfold env_corr2 in H4.
    specialize (H1 _ _ H2).
    specialize (H4 _ _ _ _ H1).
    intuition.
    assert (env_exec m p0 nil (EFinished m (rs tid))) as Hexec.
    match goal with
    | [ H': _ = TRunning p0, H: context[_ = TRunning _ -> _] |- _] =>
      apply H in H'; rewrite H'
    end; auto.
    specialize (H7 _ _ Hexec).
    intuition.
    edestruct H8.
    intros ? ? Hin; inversion Hin.
    deex.
    congruence.
Qed.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Lemma act_star_ptsto : forall AT AEQ V F a v (m1 m2: @mem AT AEQ V),
  (F * a |-> v)%pred m1 ->
  ( (F ~> F) * act_id_pred (a |->?) )%act m1 m2 ->
  (F * a |-> v)%pred m2.
Proof.
  intros.
  eapply act_star_stable_invariant_preserves; eauto.
  apply ptsto_preserves.
Qed.

Local Hint Resolve in_eq.
Local Hint Resolve in_cons.
Local Hint Resolve act_star_ptsto.

Lemma act_ptsto_upd : forall AT AEQ V F a old new (m: @mem AT AEQ V),
  (F * a |-> old)%pred m ->
  (act_id_any * (a |-> old ~> a |-> new))%act m (upd m a new).
Proof.
  unfold_sep_star.
  unfold act_star, act_bow.
  intros.
  repeat deex.
  do 4 eexists.
  (* prove this first since it's used twice *)
  assert (mem_disjoint m1 (upd m2 a new)).
    rewrite mem_disjoint_comm.
    eapply mem_disjoint_upd.
    eapply ptsto_valid.
    pred_apply; cancel.
    now (apply mem_disjoint_comm; auto).
  intuition eauto.
  - apply act_id_any_refl.
  - apply emp_star.
    apply sep_star_comm.
    eapply ptsto_upd.
    pred_apply; cancel.
  - rewrite mem_union_comm by auto.
    rewrite mem_union_comm with (m1 := m1) by auto.
    erewrite mem_union_upd; auto.
    eapply ptsto_valid.
    pred_apply; cancel.
Qed.

(** Wrapper for {C pre C} that constructs a pre function from separate
    precondition, rely, guarantee and post statements, all under a common
    set of (existential) binders.

    We encode the postcondition as follows: The precondition of p rx includes
    {C post C} rx and captures the done predicate. Since this is the only way to
    prove done, proving this statement requires also proving the postcondition
    for after p executes.

    Analogous to the Hoare notation {!< ... >!}, similarly lacking a frame
    predicate. We do this here because we don't yet know how the frame
    should be incorporated into the rely condition, having seen few examples.
*)
Notation "{!C< e1 .. e2 , 'PRE' pre 'RELY' rely 'GUAR' guar 'POST' post >C!} p1" :=
  (forall (rx: _ -> prog nat),
    {C
      fun done rely_ guar_ =>
        (exis (fun e1 => .. (exis (fun e2 =>
        (* the %pred%act causes both pre occurrences to use the same
           scope stack *)
         pre%pred%act *
         [[ act_and (pre ~> any) rely_ =a=> rely%act ]] *
         [[ guar%act =a=> guar_ ]] *
         [[ forall ret_,
            {C
              fun done_rx rely_rx guar_rx =>
              post emp ret_ *
              [[ done_rx = done ]] *
              [[ rely_rx =a=> rely_ ]] *
              [[ guar_ =a=> guar_rx ]]
            C} rx ret_ ]]
         )) .. ))
     C} p1 rx)
   (at level 0, p1 at level 60,
    e1 binder, e2 binder,
    only parsing).

Lemma pre_and_rely : forall AT AEQ V pre (m1 m2:@mem AT AEQ V) rely_ r,
  (pre ~> any) /\ rely_ =a=> r ->
  rely_ m1 m2 ->
  pre m1 ->
  r m1 m2.
Proof.
  firstorder.
Qed.

Ltac match_rely_pre :=
  match goal with
  | [ H1: (?pre ~> any) /\ _ =a=> _ |- _ ] =>
    match goal with
    | [ H2: pre ?m1 |- _ ?m2 ] =>
      generalize (pre_and_rely m1 m2 H1)
    end
  end.

Theorem write_cok : forall a vnew,
  {!C< F v0 vrest,
  PRE F * a |-> (v0, vrest)
  RELY (F ~> F) * act_id_pred (a |->?)
  GUAR act_id_any *
         (a |-> (v0, vrest) ~> a |-> (vnew, [v0] ++ vrest))
  POST RET:r F * a |-> (vnew, [v0] ++ vrest)
  >C!} Write a vnew.
Proof.
  unfold env_corr2 at 1; intros.
  destruct_lift H.
  intuition.
  (* stability *)
  - unfold stable; intros;
    destruct_lift H0.
    repeat eexists.
    repeat apply sep_star_lift_apply'; eauto.
    match_rely_pre; eauto.
  (* guarantee *)
  - remember (Write a vnew rx) as p.
    generalize dependent n.
    induction H0; intros.
    * subst p.
      inversion H0; subst.
      (* prove n = S n' *)
      destruct n; simpl in *.
        contradiction.
      assert (m a = Some (v1, vrest)) as Hma'.
      eapply ptsto_valid.
      pred_apply; cancel.
      rewrite Hma' in H13.
      inversion H13; subst.
      intuition.
      + (* StepThis was the Write *)
        inv_label.
        apply H3.
        eapply act_ptsto_upd; eauto.
      + (* StepThis was in rx *)
        eapply H2; eauto.
        repeat apply sep_star_lift_apply'; eauto.
        apply pimpl_star_emp.
        apply sep_star_comm.
        eapply ptsto_upd;
          pred_apply; cancel.
        intros; eauto.
    * destruct n; contradiction.
    * destruct n; simpl in *.
        contradiction.
      intuition (try congruence; eauto).
      eapply IHenv_exec; eauto.
      match_rely_pre; eauto.
    * destruct n; contradiction.
 (* done condition *)
 - remember (Write a vnew rx) as p.
   induction H0; intros; try subst p.
   * inversion H0; subst.
     eapply H2; eauto.
     repeat apply sep_star_lift_apply'; eauto.
     assert (m a = Some (v1, vrest)) as Hma'.
     eapply ptsto_valid.
     pred_apply; cancel.
     rewrite Hma' in H12.
     inversion H12; subst.
     apply pimpl_star_emp.
     apply sep_star_comm.
     eapply ptsto_upd;
       pred_apply; cancel.
     intros; eauto.
   * contradiction H0.
     repeat eexists; eauto.
     econstructor.
     eapply ptsto_valid.
     pred_apply; cancel.
   * eapply IHenv_exec; eauto.
     match_rely_pre; eauto.
   * congruence.
Qed.

Theorem pimpl_cok : forall pre pre' (p : prog nat),
  {C pre' C} p ->
  (forall done rely guarantee, pre done rely guarantee =p=> pre' done rely guarantee) ->
  (forall done rely guarantee m, pre done rely guarantee m
    -> stable (pre done rely guarantee) rely) ->
  {C pre C} p.
Proof.
  unfold env_corr2; intros; eauto.
  intuition.
  - unfold stable; intros.
    eapply H1; eauto.
  - eapply H; eauto.
    apply H0; eauto.
  - eapply H; eauto.
    apply H0; eauto.
Qed.

Definition write2 a b va vb (rx : unit -> prog nat) :=
  Write a va;;
  Write b vb;;
  rx tt.

Lemma pre_and_impl : forall AT AEQ V (rely: @action AT AEQ V)
  pre pre' r r',
  pre' ~> any /\ rely =a=> r' ->
  pre =p=> pre' ->
  pre ~> any /\ r' =a=> r ->
  pre ~> any /\ rely =a=> r.
Proof.
  intros.
  rewrite <- H1.
  eapply act_impl_trans; [|eauto].
  unfold act_and, act_impl, act_bow.
  firstorder.
Qed.

Lemma stable_and_empty : forall AT AEQ V P (p: @pred AT AEQ V) a,
  stable p a ->
  stable (p * [[P]]) a.
Proof.
  unfold stable.
  intros.
  destruct_lift H0.
  eapply H in H0; eauto.
  pred_apply; cancel.
Qed.

Lemma stable_and_empty_rev : forall AT AEQ V (P:Prop) (p: @pred AT AEQ V) a,
  P ->
  stable (p * [[P]]) a ->
  stable p a.
Proof.
  unfold stable.
  intros.
  assert ((p * [[P]])%pred m2).
  eapply H0; eauto.
  pred_apply; cancel.
  pred_apply; cancel.
Qed.

Theorem write2_cok : forall a b vanew vbnew,
  {!C< F va0 varest vb0 vbrest,
  PRE F * a |-> (va0, varest) * b |-> (vb0, vbrest)
  RELY (F ~> F) * act_id_pred (a |->? * b |->?)
  GUAR act_id_any * ((a |->? * b |->?) ~> (a |->? * b |->?))
  POST RET:r F * a |-> (vanew, [va0] ++ varest) *
                 b |-> (vbnew, [vb0] ++ vbrest)
  >C!} write2 a b vanew vbnew.
Proof.
  unfold write2; intros.

  eapply pimpl_cok. apply write_cok.
  intros. cancel.

  eapply pre_and_impl; eauto.
  cancel.
  admit.

  rewrite <- H2.
  apply act_impl_star; auto.
  (* TODO: need to fix guarantee in the same way as rely;
     this isn't provable since we can't prove b |->? *)
  admit.

  eapply pimpl_cok. apply write_cok.
  intros; cancel.

  rewrite H5.
  (* act_cancel *)
  admit.

  rewrite <- H4.
  rewrite <- H2.
  (* act_cancel *)
  (* similarly need pre to prove a |->? *)
  admit.

  (* same as H1 with a emp * in front *)
  eapply pimpl_cok.
  apply H1.
  cancel.
  (* trivial action impls *)
  eapply act_impl_trans; eauto.
  eapply act_impl_trans; eauto.

  (* remaining goals are stability *)

  - intros.
    (* this proof is sort of cheating: our rely-guarantee spec supposes
       that the postcondition is stable under rely by making a {C ... C}
       statement about rx, and that's what we're proving here;
       if the postcondition weren't stable under rely, the spec would be
       useless since it would assume a contradiction, and this would be hard to
       figure out. *)
    destruct_lift H; subst.
    repeat apply stable_and_empty.
    edestruct H1 with (m:=m). pred_apply. cancel.
    unfold stable; intros m1 m2; intros.
    match goal with
    | [ H: stable _ rely |- _ ] =>
        repeat (apply stable_and_empty_rev in H; [| now auto]);
        unfold stable in H;
        specialize (H m1 m2)
     end.
     eapply pimpl_apply; [| apply H0]; auto.
     cancel.
     pred_apply; cancel.

  - intros.
    destruct_lift H; subst.
    repeat apply stable_and_empty.
    unfold stable; intros.
    apply pimpl_star_emp.
    apply emp_star in H0.
    apply H6 in H4.
    (* Now we're stuck; the only way to get the real rely condition
       (F ~> F) * [a |->? * b |->?] is to show that a and b point to the old
       values in m1 (and use H3), but this isn't true now that we've written.
       Somehow our own guarantee needs to be allowed in (pre ~> any) =a=> rely
       for the intermediate instructions. *)
    admit.

  - intros.
    destruct_lift H; subst.
    (* Why are there existential binders under the {C .. C}?
       if they aren't universally quantified, we can't make use of H4,
       the =a=> we have about rely, which will make this impossible to prove.

       It's that this is how {!< >!} and {< >} (CHL) work for Hoare logic,
       but not {<< >>} (crash+recovery semantics), which has universal
       quantification outside the Hoare tuple. *)
    admit.

  Grab Existential Variables.
  all: auto.
Admitted.
