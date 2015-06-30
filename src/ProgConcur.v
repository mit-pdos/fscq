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

End STAR.


Section ExecConcur.

  Inductive threadstate :=
  | TNone
  | TRunning (p : prog nat)
  | TFinished (r : nat)
  | TFailed.

  Inductive some_result :=
  | Res (r : nat).

  Definition threadstates := forall (tid : nat), threadstate.
  Definition results := forall (tid : nat), option some_result.

  Definition upd_prog (ap : threadstates) (tid : nat) (p : threadstate) :=
    fun tid' => if eq_nat_dec tid' tid then p else ap tid'.

  Lemma upd_prog_eq : forall ap tid p, upd_prog ap tid p tid = p.
  Proof.
    unfold upd_prog; intros; destruct (eq_nat_dec tid tid); congruence.
  Qed.

  Lemma upd_prog_ne : forall ap tid p tid', tid <> tid' -> upd_prog ap tid p tid' = ap tid'.
  Proof.
    unfold upd_prog; intros; destruct (eq_nat_dec tid' tid); congruence.
  Qed.

  Inductive cstep : nat -> mem -> threadstates -> mem -> threadstates -> Prop :=
  | cstep_step : forall tid ts m (p : prog nat) m' p',
    ts tid = TRunning p ->
    step m p m' p' ->
    cstep tid m ts m' (upd_prog ts tid (TRunning p))
  | cstep_fail : forall tid ts m (p : prog nat),
    ts tid = TRunning p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    cstep tid m ts m (upd_prog ts tid TFailed)
  | cstep_done : forall tid ts m (r : nat),
    ts tid = TRunning (Done r) ->
    cstep tid m ts m (upd_prog ts tid (TFinished r)).

  (**
   * The first argument of [cstep] is the PID that caused the step.
   * If we want to use [star], we should probably use [cstep_any].
   *)

  Definition cstep_any m ts m' ts' := exists tid, cstep tid m ts m' ts'.

  Definition ccorr2 (pre : forall (done : donecond nat),
                           forall (rely : @action addr (@weq addrlen) valuset),
                           forall (guarantee : @action addr (@weq addrlen) valuset),
                           @pred addr (@weq addrlen) valuset)
                    (p : prog nat) : Prop.
    refine (forall (tid : nat), (_ : Prop)).
    refine (forall (done : donecond nat), (_ : Prop)).
    refine (forall (rely : @action addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (guarantee : @action addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (m : @mem addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (ts : threadstates), (_ : Prop)).
    refine (ts tid = TRunning p -> (_ : Prop)).
    refine (pre done rely guarantee m -> (_ : Prop)).
    refine ((forall m' ts', star cstep_any m ts m' ts' ->
             forall tid'' m'' ts'', tid'' <> tid ->
             cstep tid'' m' ts' m'' ts'' -> rely m' m'') -> (_ : Prop)).
    refine (forall m' ts', star cstep_any m ts m' ts' -> (_ : Prop)).
    refine (forall m'' ts'', cstep tid m' ts' m'' ts'' -> (_ : Prop)).
    refine (guarantee m' m'' /\ ts'' tid <> TFailed /\
            (forall r, ts'' tid = TFinished r -> done r m'')).
  Defined.

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
    (forall tid, (ts tid = TNone /\ rs tid = None) \/
                 exists r, (ts tid = TRunning (Done r) /\ rs tid = Some (Res r))) ->
    cexec m ts (CFinished m rs).

End ExecConcur.

Notation "{C pre C} p" := (ccorr2 pre%pred p) (at level 0, p at level 60).

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

Theorem write_cok : forall a vnew rx,
  {C
    fun done rely guarantee =>
    exists F v0 vrest,
    F * a |-> (v0, vrest) *
    [[ forall F0 F1 v, rely =a=> (F0 * a |-> v ~> F1 * a |-> v) ]] *
    [[ forall F x y, (F * a |-> x ~> F * a |-> y) =a=> guarantee ]] *
    [[ {C
         fun done_rx rely_rx guarantee_rx =>
         F * a |-> (vnew, [v0] ++ vrest) *
         [[ done_rx = done ]] *
         [[ rely =a=> rely_rx ]] *
         [[ guarantee_rx =a=> guarantee ]]
       C} rx tt ]]
  C} Write a vnew rx.
Proof.
  unfold ccorr2; intros.
  destruct_lift H0.
  induction H2.
  - (* Base case: we are still in the starting state. *)
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
      exfalso. apply H4. do 2 eexists.
      constructor.
      apply sep_star_comm in H0. apply ptsto_valid in H0. eauto.
    + (* cstep_done *)
      congruence.
  - (* Inductive case: we made some steps. *)
    (* XXX should have probably strengthened the inductive hypothesis.. *)
    admit.
Admitted.
