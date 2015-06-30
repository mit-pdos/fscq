Require Import Mem.
Require Import Prog.
Require Import Word.
Require Import Hoare.
Require Import Pred.
Require Import RG.
Require Import Arith.

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

  Variable doneTs : nat -> Type.

  Inductive threadstate (T : Type) :=
  | TNone
  | TRunning (p : prog T)
  | TFinished (r : T)
  | TFailed.

  Definition threadstates := forall (tid : nat), threadstate (doneTs tid).
  Definition results := forall (tid : nat), option (doneTs tid).

  Definition upd_prog (ap : threadstates) (tid : nat) (p : threadstate (doneTs tid)) : threadstates.
    refine (fun tid' => if eq_nat_dec tid' tid then _ else ap tid').
    rewrite e.
    exact p.
  Defined.

  Definition upd_result (ar : results) (tid : nat) (p : doneTs tid) : results.
    refine (fun tid' => if eq_nat_dec tid' tid then _ else ar tid').
    rewrite e.
    exact (Some p).
  Defined.

  (**
   * It's a little weird that [tid] is an implicit argument for [upd_prog].
   * That's because Coq can figure out which thread ID you're updating based
   * on the type of [p'], since its return type is already dependent on its
   * thread ID..
   *)

  Inductive cstep : nat -> mem -> threadstates -> mem -> threadstates -> Prop :=
  | cstep_step : forall tid ts m p m' p',
    ts tid = TRunning p ->
    step m p m' p' ->
    cstep tid m ts m' (upd_prog ts (TRunning p))
  | cstep_fail : forall tid ts m p,
    ts tid = TRunning p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    cstep tid m ts m (upd_prog ts (@TFailed (doneTs tid)))
  | cstep_done : forall tid ts m r,
    ts tid = TRunning (Done r) ->
    cstep tid m ts m (upd_prog ts (TFinished r)).

  (**
   * The first argument of [cstep] is the PID that caused the step.
   * If we want to use [star], we should probably use [cstep_any].
   *)

  Definition cstep_any m ts m' ts' := exists tid, cstep tid m ts m' ts'.

  Definition ccorr2 (T : Type)
                    (pre : forall (done : donecond T),
                           forall (rely : @action addr (@weq addrlen) valuset),
                           forall (guarantee : @action addr (@weq addrlen) valuset),
                           @pred addr (@weq addrlen) valuset)
                    (p : prog T) : Prop.
    refine (forall (tid : nat), (_ : Prop)).
    refine (forall (done : donecond (doneTs tid)), (_ : Prop)).
    refine (forall (rely : @action addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (guarantee : @action addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (m : @mem addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (ts : threadstates), (_ : Prop)).
    refine (forall (H : T = doneTs tid), (_ : Prop)).
    subst T.
    refine (ts tid = TRunning p -> (_ : Prop)).
    refine (pre done rely guarantee m -> (_ : Prop)).
    refine ((forall tid' m' ts', tid' <> tid ->
             cstep tid' m ts m' ts' -> rely m m') /\ (_ : Prop)).
    refine (forall m' ts', cstep tid m ts m' ts' ->
            (guarantee m m' /\ ts' tid <> (@TFailed (doneTs tid)))).
  Defined.

  Inductive coutcome :=
  | CFailed
  | CFinished (m : @mem addr (@weq addrlen) valuset) (rs : results).

  Inductive cexec : mem -> threadstates -> coutcome -> Prop :=
  | CStep : forall tid ts m m' p p' out,
    ts tid = TRunning p ->
    step m p m' p' ->
    cexec m' (upd_prog ts (TRunning p')) out ->
    cexec m ts out
  | CFail : forall tid ts m p,
    ts tid = TRunning p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    cexec m ts CFailed
  | CDone : forall ts m rs,
    (forall tid, (ts tid = (@TNone (doneTs tid)) /\ rs tid = None) \/
                 exists (r : doneTs tid), (ts tid = TRunning (Done r) /\ rs tid = Some r)) ->
    cexec m ts (CFinished m rs).

End ExecConcur.


Definition write1 :=
  Write $0 $11;;
  Done 1.

Definition write2 :=
  Write $1 $22;;
  Done 2.

Theorem write1_ok : forall doneTs, ccorr2 doneTs
  (fun done rely guarantee =>
   exists F v0,
   F * $0 |-> v0 *
   [[ forall F0 F1 v, rely =a=> (F0 * $0 |-> v ~> F1 * $0 |-> v) ]] *
   [[ forall F a b, (F * $0 |-> a ~> F * $0 |-> b) =a=> guarantee ]]
  )%pred write1.
Proof.
  unfold ccorr2; intros.
  generalize dependent done.
  (* XXX dependent type mess with [doneTs].. *)
Admitted.

Theorem write2_ok : forall doneTs, ccorr2 doneTs
  (fun done rely guarantee =>
   exists F v0,
   F * $1 |-> v0 *
   [[ forall F0 F1 v, rely =a=> (F0 * $1 |-> v ~> F1 * $1 |-> v) ]] *
   [[ forall F a b, (F * $1 |-> a ~> F * $1 |-> b) =a=> guarantee ]]
  )%pred write2.
Proof.
Admitted.
