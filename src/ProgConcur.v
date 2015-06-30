Require Import Mem.
Require Import Prog.
Require Import Word.
Require Import Hoare.
Require Import Pred.
Require Import RG.
Require Import Arith.
Require Import SepAuto.

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
  | TRunning (T : Type) (p : prog T)
  | TFinished (T : Type) (r : T)
  | TFailed.

  Inductive some_result :=
  | Res (T : Type) (r : T).

  Definition threadstates := forall (tid : nat), threadstate.
  Definition results := forall (tid : nat), option some_result.

  Definition upd_prog (ap : threadstates) (tid : nat) (p : threadstate) :=
    fun tid' => if eq_nat_dec tid' tid then p else ap tid'.

  Inductive cstep : nat -> mem -> threadstates -> mem -> threadstates -> Prop :=
  | cstep_step : forall T tid ts m (p : prog T) m' p',
    ts tid = TRunning p ->
    step m p m' p' ->
    cstep tid m ts m' (upd_prog ts tid (TRunning p))
  | cstep_fail : forall T tid ts m (p : prog T),
    ts tid = TRunning p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    cstep tid m ts m (upd_prog ts tid TFailed)
  | cstep_done : forall T tid ts m (r : T),
    ts tid = TRunning (Done r) ->
    cstep tid m ts m (upd_prog ts tid (TFinished r)).

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
    refine (forall (done : donecond T), (_ : Prop)).
    refine (forall (rely : @action addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (guarantee : @action addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (m : @mem addr (@weq addrlen) valuset), (_ : Prop)).
    refine (forall (ts : threadstates), (_ : Prop)).
    refine (ts tid = TRunning p -> (_ : Prop)).
    refine (pre done rely guarantee m -> (_ : Prop)).
    refine ((forall tid' m' ts', tid' <> tid ->
             cstep tid' m ts m' ts' -> rely m m') -> (_ : Prop)).
    refine (forall m' ts', cstep tid m ts m' ts' ->
            (guarantee m m' /\ ts' tid <> TFailed)).
  Defined.

  Inductive coutcome :=
  | CFailed
  | CFinished (m : @mem addr (@weq addrlen) valuset) (rs : results).

  Inductive cexec : mem -> threadstates -> coutcome -> Prop :=
  | CStep : forall T tid ts m m' (p : prog T) p' out,
    ts tid = TRunning p ->
    step m p m' p' ->
    cexec m' (upd_prog ts tid (TRunning p')) out ->
    cexec m ts out
  | CFail : forall T tid ts m (p : prog T),
    ts tid = TRunning p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    cexec m ts CFailed
  | CDone : forall ts m rs,
    (forall tid, (ts tid = TNone /\ rs tid = None) \/
                 exists r, (ts tid = TRunning (Done r) /\ rs tid = Some r)) ->
    cexec m ts (CFinished m rs).

End ExecConcur.


Definition write1 :=
  Write $0 $11;;
  Done 1.

Definition write2 :=
  Write $1 $22;;
  Done 2.

Theorem write1_ok : ccorr2
  (fun done rely guarantee =>
   exists F v0,
   F * $0 |-> v0 *
   [[ forall F0 F1 v, rely =a=> (F0 * $0 |-> v ~> F1 * $0 |-> v) ]] *
   [[ forall F a b, (F * $0 |-> a ~> F * $0 |-> b) =a=> guarantee ]]
  )%pred write1.
Proof.
  unfold ccorr2, write1; intros.
  destruct_lift H0.
Admitted.

Theorem write2_ok : ccorr2
  (fun done rely guarantee =>
   exists F v0,
   F * $1 |-> v0 *
   [[ forall F0 F1 v, rely =a=> (F0 * $1 |-> v ~> F1 * $1 |-> v) ]] *
   [[ forall F a b, (F * $1 |-> a ~> F * $1 |-> b) =a=> guarantee ]]
  )%pred write2.
Proof.
Admitted.
