Require Import EventCSL.

Section RecoveryExecution.

  Variable Mcontents : list Set.
  Variable S : Type.

  Variable StateR : ID -> Relation S.
  Variable LockR : ID -> Relation S.
  Variable StateI : Invariant Mcontents S.
  Variable LockI : Invariant Mcontents S.

  Variable empty_mem : M Mcontents.
  Variable empty_s : S.

  Notation exec := (@exec Mcontents S _ StateR LockR StateI LockI).

  Inductive recover_outcome (TF TR:Type) :=
  | RFailed
  | RFinished (d:DISK) (v: TF)
  | RRecovered (d:DISK) (v: TR).

  Inductive exec_recover (TF TR:Type)
            (tid:ID) (st:DISK * M Mcontents * S * S)
    : forall (p:prog Mcontents S TF) (recovery_p:prog Mcontents S TR),
      recover_outcome TF TR -> Prop :=
  | ExecRecoverFail : forall p rec,
      exec tid st p (Failed _) ->
      exec_recover TF TR tid st p rec (RFailed _ _)
  | ExecRecoverFinish : forall p rec d v,
      exec tid st p (Finished d v) ->
      exec_recover TF TR tid st p rec (RFinished _ _ d v)
  | ExecRecoverCrashFinish : forall p rec d d' v,
      exec tid st p (Crashed _ d) ->
      exec_recover TR TR tid (d, empty_mem, empty_s, empty_s)
                   rec rec (RFinished _ _ d' v) ->
      exec_recover TF TR tid st p rec (RRecovered _ _ d' v)
  | ExecRecoverCrashRecover : forall p rec d d' v,
      exec tid st p (Crashed _ d) ->
      exec_recover TR TR tid (d, empty_mem, empty_s, empty_s)
                   rec rec (RRecovered _ _ d' v) ->
      exec_recover TF TR tid st p rec (RRecovered _ _ d' v).

End RecoveryExecution.