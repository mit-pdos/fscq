Require Import EventCSL.
Require Import PeanoNat.
Require Import Hlist.

(** Execution semantics for running several programs concurrently with
cooperative scheduling.

We want validity proofs in the single-program execution semantics to
translate into concurrent validity as long as threads agree on a
common invariant and relation with shared memory and ghost state. *)
Section ConcurrentSemantics.

  Variable Mcontents : list Set.
  Definition M := EventCSL.M Mcontents.

  (** Programs can manipulate ghost state of type S *)
  Variable S:Type.

  (** For simplicity, all programs must return values of type T *)
  Variable T:Type.

  Definition prog := prog Mcontents S T.

  Definition threads := ID -> option prog.
  Definition state : Type := ID * state Mcontents S.
  Variable StateR : ID -> Relation Mcontents S.
  Variable StateI : Invariant Mcontents S.

  Definition step := @step Mcontents S T StateR StateI.

  Definition upd ts id0 p' : threads :=
    fun id => if (Nat.eq_dec id id0) then Some p' else (ts id).

  Definition var := var Mcontents.

  (* TODO: this allows any interleaving; actually, a given thread is
  executing until a Yield/AcquireLock, which means we need a rule for
  each prog constructor, and need to track the current thread in state *)
  Inductive tstep : state -> threads -> state -> threads -> Prop :=
    (* boring rules that step one thread *)
  | TStepRead : forall tid ts st p' st'
                  a rx,
      ts tid = Some (Read a rx) ->
      step tid st (Read a rx) st' p' ->
      tstep (tid, st) ts (tid, st') (upd ts tid p')
  | TStepWrite : forall tid ts st p' st'
                  a v rx,
      ts tid = Some (Write a v rx) ->
      step tid st (Write a v rx) st' p' ->
      tstep (tid, st) ts (tid, st') (upd ts tid p')
  | TStepCommit : forall tid ts st p' st'
                  up rx,
      ts tid = Some (Commit up rx) ->
      step tid st (Commit up rx) st' p' ->
      tstep (tid, st) ts (tid, st') (upd ts tid p')
  | TStepGetTID : forall tid ts st p' st'
                  rx,
      ts tid = Some (GetTID rx) ->
      step tid st (GetTID rx) st' p' ->
      tstep (tid, st) ts (tid, st') (upd ts tid p')
  | TStepGet : forall tid ts st p' st'
                  t (v: var t) rx,
      ts tid = Some (Get v rx) ->
      step tid st (Get v rx) st' p' ->
      tstep (tid, st) ts (tid, st') (upd ts tid p')
  | TStepAssgn : forall tid ts st p' st'
                  t (v: var t) val rx,
      ts tid = Some (Assgn v val rx) ->
      step tid st (Assgn v val rx) st' p' ->
      tstep (tid, st) ts (tid, st') (upd ts tid p')
    (* note that its possibly for this step to give execution
    to the same thread (that is, Yield immediately returns
    without modifying anything) *)
  | TStepYieldToYield : forall tid tid' ts st rx rx',
      ts tid = Some (Yield rx) ->
      ts tid' = Some (Yield rx') ->
      (* tid' executes, starting at its continuation *)
      tstep (tid, st) ts (tid', st) (upd ts tid' (rx' tt))
  | TStepYieldToLock : forall tid tid' ts
                         d m s0 s l rx rx',
      ts tid = Some (Yield rx) ->
      ts tid' = Some (AcquireLock l rx') ->
      get l m = Open ->
      tstep (tid, (d, m, s0, s)) ts
            (* tid' begins execution, gets the lock *)
            (tid', (d, set l (Locked tid') m, s0, s))
            (* ... and continues *)
            (upd ts tid' (rx' tt))
    (* copies of the above, except starting from an AcquireLock *)
  | TStepLockToYield : forall tid tid' ts st
                          l rx rx',
      ts tid = Some (AcquireLock l rx) ->
      ts tid' = Some (Yield rx') ->
      (* tid' executes, starting at its continuation *)
      tstep (tid, st) ts (tid', st) (upd ts tid' (rx' tt))
  | TStepLockToLock : forall tid tid' ts
                         l' d m s0 s l rx rx',
      ts tid = Some (AcquireLock l' rx) ->
      ts tid' = Some (AcquireLock l rx') ->
      get l m = Open ->
      tstep (tid, (d, m, s0, s)) ts
            (* tid' begins execution, gets the lock *)
            (tid', (d, set l (Locked tid') m, s0, s))
            (* ... and continues *)
            (upd ts tid' (rx' tt))
  | TStepDone : forall tid st ts tid' v,
      ts tid = Some (Done _ _ v) ->
      (forall v', ts tid' <> Some (Done _ _ v')) ->
      tstep (tid, st) ts (tid', st) ts.

  Definition outcomes := ID -> option (outcome T).
  Definition thread_outcomes (ts:threads) d :=
    fun id =>
      match ts id with
      | None => None
      | Some (Done _ _ v) => Some (Finished d v)
      | Some _ => None
      end.

  Inductive cexec : state -> threads -> outcomes -> Prop :=
  | CExecAllDone : forall tid d m s0 s ts,
      (forall id p, ts id = Some p -> exists v, p = Done _ _ v) ->
      cexec (tid, (d, m, s0, s)) ts (thread_outcomes ts d)
  (* TODO: add fail upon fail_step *)
  | CExecStep : forall st ts st' ts' outs,
      tstep st ts st' ts' ->
      cexec st' ts' outs ->
      cexec st ts outs.

  (* TODO: valid for concurrent setting *)

  Definition doneconds := ID -> option (donecond T).

End ConcurrentSemantics.
