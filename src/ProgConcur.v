Require Import Mem.
Require Import Prog.
Require Import Word.

Set Implicit Arguments.


Section ExecConcur.

  Variable tidT : Type.
  Variable tid_eq : forall (t1 t2 : tidT), {t1=t2} + {t1<>t2}.
  Variable doneTs : tidT -> Type.

  Definition allprogs := forall (tid : tidT), prog (doneTs tid).
  Definition allresults := forall (tid : tidT), doneTs tid.

  Inductive concur_outcome :=
  | Failed
  | Finished (m: @mem addr (@weq addrlen) valuset) (v: allresults)
  | Crashed (m: @mem addr (@weq addrlen) valuset).

  Definition upd_prog (ap : allprogs) (tid : tidT) (p : prog (doneTs tid)) : allprogs.
    refine (fun tid' => if tid_eq tid' tid then _ else ap tid').
    rewrite e.
    exact p.
  Defined.

  Inductive exec_concur : mem -> allprogs -> concur_outcome -> Prop :=
  | XCStep : forall tid m m' p p' progs outs, progs tid = p ->
    step m p m' p' ->
    exec_concur m' (upd_prog progs p') outs ->
    (**
     * It's a little weird that [tid] is an implicit argument for [upd_prog].
     * That's because Coq can figure out which thread ID you're updating based
     * on the type of [p'], since its return type is already dependent on its
     * thread ID..
     *)
    exec_concur m progs outs
  | XCFail : forall tid m p progs, progs tid = p ->
    (~exists m' p', step m p m' p') -> (~exists r, p = Done r) ->
    exec_concur m progs Failed
  | XCCrash : forall m progs,
    exec_concur m progs (Crashed m)
  | XCDone : forall m progs results,
    (forall tid, progs tid = Done (results tid)) ->
    exec_concur m progs (Finished m results).

End ExecConcur.
