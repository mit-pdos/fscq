Require Import AsyncDisk.
Require Import Word.
Require Import Mem Pred.
Require Import PeanoNat.
Require Import Hashmap.
Require Import Relation_Operators.
Require Automation.

Global Set Implicit Arguments.

Inductive ReadState := Pending | NoReader.
Notation DISK := (@mem addr addr_eq_dec (valu * ReadState)).

Polymorphic Inductive Var :=
| val : forall T, T -> Var
(* abstraction (ghost) variable *)
| abs : forall T, T -> Var.

Definition ident := nat.
Opaque ident.

Notation heap := (@mem ident Nat.eq_dec Var).
Notation heappred := (@pred ident Nat.eq_dec Var).

(* The states a program steps through. *)
Inductive Sigma :=
| state (d:DISK) (m:heap) (hm:hashmap).

Module Sigma.
  Definition disk (sigma:Sigma) :=
    let (d, _, _) := sigma in d.
  Definition mem (sigma:Sigma) :=
    let (_, m, _) := sigma in m.
  Definition hm (sigma:Sigma) :=
    let (_, _, hm) := sigma in hm.

  Definition set_mem (sigma:Sigma) i v :=
    let (d, m, hm) := sigma in state d (upd m i v) hm.
  Definition upd_disk (sigma:Sigma) (d':DISK -> DISK) :=
    let (d, m, hm) := sigma in state (d' d) m hm.
  Definition upd_hm (sigma:Sigma) sz (buf: word sz) :=
    let (d, m, hm) := sigma in state d m (upd_hashmap' hm (hash_fwd buf) buf).
End Sigma.

Section CCL.

  Definition TID := nat.
  Opaque TID.

  CoInductive cprog : Type -> Type :=
  | Alloc A (v0:A) : cprog (ident)
  | Get A (i:ident) : cprog A
  | Assgn A (i:ident) (v:A) : cprog unit
  | GhostUpdate A (i:ident) (update: TID -> A -> A) : cprog unit
  | BeginRead (a:addr) : cprog unit
  | WaitForRead (a:addr) : cprog valu
  | Write (a:addr) (v: valu) : cprog unit
  | Hash sz (buf: word sz) : cprog (word hashlen)
  | Yield : cprog unit
  | Ret T (v:T) : cprog T
  | Bind T T' (p: cprog T') (p': T' -> cprog T) : cprog T.

  Inductive step (tid:TID) (sigma: Sigma) :
    forall T, cprog T -> Sigma -> T -> Prop :=
  | StepAlloc : forall A (v0:A) i,
      Sigma.mem sigma i = None ->
      step tid sigma (Alloc v0) (Sigma.set_mem sigma i (val v0)) i
  | StepGet : forall A (i: ident) (v:A),
      Sigma.mem sigma i = Some (val v) ->
      step tid sigma (Get A i) sigma v
  | StepAssgn : forall A i (v:A) (v0:A),
      Sigma.mem sigma i = Some (val v0) ->
      step tid sigma (Assgn i v) (Sigma.set_mem sigma i (val v)) tt
  | StepGhostUpdate : forall A i (up: TID -> A -> A) v0,
      Sigma.mem sigma i = Some (abs v0) ->
      step tid sigma (GhostUpdate i up) (Sigma.set_mem sigma i (abs (up tid v0))) tt
  | StepBeginRead : forall a v,
      Sigma.disk sigma a = Some (v, NoReader) ->
      step tid sigma (BeginRead a)
           (Sigma.upd_disk sigma (fun d => upd d a (v, Pending))) tt
  | StepWaitForRead : forall a v,
      Sigma.disk sigma a = Some (v, Pending) ->
      step tid sigma (WaitForRead a)
           (Sigma.upd_disk sigma (fun d => upd d a (v, NoReader))) v
  | StepWrite : forall a v0 v,
      Sigma.disk sigma a = Some (v0, NoReader) ->
      step tid sigma (Write a v)
           (Sigma.upd_disk sigma (fun d => upd d a (v, NoReader))) tt
  | StepHash : forall sz buf,
      let h := hash_fwd buf in
      hash_safe (Sigma.hm sigma) h buf ->
      step tid sigma (@Hash sz buf)
           (Sigma.upd_hm sigma buf) h.

  Inductive fail_step (sigma: Sigma) :
    forall T, cprog T -> Prop :=
  | FailStepGetOob : forall A (i: ident),
      Sigma.mem sigma i = None ->
      fail_step sigma (Get A i)
  | FailStepGetTy : forall A A' (i: ident) (v0: A'),
      Sigma.mem sigma i = Some (val v0) ->
      A <> A' ->
      fail_step sigma (Get A i)
  | FailStepAssgnOob : forall A i (v':A),
      Sigma.mem sigma i = None ->
      fail_step sigma (Assgn i v')
  | FailStepAssgnTy : forall A A' i (v0: A') (v':A),
      Sigma.mem sigma i = Some (val v0) ->
      A <> A' ->
      fail_step sigma (Assgn i v')
  | FailStepBeginReadOob : forall a,
      Sigma.disk sigma a = None ->
      fail_step sigma (BeginRead a)
  | FailStepBeginReadPending : forall a v,
      Sigma.disk sigma a = Some (v, Pending) ->
      fail_step sigma (BeginRead a)
  | FailStepWaitForReadOob : forall a,
      Sigma.disk sigma a = None ->
      fail_step sigma (WaitForRead a)
  | FailStepWaitForReadPending : forall a v,
      Sigma.disk sigma a = Some (v, NoReader) ->
      fail_step sigma (WaitForRead a)
  | FailStepWriteOob : forall a v,
      Sigma.disk sigma a = None ->
      fail_step sigma (Write a v)
  | FailStepWritePending : forall a v0 v,
      Sigma.disk sigma a = Some (v0, Pending) ->
      fail_step sigma (Write a v).

  Inductive outcome T :=
  | Finished (sigma:Sigma * Sigma) (r:T)
  | Error.

  Arguments Error {T}.

  Definition Protocol := TID -> Sigma -> Sigma -> Prop.
  Variable Guarantee : Protocol.

  Definition Rely : Protocol :=
    fun tid =>
      clos_refl_trans _ (fun sigma sigma' =>
                           exists tid', tid <> tid' /\
                                   Guarantee tid sigma sigma').

  Inductive exec (tid:TID) : forall T, (Sigma * Sigma) -> cprog T -> outcome T -> Prop :=
  | ExecRet : forall T (v:T) st, exec tid st (Ret v) (Finished st v)
  | ExecStep : forall T (p: cprog T) sigma_i sigma sigma' v,
      step tid sigma p sigma' v ->
      exec tid (sigma_i, sigma) p (Finished (sigma_i, sigma') v)
  | ExecFail : forall T (p: cprog T) sigma_i sigma,
      fail_step sigma p ->
      exec tid (sigma_i, sigma) p Error
  | ExecBindFinish : forall T T' (p: cprog T') (p': T' -> cprog T)
                       st st' v out,
      exec tid st p (Finished st' v) ->
      exec tid st' (p' v) out ->
      exec tid st (Bind p p') out
  | ExecBindFail : forall T T' (p: cprog T') (p': T' -> cprog T) st,
      exec tid st p Error ->
      exec tid st (Bind p p') Error
  | ExecYield : forall sigma_i sigma sigma',
      Guarantee tid sigma_i sigma ->
      Rely tid sigma sigma' ->
      exec tid (sigma_i, sigma) Yield (Finished (sigma', sigma') tt)
  | ExecYieldFail : forall sigma_i sigma,
      ~Guarantee tid sigma_i sigma ->
      exec tid (sigma_i, sigma) Yield Error.

  Definition SpecDouble T :=
    (Sigma * Sigma) -> (Sigma * Sigma -> T -> Prop) -> Prop.

  Definition cprog_ok tid T (pre: SpecDouble T) (p: cprog T) :=
    forall st donecond out, pre st donecond ->
                       exec tid st p out ->
                       match out with
                       | Finished st' v =>
                         donecond st' v
                       | Error => False
                       end.

End CCL.

Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2))
                                 (at level 60, right associativity).
(* BUG: this should work but using it to do a destructuring pattern triggers an
exception exception at interp/topcontr.ml line 200 *)
Notation "'do' x .. y <- p1 ; p2" := (Bind p1 (fun x => .. (fun y => p2) ..))
                                      (at level 60, right associativity,
                                       x binder, y binder, only parsing).

(* Use to give spec hints to the automation: the pattern should be

Hint Extern 0 {{ Method _ _; _ }} => apply Method_ok.

The number of underscores given in Method needs to be correct. *)
Notation "{{ p ; '_' }}" := (cprog_ok _ _ _ (Bind p _)) (only parsing).

Arguments Error {T}.
Arguments Ret {T} v.

Module CCLTactics.
  Import Automation.
  Ltac inv_bind :=
    match goal with
    | [ H: exec _ _ _ (Bind _ _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ _ _ _ |- _ ] =>
            solve [ inversion H ]
          | [ H: fail_step _ _ |- _ ] =>
            solve [ inversion H ]
          end;
      clear H
    end.

  Ltac inv_ret :=
    match goal with
    | [ H: exec _ _ _ (Ret _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ (Ret _) _ _ |- _ ] =>
            solve [ inversion H ]
          | [ H: fail_step _ (Ret _) |- _ ] =>
            solve [ inversion H ]
          end;
      clear H
    end.

  Local Ltac inv_cleanup H :=
    inversion H; subst; repeat inj_pair2.

  Ltac inv_exec' H :=
    inv_cleanup H;
    try match goal with
        | [ H: step _ _ _ _ _ |- _ ] => inv_cleanup H
        | [ H: fail_step _ _ |- _ ] => inv_cleanup H
        end; try congruence.

  Ltac inv_exec :=
    match goal with
    | [ H: exec _ _ _ _ (Finished _ _) |- _ ] => inv_exec' H
    | [ H: exec _ _ _ _ Error |- _ ] => inv_exec' H
    end.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ _ |- _ ] => inversion H; subst
    end.

  Ltac inv_fail_step :=
    match goal with
    | [ H: fail_step _ _ |- _ ] => inversion H; subst
    end.

End CCLTactics.

(* Local Variables: *)
(* compval-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)