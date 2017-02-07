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

(* Define the structure of the memory and ghost state. *)
Record StateTypes:Type :=
  defState {
      Mem : Type;
      Abstraction : Type; }.

(* The states a program steps through. *)
Inductive Sigma St :=
| state (d:DISK) (m:Mem St) (s:Abstraction St) (hm:hashmap).

Arguments state {St} d m s hm.

Module Sigma.
  Definition disk St (s:Sigma St) :=
    let (d, _, _, _) := s in d.
  Definition mem St (s:Sigma St) :=
    let (_, m, _, _) := s in m.
  Definition s St (s:Sigma St) :=
    let (_, _, s, _) := s in s.
  Definition hm St (s:Sigma St) :=
    let (_, _, _, hm) := s in hm.

  Definition set_mem St (s:Sigma St) (m:Mem St) :=
    let (d, _, s, hm) := s in state d m s hm.
  Definition upd_disk St (s:Sigma St) (d':DISK -> DISK) :=
    let (d, m, s, hm) := s in state (d' d) m s hm.
  Definition upd_s St (s:Sigma St) (s':Abstraction St -> Abstraction St) :=
    let (d, m, s, hm) := s in state d m (s' s) hm.
  Definition upd_hm St (s:Sigma St) sz (buf: word sz) :=
    let (d, m, s, hm) := s in state d m s (upd_hashmap' hm (hash_fwd buf) buf).
End Sigma.

Section CCL.

  (** Type parameters for state. *)
  Context {St:StateTypes}.

  Definition TID := nat.
  Opaque TID.

  CoInductive cprog : Type -> Type :=
  | Get : cprog (Mem St)
  | Assgn (m:Mem St) : cprog unit
  | GhostUpdate (update: TID -> Abstraction St -> Abstraction St) : cprog unit
  | BeginRead (a:addr) : cprog unit
  | WaitForRead (a:addr) : cprog valu
  | Write (a:addr) (v: valu) : cprog unit
  | Hash sz (buf: word sz) : cprog (word hashlen)
  | Yield : cprog unit
  | Ret T (v:T) : cprog T
  | Bind T T' (p: cprog T') (p': T' -> cprog T) : cprog T.

  Inductive step (tid:TID) (sigma: Sigma St) :
    forall T, cprog T -> Sigma St -> T -> Prop :=
  | StepGet :
      step tid sigma Get sigma (Sigma.mem sigma)
  | StepAssgn : forall m',
      step tid sigma (Assgn m') (Sigma.set_mem sigma m') tt
  | StepGhostUpdate : forall up,
      step tid sigma (GhostUpdate up) (Sigma.upd_s sigma (up tid)) tt
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

  Inductive fail_step (sigma: Sigma St) :
    forall T, cprog T -> Prop :=
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
  | Finished (sigma_i sigma:Sigma St) (r:T)
  | Error.

  Arguments Error {T}.

  Definition Protocol := TID -> Sigma St -> Sigma St -> Prop.
  Variable Guarantee : Protocol.

  Definition Rely : Protocol :=
    fun tid =>
      clos_refl_trans _ (fun sigma sigma' =>
                           exists tid', tid <> tid' /\
                                   Guarantee tid sigma sigma').

  Inductive exec (tid:TID) : forall T, (Sigma St * Sigma St) -> cprog T -> outcome T -> Prop :=
  | ExecRet : forall T (v:T) sigma_i sigma, exec tid (sigma_i, sigma) (Ret v) (Finished sigma_i sigma v)
  | ExecStep : forall T (p: cprog T) sigma_i sigma sigma' v,
      step tid sigma p sigma' v ->
      exec tid (sigma_i, sigma) p (Finished sigma_i sigma' v)
  | ExecFail : forall T (p: cprog T) sigma_i sigma,
      fail_step sigma p ->
      exec tid (sigma_i, sigma) p Error
  | ExecBindFinish : forall T T' (p: cprog T') (p': T' -> cprog T)
                       sigma_i sigma sigma_i' sigma' v out,
      exec tid (sigma_i, sigma) p (Finished sigma_i' sigma' v) ->
      exec tid (sigma_i', sigma') (p' v) out ->
      exec tid (sigma_i, sigma) (Bind p p') out
  | ExecBindFail : forall T T' (p: cprog T') (p': T' -> cprog T) sigma_i sigma,
      exec tid (sigma_i, sigma) p Error ->
      exec tid (sigma_i, sigma) (Bind p p') Error
  | ExecYield : forall sigma_i sigma sigma',
      Guarantee tid sigma_i sigma ->
      Rely tid sigma sigma' ->
      exec tid (sigma_i, sigma) Yield (Finished sigma' sigma' tt)
  | ExecYieldFail : forall sigma_i sigma,
      ~Guarantee tid sigma_i sigma ->
      exec tid (sigma_i, sigma) Yield Error.

  Definition SpecDouble T :=
    (Sigma St * Sigma St) -> (Sigma St * Sigma St -> T -> Prop) -> Prop.

  Definition cprog_ok tid T (pre: SpecDouble T) (p: cprog T) :=
    forall st donecond out, pre st donecond ->
                       exec tid st p out ->
                       match out with
                       | Finished sigma_i' sigma' v =>
                         donecond (sigma_i', sigma') v
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

Arguments Error {St T}.
Arguments Ret {St T} v.
Arguments Protocol St : clear implicits.

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
    | [ H: exec _ _ _ _ (Finished _ _ _) |- _ ] => inv_exec' H
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
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)