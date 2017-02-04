Require Import AsyncDisk.
Require Import Word.
Require Import Mem Pred.
Require Import PeanoNat.
Require Import Hashmap.
Require Import Relation_Operators.

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
  Definition st St (s:Sigma St) :=
    let (_, _, s, _) := s in s.
  Definition hm St (s:Sigma St) :=
    let (_, _, _, hm) := s in hm.

  Definition set_mem St (s:Sigma St) (m:Mem St) :=
    let (d, _, s, hm) := s in state d m s hm.
  Definition upd_disk St (s:Sigma St) (d':DISK -> DISK) :=
    let (d, m, s, hm) := s in state (d' d) m s hm.
  Definition upd_st St (s:Sigma St) (s':Abstraction St -> Abstraction St) :=
    let (d, m, s, hm) := s in state d m (s' s) hm.
  Definition upd_hm St (s:Sigma St) (hm':hashmap -> hashmap) :=
    let (d, m, s, hm) := s in state d m s (hm' hm).
End Sigma.

Section CCL.

  (** Type parameters for state. *)
  Variable St:StateTypes.

  Definition TID := nat.
  Opaque TID.

  Inductive cprog : Type -> Type :=
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
      step tid sigma (GhostUpdate up) (Sigma.upd_st sigma (up tid)) tt
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
           (Sigma.upd_hm sigma (fun hm => upd_hashmap' hm h buf)) h.

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

  Inductive outcome A :=
  | Finished (sigma_i sigma:Sigma St) (r:A)
  | Error.

  Arguments Error {A}.

  Variable Guarantee : TID -> Sigma St -> Sigma St -> Prop.

  Definition Rely tid :=
    clos_refl_trans _ (fun sigma sigma' =>
                         exists tid', tid <> tid' /\
                                 Guarantee tid sigma sigma').

  Inductive exec (tid:TID) : forall T, (Sigma St * Sigma St) -> cprog T -> outcome T -> Prop :=
  | ExecRet : forall T (v:T) sigma_i sigma, exec tid (sigma_i, sigma) (Ret v) (Finished sigma_i sigma v)
  | ExecStep : forall T (p: cprog T) sigma_i sigma sigma' v,
      step tid sigma p sigma' v ->
      exec tid (sigma_i, sigma) p (Finished sigma_i sigma v)
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

  Record Spec A T :=
    { precondition : A -> (Sigma St * Sigma St) -> Prop;
      postcondition : A -> (Sigma St * Sigma St) ->
                      (Sigma St * Sigma St) ->
                      T -> Prop }.

  Definition ReflectDouble tid A T T' (spec: Spec A T')
             (rx: T' -> cprog T) : SpecDouble T :=
    fun st donecond =>
      exists a, precondition spec a st /\
           forall r, cprog_ok tid (fun st' donecond_rx =>
                                postcondition spec a st st' r /\
                                donecond_rx = donecond) (rx r).

  Definition cprog_triple tid A T' (spec: Spec A T') (p: cprog T') :=
    forall T (rx: _ -> cprog T),
      cprog_ok tid (ReflectDouble tid spec rx) (Bind p rx).

End CCL.

Arguments Ret {St T} v.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)