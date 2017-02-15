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

Inductive LockState :=
| Free
| ReadLock
| WriteLock.

Inductive ReadPermission : LockState -> Prop :=
| ReadPermissionR : ReadPermission ReadLock
| ReadPermissionW : ReadPermission WriteLock.

Lemma read_perm_r_eq : forall l,
    l = ReadLock ->
    ReadPermission l.
Proof.
  intros; subst; constructor.
Qed.

Lemma read_perm_w_eq : forall l,
    l = WriteLock ->
    ReadPermission l.
Proof.
  intros; subst; constructor.
Qed.

Hint Resolve read_perm_r_eq read_perm_w_eq.

Definition CanRead (l:LockState) : {ReadPermission l} + {l = Free}.
Proof.
  destruct l; eauto.
Defined.

Definition CanWrite (l:LockState) : {l = WriteLock} + {l <> WriteLock}.
Proof.
  destruct l; left + right; congruence.
Defined.

Definition lock_dec (l l':LockState) : {l=l'}+{l<>l'}.
Proof.
  decide equality.
Defined.

(* The states a program steps through. *)
Inductive Sigma St :=
| state (d:DISK) (m:Mem St) (s:Abstraction St) (hm:hashmap) (l:LockState).

Arguments state {St} d m s hm l.

Module Sigma.
  Definition disk St (sigma:Sigma St) :=
    let (d, _, _, _, _) := sigma in d.
  Definition mem St (sigma:Sigma St) :=
    let (_, m, _, _, _) := sigma in m.
  Definition s St (sigma:Sigma St) :=
    let (_, _, s, _, _) := sigma in s.
  Definition hm St (sigma:Sigma St) :=
    let (_, _, _, hm, _) := sigma in hm.
  Definition l St (sigma:Sigma St) :=
    let (_, _, _, _, l) := sigma in l.

  Definition set_mem St (sigma:Sigma St) (m:Mem St) :=
    let (d, _, s, hm, l) := sigma in state d m s hm l.
  Definition upd_disk St (sigma:Sigma St) (d':DISK -> DISK) :=
    let (d, m, s, hm, l) := sigma in state (d' d) m s hm l.
  Definition upd_s St (sigma:Sigma St) (s':Abstraction St -> Abstraction St) :=
    let (d, m, s, hm, l) := sigma in state d m (s' s) hm l.
  Definition upd_hm St (sigma:Sigma St) sz (buf: word sz) :=
    let (d, m, s, hm, l) := sigma in state d m s (upd_hashmap' hm (hash_fwd buf) buf) l.
  Definition set_l St (sigma:Sigma St) l :=
    let (d, m, s, hm, _) := sigma in state d m s hm l.
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
  | SetLock (l:LockState) : cprog unit
  | Ret T (v:T) : cprog T
  | Bind T T' (p: cprog T') (p': T' -> cprog T) : cprog T.

  Definition Protocol := TID -> Sigma St -> Sigma St -> Prop.
  Variable Guarantee : Protocol.

  Definition Rely : Protocol :=
    fun tid =>
      clos_refl_trans _ (fun sigma sigma' =>
                           exists tid', tid <> tid' /\
                                   Guarantee tid sigma sigma').

  Inductive StepOutcome T :=
  | StepTo (sigma':Sigma St) (v:T)
  | Fails
  | NonDet.

  Arguments Fails {T}.
  Arguments NonDet {T}.

  Definition step_dec tid (sigma: Sigma St) T (p: cprog T) : StepOutcome T :=
    match p with
    | Get => if CanRead (Sigma.l sigma) then StepTo sigma (Sigma.mem sigma)
            else Fails
    | Assgn m' => if CanWrite (Sigma.l sigma) then StepTo (Sigma.set_mem sigma m') tt
                  else Fails
    | GhostUpdate up => if CanWrite (Sigma.l sigma) then StepTo (Sigma.upd_s sigma (up tid)) tt
                       else Fails
    | BeginRead a => if CanWrite (Sigma.l sigma) then
                      match Sigma.disk sigma a with
                      | Some (v, NoReader) =>
                        StepTo (Sigma.upd_disk sigma (fun d => upd d a (v, Pending))) tt
                      | _ => Fails
                      end
                    else Fails
    | WaitForRead a => if CanWrite (Sigma.l sigma) then
                        match Sigma.disk sigma a with
                        | Some (v, Pending) =>
                          StepTo (Sigma.upd_disk sigma (fun d => upd d a (v, NoReader))) v
                        | _ => Fails
                        end
                      else Fails
    | Write a v => if CanWrite (Sigma.l sigma) then
                    match Sigma.disk sigma a with
                    | Some (_, NoReader) =>
                      StepTo (Sigma.upd_disk sigma (fun d => upd d a (v, NoReader))) tt
                    | _ => Fails
                    end
                  else Fails
    | SetLock l' => if lock_dec (Sigma.l sigma) ReadLock then
                     if lock_dec l' Free then
                       StepTo (Sigma.set_l sigma Free) tt
                     else Fails
                   else NonDet
    | Ret v => StepTo sigma v
    | _ => NonDet
    end.

  Inductive outcome T :=
  | Finished (sigma_i sigma:Sigma St) (r:T)
  | Error.

  Arguments Error {T}.

  Inductive exec (tid:TID) : forall T, (Sigma St * Sigma St) -> cprog T -> outcome T -> Prop :=
  | ExecStepDec : forall T (p: cprog T) sigma_i sigma sigma' v,
      step_dec tid sigma p = StepTo sigma' v ->
      exec tid (sigma_i, sigma) p (Finished sigma_i sigma' v)
  | ExecStepDecFail : forall T (p: cprog T) sigma_i sigma,
      step_dec tid sigma p = Fails ->
      exec tid (sigma_i, sigma) p Error
  | ExecHash : forall sigma_i sigma sz buf,
      let h := hash_fwd buf in
      hash_safe (Sigma.hm sigma) h buf ->
      exec tid (sigma_i, sigma) (@Hash sz buf) (Finished sigma_i
                                                     (Sigma.upd_hm sigma buf) h)
  | ExecBindFinish : forall T T' (p: cprog T') (p': T' -> cprog T)
                       sigma_i sigma sigma_i' sigma' v out,
      exec tid (sigma_i, sigma) p (Finished sigma_i' sigma' v) ->
      exec tid (sigma_i', sigma') (p' v) out ->
      exec tid (sigma_i, sigma) (Bind p p') out
  | ExecBindFail : forall T T' (p: cprog T') (p': T' -> cprog T) sigma_i sigma,
      exec tid (sigma_i, sigma) p Error ->
      exec tid (sigma_i, sigma) (Bind p p') Error
  | ExecLock : forall sigma_i sigma l' sigma',
      Sigma.l sigma = Free ->
      Rely tid sigma sigma' ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ->
      let sigma' := Sigma.set_l sigma' l' in
      exec tid (sigma_i, sigma) (SetLock l') (Finished sigma' sigma' tt)
  | ExecRelease : forall sigma_i sigma,
      Sigma.l sigma = WriteLock ->
      Guarantee tid sigma_i sigma ->
      let sigma' := Sigma.set_l sigma Free in
      exec tid (sigma_i, sigma) (SetLock Free) (Finished sigma' sigma' tt)
  | ExecReleaseFail : forall sigma_i sigma,
      Sigma.l sigma = WriteLock ->
      ~Guarantee tid sigma_i sigma ->
      exec tid (sigma_i, sigma) (SetLock Free) Error.

  Theorem ExecRet : forall tid T (v:T) sigma_i sigma,
      exec tid (sigma_i, sigma) (Ret v) (Finished sigma_i sigma v).
  Proof.
    intros.
    eapply ExecStepDec.
    auto.
  Qed.

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

  Ltac inv_step :=
    match goal with
    | [ H: step_dec _ _ _ = _ |- _ ] =>
      simpl in H; inversion H; subst; clear H
    end.

  Ltac inv_bind :=
    match goal with
    | [ H: exec _ _ _ (Bind _ _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try solve [ inv_step ];
      clear H
    end.

  Ltac inv_ret :=
    match goal with
    | [ H: exec _ _ _ (Ret _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step_dec _ _ (Ret _) = _ |- _ ] =>
            simpl in H; inversion H; subst; clear H
          end;
      clear H
    end.

  Local Ltac inv_cleanup H :=
    inversion H; subst; repeat inj_pair2.

  Ltac inv_exec' H :=
    inv_cleanup H;
    try match goal with
        | [ H: step_dec _ _ _ = _ |- _ ] =>
          simpl in H;
          repeat match goal with
                 | [ H: context[match ?d with _ => _ end] |- _ ] =>
                   destruct d; try congruence;
                   let n := numgoals in guard n <= 1
                 end
        end;
    repeat match goal with
           | [ H: StepTo _ _ = StepTo _ _ |- _ ] =>
             inversion H; subst; clear H
           end;
    try congruence.

  Ltac inv_exec :=
    match goal with
    | [ H: exec _ _ _ _ (Finished _ _ _) |- _ ] => inv_exec' H
    | [ H: exec _ _ _ _ Error |- _ ] => inv_exec' H
    end.

End CCLTactics.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)