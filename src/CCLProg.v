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

Inductive Var :=
(* materialized memory variables *)
| val : forall T, T -> Var
(* abstraction (ghost) variables *)
| abs : forall T, T -> Var
(* ghost variables that are memories

 We separate these into their own constructor to avoid instantiating the T in
 the bas constructor with a memory, which causes universe consistency issues
 with also using @mem _ _ Var. *)
| absMem : forall A AEQ V, @mem A AEQ V -> Var.

Definition ident := nat.
Opaque ident.

Notation heap := (@mem ident Nat.eq_dec Var).
Notation heappred := (@pred ident Nat.eq_dec Var).

(* The states a program steps through. *)
Inductive Sigma :=
| state (d:DISK) (m:heap) (hm:hashmap) (l:LockState).

Module Sigma.
  Definition disk (sigma:Sigma) :=
    let (d, _, _, _) := sigma in d.
  Definition mem (sigma:Sigma) : heap :=
    let (_, m, _, _) := sigma in m.
  Definition hm (sigma:Sigma) :=
    let (_, _, hm, _) := sigma in hm.
  Definition l (sigma:Sigma) :=
    let (_, _, _, l) := sigma in l.

  Definition set_mem (sigma:Sigma) (m:heap) :=
    let (d, _, hm, l) := sigma in state d m hm l.
  Definition upd_disk (sigma:Sigma) (d':DISK -> DISK) :=
    let (d, m, hm, l) := sigma in state (d' d) m hm l.
  Definition upd_hm (sigma:Sigma) sz (buf: word sz) :=
    let (d, m, hm, l) := sigma in state d m (upd_hashmap' hm (hash_fwd buf) buf) l.
  Definition set_l (sigma:Sigma) l :=
    let (d, m, hm, _) := sigma in state d m hm l.
End Sigma.

Section CCL.

  Definition TID := nat.
  Opaque TID.

  CoInductive cprog : Type -> Type :=
  | Alloc A (v:A) : cprog ident
  | Get A (i:ident) : cprog A
  | Assgn A (i:ident) (v:A) : cprog unit
  | GhostUpdate A (i:ident) (update: TID -> A -> A) : cprog unit
  | GhostUpdateMem A AEQ V (i:ident) (update: TID -> @mem A AEQ V -> @mem A AEQ V) : cprog unit
  | BeginRead (a:addr) : cprog unit
  | WaitForRead (a:addr) : cprog valu
  | Write (a:addr) (v: valu) : cprog unit
  | Hash sz (buf: word sz) : cprog (word hashlen)
  (* SetLock returns the new state to support trying to upgrade read -> write *)
  | SetLock (l:LockState) (l':LockState) : cprog LockState
  | Ret T (v:T) : cprog T
  | Bind T T' (p: cprog T') (p': T' -> cprog T) : cprog T.

  Definition Protocol := TID -> Sigma -> Sigma -> Prop.
  Variable Guarantee : Protocol.

  Definition Rely : Protocol :=
    fun tid =>
      clos_refl_trans _ (fun sigma sigma' =>
                           exists tid', tid <> tid' /\
                                   Guarantee tid sigma sigma').

  Theorem Rely_trans : forall tid sigma sigma' sigma'',
      Rely tid sigma sigma' ->
      Rely tid sigma' sigma'' ->
      Rely tid sigma sigma''.
  Proof.
    unfold Rely; intros.
    eapply Relation_Operators.rt_trans; eauto.
  Qed.

  Inductive StepOutcome T :=
  | StepTo (sigma':Sigma) (v:T)
  | Fails
  | NonDet.

  Arguments Fails {T}.
  Arguments NonDet {T}.

  Definition step_dec (sigma: Sigma) T (p: cprog T) : StepOutcome T :=
    match p with
    | Alloc v => NonDet
    | Get A i => if CanRead (Sigma.l sigma) then
                  match Sigma.mem sigma i with
                  | Some (val _) => NonDet (* still need to check type *)
                  | _ => Fails
                  end
              else Fails
    | Assgn i v => if CanWrite (Sigma.l sigma) then
                    match Sigma.mem sigma i with
                    | Some (val _) => NonDet (* still need to check type *)
                    | _ => Fails
                    end
                  else Fails
    | GhostUpdate i up => if CanWrite (Sigma.l sigma) then
                           match Sigma.mem sigma i with
                           | Some (abs _) => NonDet (* still need to check type *)
                           | _ => Fails
                           end
                         else Fails
    | GhostUpdateMem i up => if CanWrite (Sigma.l sigma) then
                           match Sigma.mem sigma i with
                           | Some (absMem _) => NonDet (* still need to check type *)
                           | _ => Fails
                           end
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
    | SetLock l l' => if lock_dec (Sigma.l sigma) l then
                       if lock_dec (Sigma.l sigma) ReadLock then
                         if lock_dec l' Free then
                           StepTo (Sigma.set_l sigma Free) Free
                         else if lock_dec l' ReadLock
                              then Fails
                              else NonDet
                       else NonDet
                     else Fails
    | Ret v => StepTo sigma v
    | _ => NonDet
    end.

  Inductive outcome T :=
  | Finished (sigma_i sigma:Sigma) (r:T)
  | Error.

  Arguments Error {T}.

  Inductive exec (tid:TID) : forall T, (Sigma * Sigma) -> cprog T -> outcome T -> Prop :=
  | ExecStepDec : forall T (p: cprog T) sigma_i sigma sigma' v,
      step_dec sigma p = StepTo sigma' v ->
      exec tid (sigma_i, sigma) p (Finished sigma_i sigma' v)
  | ExecStepDecFail : forall T (p: cprog T) sigma_i sigma,
      step_dec sigma p = Fails ->
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
  | ExecWriteLock : forall sigma_i sigma l' sigma',
      Sigma.l sigma = Free ->
      Rely tid sigma sigma' ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ->
      let sigma' := Sigma.set_l sigma' l' in
      exec tid (sigma_i, sigma) (SetLock Free l') (Finished sigma' sigma' l')
  | ExecUpgradeLockSuccess : forall sigma_i sigma,
      Sigma.l sigma = ReadLock ->
      let sigma' := Sigma.set_l sigma WriteLock in
      exec tid (sigma_i, sigma) (SetLock ReadLock WriteLock)
           (Finished sigma_i sigma' WriteLock)
  | ExecUpgradeLockFail : forall sigma_i sigma,
      Sigma.l sigma = ReadLock ->
      exec tid (sigma_i, sigma) (SetLock ReadLock WriteLock)
           (Finished sigma_i sigma ReadLock)
  | ExecAlloc : forall sigma_i sigma A (v:A) i,
      Sigma.mem sigma i = None ->
      let sigma' := Sigma.set_mem sigma (upd (Sigma.mem sigma) i (val v)) in
      exec tid (sigma_i, sigma) (Alloc v)
           (Finished sigma_i sigma' i)
  | ExecGet : forall sigma_i sigma A i (v:A),
      Sigma.mem sigma i = Some (val v) ->
      exec tid (sigma_i, sigma) (Get A i)
           (Finished sigma_i sigma v)
  | ExecGetFail : forall sigma_i sigma A A' i (v:A'),
      A <> A' ->
      Sigma.mem sigma i = Some (val v) ->
      exec tid (sigma_i, sigma) (Get A i) Error
  | ExecAssgn : forall sigma_i sigma A i (v:A) (v0:A),
      Sigma.mem sigma i = Some (val v0) ->
      let sigma' := Sigma.set_mem sigma (upd (Sigma.mem sigma) i (val v)) in
      exec tid (sigma_i, sigma) (Assgn i v)
           (Finished sigma_i sigma' tt)
  | ExecAssgnFail : forall sigma_i sigma A i (v:A) A' (v0:A'),
      A <> A' ->
      Sigma.mem sigma i = Some (val v0) ->
      exec tid (sigma_i, sigma) (Assgn i v) Error
  (* ghost updates don't fail (no reason to, at least without some consistency
  proof) *)
  | ExecGhostUpdate : forall sigma_i sigma A i up (v0:A),
      Sigma.mem sigma i = Some (abs v0) ->
      let sigma' := Sigma.set_mem sigma (upd (Sigma.mem sigma) i (abs (up tid v0))) in
      exec tid (sigma_i, sigma) (GhostUpdate i up)
           (Finished sigma_i sigma' tt)
  | ExecGhostUpdateMem : forall sigma_i sigma A AEQ V i up (m0:@mem A AEQ V),
      Sigma.mem sigma i = Some (absMem m0) ->
      let sigma' := Sigma.set_mem sigma (upd (Sigma.mem sigma) i (absMem (up tid m0))) in
      exec tid (sigma_i, sigma) (GhostUpdateMem i up)
           (Finished sigma_i sigma' tt)
  | ExecRelease : forall sigma_i sigma,
      Sigma.l sigma = WriteLock ->
      Guarantee tid sigma_i sigma ->
      let sigma' := Sigma.set_l sigma Free in
      exec tid (sigma_i, sigma) (SetLock WriteLock Free) (Finished sigma' sigma' Free)
  | ExecReleaseFail : forall sigma_i sigma,
      Sigma.l sigma = WriteLock ->
      ~Guarantee tid sigma_i sigma ->
      exec tid (sigma_i, sigma) (SetLock WriteLock Free) Error.

  Theorem ExecRet : forall tid T (v:T) sigma_i sigma,
      exec tid (sigma_i, sigma) (Ret v) (Finished sigma_i sigma v).
  Proof.
    intros.
    eapply ExecStepDec.
    auto.
  Qed.

  Definition SpecDouble T :=
    (Sigma* Sigma) -> (Sigma * Sigma -> T -> Prop) -> Prop.

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

Arguments Error {T}.
Arguments Ret {T} v.

Module CCLTactics.
  Import Automation.

  Ltac inv_step :=
    match goal with
    | [ H: step_dec _ _ = _ |- _ ] =>
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
          | [ H: step_dec _ (Ret _) = _ |- _ ] =>
            simpl in H; inversion H; subst; clear H
          end;
      clear H
    end.

  Local Ltac inv_cleanup H :=
    inversion H; subst; repeat inj_pair2.

  Ltac inv_exec' H :=
    inv_cleanup H;
    try match goal with
        | [ H: step_dec _ _ = _ |- _ ] =>
          simpl in H;
          repeat match goal with
                 | [ H: context[match ?d with _ => _ end] |- _ ] =>
                   let H := fresh in
                   destruct d eqn:H; subst; try congruence;
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