Require Import AsyncDisk.
Require Import Word.
Require Import Mem Pred.
Require Import PeanoNat.
Require Import Hashmap.
Require Import Relation_Operators.
Require Import RelationClasses.
Require Automation.

Global Set Implicit Arguments.

Inductive ReadState := Pending | NoReader.
Notation DISK := (@mem addr addr_eq_dec (valu * ReadState)).

Inductive LockState :=
| Free
| WriteLock.

Definition CanWrite (l:LockState) : {l = WriteLock} + {l <> WriteLock}.
Proof.
  destruct l; left + right; congruence.
Defined.

Definition lock_dec (l l':LockState) : {l=l'}+{l<>l'}.
Proof.
  decide equality.
Defined.

Polymorphic Inductive Var :=
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

  Inductive read_transaction : Type -> Type :=
  | RDone : read_transaction unit
  | RCons : forall T, ident -> forall T', read_transaction T' -> read_transaction (T*T').

  Inductive heapupd : Type :=
  | NewVal : forall T, ident -> T -> heapupd
  | AbsUpd : forall T, ident -> (TID -> T -> T) -> heapupd
  | AbsMemUpd : forall A AEQ V,
      ident -> (TID -> @mem A AEQ V -> @mem A AEQ V) ->
      heapupd.

  Inductive write_transaction : Type :=
  | WDone : write_transaction
  | WCons : heapupd -> write_transaction -> write_transaction.

  CoInductive cprog : Type -> Type :=
  | Alloc A (v:A) : cprog ident
  | ReadTxn A (tx:read_transaction A) : cprog A
  | AssgnTxn (tx:write_transaction) : cprog unit
  | BeginRead (a:addr) : cprog unit
  | WaitForRead (a:addr) : cprog valu
  | Write (a:addr) (v: valu) : cprog unit
  | Hash sz (buf: word sz) : cprog (word hashlen)
  | SetLock (l:LockState) (l':LockState) : cprog unit
  | Ret T (v:T) : cprog T
  | Bind T T' (p: cprog T') (p': T' -> cprog T) : cprog T.

  Definition Protocol := TID -> Sigma -> Sigma -> Prop.
  Variable Guarantee : Protocol.

  Definition Rely : Protocol :=
    fun tid =>
      clos_refl_trans _ (fun sigma sigma' =>
                           exists tid', tid <> tid' /\
                                   Guarantee tid sigma sigma').

  Global Instance Rely_trans tid : Transitive (Rely tid).
  Proof.
    unfold Rely, Transitive; hnf; intros.
    eapply Relation_Operators.rt_trans; eauto.
  Qed.

  Inductive StepOutcome T :=
  | StepTo (sigma':Sigma) (v:T)
  | Fails
  | NonDet.

  Arguments Fails {T}.
  Arguments NonDet {T}.

  Inductive read_set_vals (h:heap) : forall T, read_transaction T -> list Var -> Prop :=
  | ReadSetValDone :
      read_set_vals h RDone nil
  | ReadSetValCons : forall A A' i (v:A') A'' (txn:read_transaction A'') vals,
      h i = Some (val v) ->
      read_set_vals h txn vals ->
      read_set_vals h (RCons A i txn) (val v::vals).

  Hint Constructors read_set_vals.

  Ltac inv_read_set_vals :=
    match goal with
    | [ H: read_set_vals _ _ _ |- _ ] =>
      inversion H; subst; clear H; repeat Automation.inj_pair2
    end.

  Ltac t := try solve [ left; repeat deex; eauto ];
            try (right; repeat deex; intros; inv_read_set_vals; congruence).

  Fixpoint rtxn_in_domain_dec A (txn:read_transaction A) (h:heap) {struct txn} :
    {exists vals, read_set_vals h txn vals} + {forall vals, ~read_set_vals h txn vals}.
  Proof.
    unfold not in *.
    destruct txn.
    - left; eauto.
    - destruct (rtxn_in_domain_dec T' txn h).
      destruct (h i) eqn:H; t.
      destruct v; t.
      right; intros.
      inv_read_set_vals; eauto.
  Defined.

  Inductive write_set_allocd (h:heap) : write_transaction -> Prop :=
  | WriteSetValDone : write_set_allocd h WDone
  | WriteSetValCons : forall A A' i (v:A') (v':A) (txn: write_transaction),
      h i = Some (val v) ->
      write_set_allocd h txn ->
      write_set_allocd h (WCons (NewVal i v') txn)
  | WriteSetAbsCons : forall A A' i (v:A') (f: TID -> A -> A)
                        (txn: write_transaction),
      h i = Some (abs v) ->
      write_set_allocd h txn ->
      write_set_allocd h (WCons (AbsUpd i f) txn)
  | WriteSetAbsMemCons : forall A AEQ V A' i (v:A') (f: TID -> @mem A AEQ V -> @mem A AEQ V)
                        (txn: write_transaction),
      h i = Some (abs v) ->
      write_set_allocd h txn ->
      write_set_allocd h (WCons (AbsUpd i f) txn).

  Hint Constructors write_set_allocd.

  Ltac inv_write_set_allocd :=
    match goal with
    | [ H: write_set_allocd _ _ |- _ ] =>
      inversion H; subst; clear H; repeat Automation.inj_pair2
    end.

  Ltac t' := try solve [ left; repeat deex; eauto ];
             try (right; repeat deex; intros; inv_write_set_allocd; congruence).

  Fixpoint wtxn_in_domain_dec (txn:write_transaction) (h:heap) {struct txn} :
    {write_set_allocd h txn} + {~write_set_allocd h txn}.
  Proof.
    unfold not in *.
    destruct txn.
    - left; eauto.
    - destruct (wtxn_in_domain_dec txn h); t'.
      destruct h0;
        match goal with
        | [ i: ident |- _ ] =>
          destruct (h i) eqn:H; t';
            try match goal with
                | [ v: Var |- _ ] => destruct v; t'
                end
        end.
  Defined.

  Definition step_dec (sigma: Sigma) T (p: cprog T) : StepOutcome T :=
    match p with
    | Alloc v => NonDet
    | ReadTxn tx => if rtxn_in_domain_dec tx (Sigma.mem sigma)
                   then NonDet (* still need to check type *)
                   else Fails
    | AssgnTxn tx => if CanWrite (Sigma.l sigma) then
                        if wtxn_in_domain_dec tx (Sigma.mem sigma)
                        then NonDet (* still need to check type *)
                        else Fails
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
                       match l, l' with
                       | Free, Free => Fails
                       | Free, WriteLock => NonDet
                       | WriteLock, Free => StepTo (Sigma.set_l sigma Free) tt
                       | WriteLock, WriteLock => Fails
                       end
                     else Fails
    | Ret v => StepTo sigma v
    | _ => NonDet
    end.

  Inductive outcome T :=
  | Finished (sigma:Sigma) (r:T)
  | Error.

  Arguments Error {T}.

  Inductive rtxn_step : forall T (txn:read_transaction T), heap -> T -> Prop :=
  | rtxn_step_done : forall h, rtxn_step RDone h tt
  | rtxn_step_cons : forall A i (v:A) A' (txn: read_transaction A') h vals,
      h i = Some (val v) ->
      rtxn_step txn h vals ->
      rtxn_step (RCons A i txn) h (v, vals).

  Inductive rtxn_error : forall T (txn:read_transaction T), heap -> Prop :=
  | rtxn_step_error_here : forall A1 A2 i (v:A1) h A' (txn: read_transaction A'),
      A1 <> A2 ->
      h i = Some (val v) ->
      rtxn_error (RCons A2 i txn) h
  | rtxn_step_error_later : forall A i h A' (txn: read_transaction A'),
      rtxn_error txn h ->
      rtxn_error (RCons A i txn) h.

  Inductive wtxn_error : forall (txn:write_transaction), heap -> Prop :=
  | wtxn_step_error_here : forall A1 A2 i (v0:A1) (v:A2) h (txn: write_transaction),
      A1 <> A2 ->
      h i = Some (val v0) ->
      wtxn_error (WCons (NewVal i v) txn) h
  | wtxn_step_error_later : forall (up:heapupd) h (txn: write_transaction),
      wtxn_error txn h ->
      wtxn_error (WCons up txn) h.

  Inductive wtxn_step (tid:TID) : forall (txn: write_transaction), heap -> heap -> Prop :=
  | wtxn_step_done : forall h, wtxn_step tid WDone h h
  | wtxn_step_val_cons : forall A i (v0 v':A)
                           (txn: write_transaction) h h'',
      h i = Some (val v0) ->
      wtxn_step tid txn (upd h i (val v')) h'' ->
      wtxn_step tid (WCons (NewVal i v') txn) h h''
  | wtxn_step_val_abs : forall A i (v0:A) f
                          (txn: write_transaction) h h'',
      h i = Some (abs v0) ->
      wtxn_step tid txn (upd h i (abs (f tid v0))) h'' ->
      wtxn_step tid (WCons (AbsUpd i f) txn) h h''
  | wtxn_step_val_absmem : forall A AEQ V i (m0:@mem A AEQ V) f
                             (txn: write_transaction) h h'',
      h i = Some (absMem m0) ->
      wtxn_step tid txn (upd h i (absMem (f tid m0))) h'' ->
      wtxn_step tid (WCons (AbsUpd i f) txn) h h''.

  Inductive exec (tid:TID) : forall T, Sigma -> cprog T -> outcome T -> Prop :=
  | ExecStepDec : forall T (p: cprog T) sigma sigma' v,
      step_dec sigma p = StepTo sigma' v ->
      exec tid sigma p (Finished sigma' v)
  | ExecStepDecFail : forall T (p: cprog T) sigma,
      step_dec sigma p = Fails ->
      exec tid sigma p Error
  | ExecHash : forall sigma sz buf,
      let h := hash_fwd buf in
      hash_safe (Sigma.hm sigma) h buf ->
      exec tid sigma (@Hash sz buf) (Finished (Sigma.upd_hm sigma buf) h)
  | ExecBindFinish : forall T T' (p: cprog T') (p': T' -> cprog T)
                       sigma sigma' v out,
      exec tid sigma p (Finished sigma' v) ->
      exec tid sigma' (p' v) out ->
      exec tid sigma (Bind p p') out
  | ExecBindFail : forall T T' (p: cprog T') (p': T' -> cprog T) sigma,
      exec tid sigma p Error ->
      exec tid sigma (Bind p p') Error
  | ExecWriteLock : forall sigma sigma',
      Sigma.l sigma = Free ->
      Rely tid sigma sigma' ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ->
      let sigma' := Sigma.set_l sigma' WriteLock in
      exec tid sigma (SetLock Free WriteLock) (Finished sigma' tt)
  | ExecAlloc : forall sigma A (v:A) i,
      Sigma.mem sigma i = None ->
      let sigma' := Sigma.set_mem sigma (upd (Sigma.mem sigma) i (val v)) in
      exec tid sigma (Alloc v)
           (Finished sigma' i)
  | ExecReadTxn : forall sigma A (txn:read_transaction A) v sigma',
      rtxn_step txn (Sigma.mem sigma) v ->
      (Sigma.l sigma = WriteLock -> sigma' = sigma) ->
      (Sigma.l sigma = Free -> Rely tid sigma sigma') ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') ->
      exec tid sigma (ReadTxn txn)
           (Finished sigma' v)
  | ExecReadTxnFail : forall sigma A (txn:read_transaction A),
      rtxn_error txn (Sigma.mem sigma) ->
      exec tid sigma (ReadTxn txn) Error
  | ExecAssgnTxn : forall sigma (txn:write_transaction) h',
      Sigma.l sigma = WriteLock ->
      wtxn_step tid txn (Sigma.mem sigma) h' ->
      let sigma' := Sigma.set_mem sigma h' in
      Guarantee tid sigma sigma' ->
      exec tid sigma (AssgnTxn txn)
           (Finished sigma' tt)
  | ExecAssgnTxnProtocolError : forall sigma (txn:write_transaction) h',
      Sigma.l sigma = WriteLock ->
      wtxn_step tid txn (Sigma.mem sigma) h' ->
      let sigma' := Sigma.set_mem sigma h' in
      ~Guarantee tid sigma sigma' ->
      exec tid sigma (AssgnTxn txn) Error
  | ExecAssgnTxnTyError : forall sigma (txn:write_transaction),
      wtxn_error txn (Sigma.mem sigma) ->
      exec tid sigma (AssgnTxn txn) Error.

  Theorem ExecRet : forall tid T (v:T) sigma,
      exec tid sigma (Ret v) (Finished sigma v).
  Proof.
    intros.
    eapply ExecStepDec.
    auto.
  Qed.

  Definition SpecDouble T :=
    Sigma -> (Sigma -> T -> Prop) -> Prop.

  Definition cprog_ok tid T (pre: SpecDouble T) (p: cprog T) :=
    forall st donecond out, pre st donecond ->
                       exec tid st p out ->
                       match out with
                       | Finished sigma' v =>
                         donecond sigma' v
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
    | [ H: exec _ _ _ _ (Finished _ _) |- _ ] => inv_exec' H
    | [ H: exec _ _ _ _ Error |- _ ] => inv_exec' H
    end.

End CCLTactics.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)