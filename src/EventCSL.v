Require Export Mem.
Require Export Pred.
Require Export Word.
Require Export SepAuto.
Require Import Omega.
Require Import Star.
Require Import Hlist.
Require Import List.
Import List.ListNotations.
Local Open Scope list.

(* defined in Prog. which we don't want to import here *)
Definition addrlen := 64.
Definition valulen := 64.
Notation addr := (word addrlen).
Notation valu := (word valulen).

Set Implicit Arguments.

Definition pred_in AT AEQ V (F: @pred AT AEQ V) m := F m.

Notation "m '|=' F" :=
  (pred_in F%pred m) (at level 30, F at level 40) : mem_judgement_scope.

Delimit Scope mem_judgement_scope with judgement.

Inductive valuset : Set :=
  | Valuset (last:valu) (pending:list valu).

Definition buffer_valu (vs:valuset) v :=
  match vs with
  | Valuset last pending => Valuset v (last::pending)
  end.

Definition latest_valu (vs:valuset) :=
  let 'Valuset last _ := vs in last.

Definition synced (vs:valuset) :=
  let 'Valuset last _ := vs in Valuset last nil.

Hint Immediate (Valuset $0 nil).

(* a disk state *)
Notation DISK := (@mem addr (@weq addrlen) valuset).

(* a disk predicate *)
Notation DISK_PRED := (@pred addr (@weq addrlen) valuset).

Definition ID := nat.

Section Lock.
  Inductive Mutex := Open | Locked.
  Definition is_locked l :
    {l = Locked} + {l = Open}.
  Proof.
    destruct l; intuition eauto.
  Defined.
End Lock.

Section EventCSL.
  Set Default Proof Using "Type".

  Implicit Type d : DISK.

  (** The memory is a heterogenously typed list where element types
      are given by Mcontents. *)
  Variable Mcontents:list Set.
  (** The type of the program's memory. *)
  Definition M := @hlist Set (fun T:Set => T) Mcontents.

  Implicit Type m : M.

  (** Programs can manipulate ghost state of type S *)
  Variable S:Type.

  (** Our programs will return values of type T *)
  Variable T:Type.

  Definition var (t:Set) : Type := @member Set t Mcontents.

  (** Define the transition system for the semantics.
      The semantics will reject transitions that do not obey these rules. *)
  Definition Relation := S -> S -> Prop.
  Variable StateR : ID -> Relation.
  Variable LockR : ID -> Relation.
  Definition Invariant := M -> S -> DISK_PRED.
  Variable StateI : Invariant.
  Variable LockI : Invariant.

  CoInductive prog :=
  | AsyncRead (a: addr) (rx: valu -> prog)
  | Read (a: addr) (rx: valu -> prog)
  | Write (a: addr) (v: valu) (rx: unit -> prog)
  | Sync (a: addr) (rx: unit -> prog)
  | Get t (v: var t) (rx: t -> prog)
  | Assgn t (v: var t) (val:t) (rx: unit -> prog)
  | GetTID (rx: ID -> prog)
  | AcquireLock (l: var Mutex) (lock_ghost: ID -> S -> S) (rx: unit -> prog)
  | Yield (rx: unit -> prog)
  | Commit (up: S -> S) (rx: unit -> prog)
  | Done (v: T).

  Ltac inv_prog :=
    match goal with
    | [ H: @eq prog _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type p : prog.

  Definition state := (DISK * M * S * S)%type.

  Reserved Notation "tid ':-' p '/' st '==>' p' '/' st'"
           (at level 40, p at next level, p' at next level).

  Definition othersR (stateR:ID -> Relation) tid : Relation :=
    fun s s' =>
      exists tid', tid <> tid' /\
              stateR tid' s s'.

  Definition ProgR : ID -> Relation :=
    fun tid =>
      fun s s' =>
        StateR tid s s' /\
        LockR tid s s'.

  Definition ProgI : Invariant :=
    fun m s d =>
      StateI m s d /\
      LockI m s d.

  (* StateR' tid is a valid transition for someone other than tid *)
  Definition StateR' : ID -> Relation := othersR StateR.
  (* LockR' tid obeys the locking discipline for a non-tid thread *)
  Definition LockR' : ID -> Relation := othersR LockR.
  Definition ProgR' : ID -> Relation := othersR ProgR.

  (* TODO: use ProgR and ProgI throughout, not just for AsyncRead *)

  Inductive step (tid:ID) : forall st p st' p', Prop :=
  | StepAsyncRead : forall d m s0 s
                      d' m' s'
                      d'' v rest m'' s''
                      d''' m''' s'''
                      d'''' m'''' s''''
                      a rx,
      ProgI m s d ->
      star (ProgR' tid) s s' ->
      ProgI m' s' d' ->
      star (LockR' tid) s' s'' ->
      LockI m'' s'' d'' ->
      d'' a = Some (Valuset v rest) ->
      star (LockR' tid) s'' s''' ->
      LockI m''' s''' d''' ->
      star (ProgR' tid) s''' s'''' ->
      ProgI m'''' s'''' d'''' ->
      tid :- AsyncRead a rx / (d, m, s0, s) ==>
          rx v / (d'''', m'''', s'''', s'''')
  | StepRead : forall d m s0 s a rx vs,
      d a = Some vs ->
      tid :- Read a rx / (d, m, s0, s) ==>
          rx (latest_valu vs) / (d, m, s0, s)
  | StepWrite : forall d m s0 s a rx vs0 v',
      d a = Some vs0 ->
      let d' := upd d a (buffer_valu vs0 v') in
      LockI m s d' ->
      tid :- Write a v' rx / (d, m, s0, s) ==>
          rx tt / (d', m, s0, s)
  | StepSync : forall d m s0 s a rx vs0,
      d a = Some vs0 ->
      tid :- Sync a rx / (d, m, s0, s) ==>
          rx tt / (upd d a (synced vs0), m, s0, s)
  | StepAcquireLock : forall d m m' s s0 d' s' up rx l,
      let m'' := set l Locked m' in
      let s'' := up tid s' in
      StateI m s d ->
      LockI m s d ->
      StateR tid s0 s ->
      StateI m' s' d' ->
      LockI m' s' d' ->
      star (StateR' tid) s s' ->
      star (LockR' tid) s s' ->
      LockR tid s' s'' ->
      LockI m'' s'' d' ->
      tid :- AcquireLock l up rx / (d, m, s0, s) ==> rx tt / (d', m'', s'', s'')
  | StepYield : forall d m s0 s s' m' d' rx,
      StateI m s d ->
      LockI m s d ->
      StateI m' s' d' ->
      LockI m' s' d' ->
      StateR tid s0 s ->
      star (StateR' tid) s s' ->
      star (LockR' tid) s s' ->
      tid :- Yield rx / (d, m, s0, s) ==> rx tt / (d', m', s', s')
  | StepCommit : forall d m s0 s up rx,
      let s' := up s in
      LockR tid s s' ->
      tid :- Commit up rx / (d, m, s0, s) ==> rx tt / (d, m, s0, s')
  | StepGetTID : forall st rx,
      tid :- GetTID rx / st ==> rx tid / st
  | StepGet : forall d m s s0 t (v: var t) rx,
      tid :- Get v rx / (d, m, s0, s) ==> rx (get v m) / (d, m, s0, s)
  | StepAssgn : forall d m s s0 t (v: var t) val rx,
      let m' := set v val m in
      LockI m' s d ->
      tid :- Assgn v val rx / (d, m, s0, s) ==> rx tt / (d, m', s0, s)
  where "tid ':-' p '/' st '==>' p' '/' st'" := (step tid st p st' p').

  Inductive fail_step (tid:ID) : prog -> state -> Prop :=
  | FailStepAsyncRead : forall a d m s0 s rx,
      ~ProgI m s d ->
      fail_step tid (AsyncRead a rx) (d, m, s0, s)
  | FailStepRead : forall a d m s0 s rx, d a = None ->
                                    fail_step tid (Read a rx) (d, m, s0, s)
  | FailStepWriteMissing : forall a v d m s0 s rx, d a = None ->
                                              fail_step tid (Write a v rx) (d, m, s0, s)
  | FailStepWriteLock : forall a vs0 v' d m s0 s rx, d a = Some vs0 ->
                                              let d' := upd d a (buffer_valu vs0 v') in
                                              ~LockI m s d' ->
                                              fail_step tid (Write a v' rx) (d, m, s0, s)
  | FailStepAcquireLock : forall l up d m s0 s rx, (~StateI m s d) ->
                                           fail_step tid (AcquireLock l up rx) (d, m, s0, s)
  | FailStepAssgnLock : forall d m s s0 t (v: var t) val rx,
      let m' := set v val m in
      ~LockI m' s d ->
      fail_step tid (Assgn v val rx) (d, m, s0, s)
  | FailStepCommitLock : forall d m s0 s up rx,
      let s' := up s in
      ~LockR tid s s' ->
      fail_step tid (Commit up rx) (d, m, s0, s)
  | FailStepYield : forall d m s0 s rx, (~StateI m s d) ->
                                   fail_step tid (Yield rx) (d, m, s0, s).

  Hint Constructors step fail_step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Inductive outcome :=
  | Failed
  | Crashed d
  | Finished d (v:T).

  (** yieldProg p holds when p begins by yielding to the scheduler.

  This might be needed to define executions such that a crash in the middle of
  a yield results in a state consistent with the lock discipline, but I don't
  believe this is important since some other thread must have crashed during
  execution and we can use its crash condition. *)
  Inductive yieldProg : forall p, Prop :=
  | YieldProgYield : forall rx,
    yieldProg (Yield rx)
  | YieldProgAsyncRead : forall a rx,
    yieldProg (AsyncRead a rx)
  | YieldProgAcquireLock : forall l up rx,
    yieldProg (AcquireLock l up rx).

  Inductive exec tid : forall st p (out:outcome), Prop :=
  | ExecStep : forall st p st' p' out,
      tid :- p / st ==> p' / st' ->
      exec tid st' p' out ->
      exec tid st p out
  | ExecFail : forall st p,
      fail_step tid p st ->
      exec tid st p Failed
  | ExecCrash : forall d m s0 s p,
      exec tid (d, m, s0, s) p (Crashed d)
  | ExecDone : forall d m s0 s v,
      exec tid (d, m, s0, s) (Done v) (Finished d v).

  Hint Constructors exec.

  (* clear up dependent equalities produced by inverting fail_step *)
  Ltac sigT_eq :=
    match goal with
    | [ H: @eq (sigT _) _ _ |- _ ] =>
      apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
        subst
    end.

  Ltac inv_fail_step :=
    match goal with
    | [ H: context[fail_step] |- _ ] =>
      inversion H; subst;
      (* produce equalities from dependent equalities using proof
      irrelevance *)
      repeat sigT_eq;
      (* get rid of local definitions in context *)
      repeat match goal with
             | [ v := _ : _ |- _ ] => subst v
             end
    end.

  Ltac condition_failure :=
    intros; inv_fail_step; eauto; try congruence.

  Theorem async_read_failure : forall tid d m s0 s rx a,
      fail_step tid (AsyncRead a rx) (d, m, s0, s) ->
      ProgI m s d ->
      False.
  Proof.
    condition_failure.
  Qed.

  Theorem read_failure : forall tid d m s0 s rx a v,
      fail_step tid (Read a rx) (d, m, s0, s) ->
      d a = Some v ->
      False.
  Proof.
    condition_failure.
  Qed.

  Theorem write_failure : forall tid d m s0 s v rx a v0,
      fail_step tid (Write a v rx) (d, m, s0, s) ->
      d a = Some v0 ->
      LockI m s (upd d a (buffer_valu v0 v)) ->
      False.
  Proof.
    condition_failure.
  Qed.

  Theorem assgn_failure : forall tid d m s0 s rx t (v: var t) val,
      fail_step tid (Assgn v val rx) (d, m, s0, s) ->
      LockI (set v val m) s d ->
      False.
  Proof.
    condition_failure.
  Qed.

  Theorem commit_failure : forall tid d m s0 s rx up,
      fail_step tid (Commit up rx) (d, m, s0, s) ->
      LockR tid s (up s) ->
      False.
  Proof.
    condition_failure.
  Qed.

  Hint Resolve read_failure write_failure assgn_failure commit_failure.

  Definition donecond := T -> DISK_PRED.
  Definition crashcond := DISK_PRED.

  (** A Hoare double judgement: encodes a Crash Hoare Logic tuple via
  a precondition that accepts appropriate postconditions (donecond) and crash
  conditions. *)
  Definition valid tid (pre: donecond -> crashcond ->
        (* state: d, m, s0, s *)
        mem -> M -> S -> S -> Prop) p : Prop :=
    forall d m s0 s done crash out,
      pre done crash d m s0 s ->
      exec tid (d, m, s0, s) p out ->
      (exists d' v,
        out = Finished d' v /\ done v d') \/
      (exists d',
        out = Crashed d' /\ crash d').

  (** Programs are written in continuation-passing style, where sequencing
  is simply function application. We wrap this sequencing in a function for
  automation purposes, so that we can recognize when logically instructions
  are being sequenced. B is a continuation, of the type (input -> prog), while
  A is the type of the whole expression, (output -> prog). *)
  Definition progseq (A B:Type) (p1 : B -> A) (p2: B) := p1 p2.

  Ltac inv_st :=
    match goal with
    | [ H : @eq state _ _ |- _ ] =>
      inversion H
    end.

  Ltac inv_tuple :=
    match goal with
    | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] =>
      inversion H; subst
    end.

  Ltac ind_exec :=
    match goal with
    | [ H : exec _ ?st ?p _ |- _ ] =>
      remember st; remember p;
      induction H; subst;
      try (destruct st; inv_st);
      try inv_tuple;
      try inv_step;
      try inv_prog
    end.

  Ltac prove_rx :=
    match goal with
    | [ H: forall _, valid _ _ _ |- _ ] =>
      edestruct H; eauto
    end.

  Notation "tid |- {{ e1 .. e2 , | 'PRE' d m s0 s : pre | 'POST' d' m' s0' s' r : post | 'CRASH' d'c : oncrash }} p" :=
    (forall (rx: _ -> prog) (tid:ID),
        valid tid (fun done crash d m s0 s =>
                     (ex (fun e1 => .. (ex (fun e2 =>
                                           pre%judgement /\
                                           (forall ret_,
                                             valid tid (fun done_rx crash_rx d' m' s0' s' =>
                                                      (fun r => post%judgement) ret_ /\
                                                      done_rx = done /\
                                                      crash_rx = crash)
                                                   (rx ret_)) /\
                                           (forall d'c, oncrash%judgement -> crash d'c)
                                    )) .. ))
                  ) (p rx))
      (at level 0, p at level 60,
       e1 binder, e2 binder,
       d at level 0,
       d' at level 0,
       m at level 0,
       m' at level 0,
       s0 at level 0,
       s0' at level 0,
       s at level 0,
       s' at level 0,
       r at level 0,
       d'c at level 0,
       only parsing).

  (* extract the precondition of a valid statement into the hypotheses *)
  Ltac intros_pre :=
    unfold valid at 1; unfold pred_in; intros;
    repeat deex.

  (* simplify the postcondition obligation to its components *)
  Ltac simpl_post :=
    cbn; intuition;
      (* get rid of local definitions in context *)
      repeat match goal with
             | [ v := _ : _ |- _ ] => subst v
             end.

  Ltac learn_mem_val H m a :=
    let v := fresh "v" in
      evar (v : valuset);
      assert (m a = Some v);
      [ eapply ptsto_valid;
        pred_apply' H; cancel |
      ]; subst v.

  Ltac learn_some_addr :=
    match goal with
    | [ a: addr, H: ?P ?m |- _ ] =>
      match P with
      | context[(a |-> _)%pred] => learn_mem_val H m a
      end
    end.

  Ltac match_valusets :=
    match goal with
    | [ H: ?d ?a = Some ?v1, H': ?d ?a = Some ?v2 |- _ ] =>
      assert (v1 = v2) by congruence; subst v2;
      clear H'
    end.

  Ltac opcode_ok :=
    intros_pre; ind_exec;
    try match goal with
    | [ H: context[step] |- _ ] =>
      prove_rx; simpl_post
    | [ H: context[fail_step] |- _ ] =>
      try solve [ inversion H; congruence ];
        try match goal with
        | [ Ha: context[ptsto] |- _ ] =>
          apply ptsto_valid' in Ha
        end;
      exfalso
    end;
    try (learn_some_addr; match_valusets);
    eauto 10.

  Theorem Write_ok : forall a v,
      tid |- {{ F v0,
             | PRE d m s0 s: d |= F * a |-> v0 /\
                             LockI m s (upd d a (buffer_valu v0 v))
             | POST d' m' s0' s' _: d' |= F * a |-> (buffer_valu v0 v) /\
                                s0' = s0 /\
                                s' = s /\
                                m' = m
             | CRASH d'c : d'c = d
            }} Write a v.
  Proof.
    opcode_ok.
    eapply pimpl_apply; [| eapply ptsto_upd].
    cancel.
    pred_apply; cancel.
  Qed.

  Theorem Sync_ok : forall a,
      tid |- {{ F v0,
             | PRE d m s0 s: d |= F * a |-> v0
             | POST d' m' s0' s' _: d' |= F * a |-> (synced v0) /\
                                s0' = s0 /\
                                s' = s /\
                                m' = m
             | CRASH d'c : d'c = d
            }} Sync a.
  Proof.
    opcode_ok.
    eapply pimpl_apply; [| eapply ptsto_upd].
    cancel.
    pred_apply; cancel.
  Qed.

  Theorem AsyncRead_ok : forall a,
      tid |- {{ (_:unit),
             | PRE d m s0 s: ProgI m s d
             | POST d'''' m'''' s0' s'''' v:
                 s0' = s'''' /\
                 exists m' s' d'
                   m'' s'' d''
                   F rest
                   m''' s''' d''',
                   star (ProgR' tid) s s' /\
                   ProgI m' s' d' /\
                   star (LockR' tid) s' s'' /\
                   LockI m'' s'' d'' /\
                   d'' |= F * a |-> (Valuset v rest) /\
                   star (LockR' tid) s'' s''' /\
                   LockI m''' s''' d''' /\
                   star (ProgR' tid) s''' s'''' /\
                   ProgI m'''' s'''' d''''
            | CRASH d'c : d'c = d
            }} AsyncRead a.
  Proof.
    opcode_ok.
    unfold ProgI in *; intuition.
    repeat eexists; eauto using ptsto_valid_iff.
  Qed.

  Theorem Read_ok : forall a,
    tid |- {{ F v0,
      | PRE d m s0 s: d |= F * a |-> v0
      | POST d' m' s0' s' v: d' = d /\
                             v = latest_valu v0 /\
                             s0' = s0 /\
                             s' = s /\
                             m' = m
      | CRASH d'c : d'c = d
    }} Read a.
  Proof.
    opcode_ok.
  Qed.

  Theorem Get_ok : forall t (v: var t),
      tid |- {{ (_:unit),
             | PRE d m s0 s: True
             | POST d' m' s0' s' r: d' = d /\
                                    r = get v m /\
                                    m' = m /\
                                    s0' = s0 /\
                                    s' = s
             | CRASH d'c : d'c = d
            }} Get v.
  Proof.
    opcode_ok; repeat sigT_eq;
      (* this search is apparently too deep/complex for eauto *)
      match goal with
      | [ H: _ -> valid _ _ _ |- _ ] =>
        eapply H; intuition eauto
      end.
  Qed.

  Theorem Assgn_ok : forall t (v: var t) val,
      tid |- {{ (_:unit),
             | PRE d m s0 s: LockI (set v val m) s d
             | POST d' m' s0' s' _: d' = d /\
                                    m' = set v val m /\
                                    s0' = s0 /\
                                    s' = s
             | CRASH d'c : d'c = d
            }} Assgn v val.
  Proof.
    opcode_ok; repeat sigT_eq; eauto.
  Qed.

  Theorem GetTID_ok :
    tid |- {{ (_:unit),
           | PRE d m s0 s: True
           | POST d' m' s0' s' r: d' = d /\
                                  m' = m /\
                                  s0' = s0 /\
                                  s' = s /\
                                  r = tid
           | CRASH d'c: d'c = d
          }} GetTID.
  Proof.
    opcode_ok.
  Qed.

  Theorem AcquireLock_ok : forall l up,
      tid |- {{ (_:unit),
             | PRE d m s0 s: d |= StateI m s /\
                             StateR tid s0 s
             | POST d' m'' s0' s'' _: exists m' s',
                 d' |= StateI m' s' /\
                 LockI m' s' d' /\
                 star (StateR' tid) s s' /\
                 star (LockR' tid) s s' /\
                 LockR tid s' s'' /\
                 m'' = set l Locked m' /\
                 s'' = up tid s' /\
                 get l m'' = Locked /\
                 s0' = s''
             | CRASH d'c: d'c = d
            }} AcquireLock l up.
  Proof.
    opcode_ok.
    repeat eexists; intuition.
    simpl_get_set.
  Qed.

  Theorem Yield_ok :
    tid |- {{ (_:unit),
           | PRE d m s0 s: d |= StateI m s /\
                           StateR tid s0 s
           | POST d' m' s0' s' _: d' |= StateI m' s' /\
                                  s0' = s' /\
                                  star (StateR' tid) s s' /\
                                  star (LockR' tid) s s' /\
                                  LockI m' s' d'
           | CRASH d'c: d'c = d
    }} Yield.
  Proof.
    opcode_ok.
  Qed.

  Theorem Commit_ok : forall up,
    tid |- {{ (_:unit),
           | PRE d m s0 s: LockR tid s (up s)
           | POST d' m' s0' s' _: d' = d /\
                                  s0' = s0 /\
                                  s' = up s /\
                                  m' = m
           | CRASH d'c: d'c = d
          }} Commit up.
  Proof.
    opcode_ok.
  Qed.

  Theorem pimpl_ok : forall tid (pre pre': _ -> _ -> _ -> _ -> _ -> _ -> Prop) p,
      valid tid pre p ->
      (forall done crash d m s0 s, pre' done crash d m s0 s ->
        pre done crash d m s0 s) ->
      valid tid pre' p.
  Proof.
    unfold valid.
    intros.
    apply H0 in H1.
    eauto.
  Qed.

  Definition If_ P Q (b: {P} + {Q}) (ptrue pfalse : prog) :=
    if b then ptrue else pfalse.

End EventCSL.

(** transitions defines a transition system, grouping the StateR and StateI
variables above.

This makes the notation more convenient, since R and I can be specified in one
ident.
*)
Record transitions Mcontents S := {
      (* StateR s s' holds when s -> s' is a valid transition *)
      StateR: ID -> Relation S;
      (* LockR s s' holds when s -> s' follows the lock protocol *)
      LockR: ID -> Relation S;
      (* StateI m s d holds when the ghost state s matches the memory m and disk d,
        and any important invariants across helds hold in all three *)
      StateI: Invariant Mcontents S;
      (* LockI m s d maintains consistency of lock copies in s and is
      enforced on every write to memory or disk. *)
      LockI: Invariant Mcontents S
      }.

(** Copy-paste metaprogramming:

* Copy the above notation
* add sigma, tid |- in front to specify the transition system and thread ID
* quantify over T and tid and change prog to prog _ _ T (the state/mem types should be inferred)
* add (StateR sigma) (StateI sigma) as arguments to valid *)
Notation "sigma 'TID' ':' tid |- {{ e1 .. e2 , | 'PRE' d m s0 s : pre | 'POST' d' m' s0' s' r : post | 'CRASH' d'c : oncrash }} p" :=
  (forall T (rx: _ -> prog _ _ T) (tid:ID),
      valid (StateR sigma) (LockR sigma) (StateI sigma) (LockI sigma) tid
            (fun done crash d m s0 s =>
               (ex (fun e1 => .. (ex (fun e2 =>
                                     pre%judgement /\
                                     (forall ret_,
                                       valid (StateR sigma) (LockR sigma) (StateI sigma) (LockI sigma) tid
                                             (fun done_rx crash_rx d' m' s0' s' =>
                                                (fun r => post%judgement) ret_ /\
                                                done_rx = done /\
                                                crash_rx = crash)
                                             (rx ret_)) /\
                                     (forall d'c, oncrash%judgement -> crash d'c)
                              )) .. ))
            ) (p rx))
    (at level 0, p at level 60,
     e1 binder, e2 binder,
     d at level 0,
     d' at level 0,
     m at level 0,
     m' at level 0,
     s0 at level 0,
     s0' at level 0,
     s at level 0,
     s' at level 0,
     r at level 0,
     d'c at level 0,
     only parsing).

Notation "p1 ;; p2" := (progseq p1 (fun _:unit => p2))
                         (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2))
                              (at level 60, right associativity).

(* maximally insert the return/state types for Yield/GetTID, which are always called
   without applying them to any arguments *)
Arguments Yield {Mcontents} {S} {T} rx.
Arguments GetTID {Mcontents} {S} {T} rx.

Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

(** This notation is intended to produce the patterns for prog hints.

The ; _ is merely a visual indicator that the pattern applies to any Hoare
statement beginning with f and followed by anything else. *)
Notation "{{ f ; '_' }}" := (valid _ _ _ _ _ _ (progseq f _)).

Hint Extern 1 {{ AsyncRead _; _ }} => apply AsyncRead_ok : prog.
Hint Extern 1 {{ Read _; _ }} => apply Read_ok : prog.
Hint Extern 1 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 1 {{ Sync _; _ }} => apply Sync_ok : prog.
Hint Extern 1 {{ Get _; _ }} => apply Get_ok : prog.
Hint Extern 1 {{ Assgn _ _; _ }} => apply Assgn_ok : prog.
Hint Extern 1 {{ GetTID ; _ }} => apply GetTID_ok : prog.
Hint Extern 1 {{ Yield; _ }} => apply Yield_ok : prog.
Hint Extern 1 {{ Commit _; _ }} => apply Commit_ok : prog.
Hint Extern 1 {{ AcquireLock _ _; _ }} => apply AcquireLock_ok : prog.