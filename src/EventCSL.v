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
Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).

Set Implicit Arguments.

Definition pred_in AT AEQ V (F: @pred AT AEQ V) m := F m.

Notation "m '|=' F" :=
  (pred_in F%pred m) (at level 30, F at level 40) : mem_judgement_scope.

Delimit Scope mem_judgement_scope with judgement.

Definition ID := nat.

Section Lock.
  Inductive Mutex := Open | Locked (tid:ID).
  Definition is_locked l :
    {exists tid, l = Locked tid} + {l = Open}.
  Proof.
    destruct l; intuition eauto.
  Defined.
End Lock.

Section EventCSL.
  Set Default Proof Using "Type".

  (* a disk state *)
  Notation "'DISK'" := (@mem addr (@weq addrlen) valu).
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

  (** Define the transition system for the ghost state.
      The semantics will reject transitions that do not obey these rules. *)
  Definition Relation := ID -> DISK * M * S -> DISK * M * S -> Prop.
  Variable StateR : Relation.
  Definition Invariant := M -> S -> @pred addr (@weq addrlen) valu.
  Variable StateI : Invariant.

  CoInductive prog :=
  | Read (a: addr) (rx: valu -> prog)
  | Write (a: addr) (v: valu) (rx: unit -> prog)
  | Get t (v: var t) (rx: t -> prog)
  | Assgn t (v: var t) (val:t) (rx: unit -> prog)
  | GetTID (rx: ID -> prog)
  | AcquireLock (l: var Mutex) (rx: unit -> prog)
  | Yield (rx: unit -> prog)
  | Commit (up: S -> S) (rx: unit -> prog)
  | Done (v: T).

  Ltac inv_prog :=
    match goal with
    | [ H: @eq prog _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type p : prog.

  (* TODO: make this a tuple type *)
  Inductive state :=
    | sigma : forall d m (s:S), state.

  Notation "{| d ; m ; s |}" := (sigma d m s) (at level 0).

  Reserved Notation "tid ':-' p '/' st '==>' p' '/' st'"
           (at level 40, p at next level, p' at next level).

  Definition othersR (stateR:Relation) : Relation :=
    fun tid dms dms' =>
      exists tid', tid <> tid' /\
              stateR tid' dms dms'.

  (* StateR' tid is a valid transition for someone other than tid *)
  Definition StateR' : Relation := othersR StateR.

  Inductive step (tid:ID) : forall st p st' p', Prop :=
  | StepRead : forall d m s a rx v, d a = Some v ->
                               tid :- Read a rx / {|d; m; s|} ==> rx v / {|d; m; s|}
  | StepWrite : forall d m s a rx v v', d a = Some v ->
                                   StateR tid (d, m, s) (upd d a v', m, s) ->
                                   tid :- Write a v' rx / {|d; m; s|} ==> rx tt / {|upd d a v'; m; s|}
  | StepAcquireLock : forall d m s d' s' rx l,
      let m' := set m (Locked tid) l in
      StateI m s d ->
      StateI m' s' d' ->
      star (StateR' tid) (d, m, s) (d', m', s') ->
      tid :- AcquireLock l rx / {|d; m; s|} ==> rx tt / {|d'; m'; s'|}
  | StepYield : forall d m s s' m' d' rx,
      StateI m s d ->
      StateI m' s' d' ->
      star (StateR' tid) (d, m, s) (d', m', s') ->
      tid :- Yield rx / {|d; m; s|} ==> rx tt / {|d'; m'; s'|}
  | StepCommit : forall d m s up rx,
      StateR tid (d, m, s) (d, m, up s) ->
      StateI m (up s) d ->
      tid :- Commit up rx / {|d; m; s|} ==> rx tt / {|d; m; up s|}
  | StepGetTID : forall st rx,
      tid :- GetTID rx / st ==> rx tid / st
  | StepGet : forall d m s t (v: var t) rx,
      tid :- Get v rx / {|d; m; s|} ==> rx (get m v) / {|d; m; s|}
  | StepAssgn : forall d m s t (v: var t) val rx,
      StateI (set m val v) s d ->
      StateR tid (d, m, s) (d, set m val v, s) ->
      tid :- Assgn v val rx / {|d; m; s|} ==> rx tt / {|d; set m val v; s|}
  where "tid ':-' p '/' st '==>' p' '/' st'" := (step tid st p st' p').

  Hint Constructors step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Inductive outcome :=
  | Failed
  | Finished d (v:T).

  Inductive exec tid : forall st p (out:outcome), Prop :=
  | ExecStep : forall st p st' p' out,
      tid :- p / st ==> p' / st' ->
      exec tid st' p' out ->
      exec tid st p out
  | ExecFail : forall st p,
      (~ exists st' p', tid :- p / st ==> p' / st') ->
      (forall v, p <> Done v) ->
      exec tid st p Failed
  | ExecDone : forall d m s v,
      exec tid {|d; m; s|} (Done v) (Finished d v).

  Hint Constructors exec.

  Ltac invalid_address :=
    match goal with
    | [ H: ~ exists st' p', step _ _ _ _ _ |- context[?d ?a = None] ] =>
      case_eq (d a); auto; intros;
      try solve [ contradiction H;
                  eauto ]
    end.

  Ltac no_step :=
    match goal with
    | [  |- ~ (exists st' p', step _ _ _ _ _) ] =>
      let Hcontra := fresh in
      intro Hcontra;
        repeat deex;
        inversion Hcontra; congruence
    end.

  Ltac address_failure :=
    intros; split; intros;
    try invalid_address;
    try no_step.

  Theorem read_failure_iff : forall tid d m s rx a,
      (~ exists st' p', tid :- Read a rx / {|d; m; s|} ==> p' / st') <->
      d a = None.
  Proof.
    address_failure.
  Qed.

  Ltac sigT_eq :=
    match goal with
    | [ H: @eq (sigT _) _ _ |- _ ] =>
      apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
        subst
    end.

  Ltac not_sidecondition_fail :=
    intros; intro Hcontra;
    repeat deex;
    inv_step;
    repeat sigT_eq;
    congruence.

  Theorem write_failure_iff : forall tid d m s v rx a,
      (~ exists st' p', tid :- Write a v rx / {|d; m; s|} ==> p' / st') <->
      (d a = None \/
       ~ StateR tid (d, m, s) (upd d a v, m, s)).
  Proof.
    address_failure;
    try not_sidecondition_fail;
    intuition eauto.
  Qed.

  Theorem assgn_failure : forall tid d m s rx t (v:var t) val,
      (~StateI (set m val v) s d) \/
      (~StateR tid (d, m, s) (d, set m val v, s)) ->
      (~ exists st' p', tid :- Assgn v val rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem yield_failure : forall tid d m s rx,
      (~StateI m s d) ->
      (~ exists st' p', tid :- Yield rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure : forall tid d m s up rx,
    (~StateI m (up s) d \/
     (~StateR tid (d, m, s) (d, m, up s))) ->
     (~ exists st' p', tid :- Commit up rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Hint Extern 2 (forall v, _ <> Done v) => intro; congruence.

  Definition donecond := T -> @pred addr (@weq addrlen) valu.

  Definition valid tid (pre: donecond -> mem -> M -> S -> Prop) p : Prop :=
    forall d m s done out,
      pre done d m s ->
      exec tid {|d; m; s|} p out ->
      exists d' v,
        out = Finished d' v /\
        done v d'.

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

  Ltac ind_exec :=
    match goal with
    | [ H : exec _ ?st ?p _ |- _ ] =>
      remember st; remember p;
      induction H; subst;
      try (destruct st; inv_st);
      try inv_step;
      try inv_prog
    end.

  Ltac prove_rx :=
    match goal with
    | [ H: forall _, valid _ _ _ |- _ ] =>
      edestruct H; eauto
    end.

  Notation "tid |- {{ e1 .. e2 , | 'PRE' d m s : pre | 'POST' d' m' s' r : post }} p" :=
    (forall (rx: _ -> prog) (tid:ID),
        valid tid (fun done d m s =>
                     (ex (fun e1 => .. (ex (fun e2 =>
                                           pre%judgement /\
                                           forall ret_,
                                             valid tid (fun done_rx d' m' s' =>
                                                      (fun r => post%judgement) ret_ /\
                                                      done_rx = done)
                                                   (rx ret_)
                                    )) .. ))
                  ) (p rx))
      (at level 0, p at level 60,
       e1 binder, e2 binder,
       d at level 0,
       d' at level 0,
       m at level 0,
       m' at level 0,
       s at level 0,
       s' at level 0,
       r at level 0,
       only parsing).

  (* extract the precondition of a valid statement into the hypotheses *)
  Ltac intros_pre :=
    unfold valid at 1; unfold pred_in; intros;
    repeat deex.

  (* simplify the postcondition obligation to its components *)
  Ltac simpl_post :=
    cbn; intuition.

  Ltac opcode_ok :=
    intros_pre; ind_exec;
    match goal with
    | [ H: step _ _ _ _ _ |- _ ] =>
      prove_rx; simpl_post
    | [ H: ~ exists st' p', step _ _ _ _ _ |- _ ] =>
      exfalso
    end; eauto 10.

  Theorem write_ok : forall a v0 v,
      tid |- {{ F,
             | PRE d m s: d |= F * a |-> v0 /\
                          StateR tid (d, m, s) (upd d a v, m, s)
               | POST d' m' s' _: d' |= F * a |-> v /\
                                  s' = s /\
                                  m' = m
            }} Write a v.
  Proof.
    opcode_ok.
    eapply pimpl_apply; [| eapply ptsto_upd].
    cancel.
    pred_apply; cancel.
    match goal with
    | [ H: ~ exists st' p', step _ _ _ _ _ |- _] =>
      apply write_failure_iff in H
    end.
    match goal with
    | [ H: context[ptsto a  _] |- _ ] =>
      apply ptsto_valid' in H
    end.
    intuition; congruence.
  Qed.

  Theorem read_ok : forall a v0,
    tid |- {{ F,
      | PRE d m s: d |= F * a |-> v0
       | POST d' m' s' v: d' |= F * a |-> v0 /\
                          v = v0 /\
                          s' = s /\
                          m' = m
    }} Read a.
  Proof.
    opcode_ok.
    assert (d a = Some v0).
    eapply ptsto_valid; eauto.
    pred_apply; cancel.
    congruence.
    match goal with
    | [ H: ~ exists st' p', step _ _ _ _ _ |- _ ] =>
      apply read_failure_iff in H
    end.
    match goal with
    | [ H: context[ptsto a _] |- _ ] =>
      apply ptsto_valid' in H
    end.
    congruence.
  Qed.

  Theorem get_ok : forall t (v: var t),
      tid |- {{ F,
             | PRE d m s: d |= F
               | POST d' m' s' r: d' |= F /\
                                  r = get m v /\
                                  m' = m /\
                                  s' = s
            }} Get v.
  Proof.
    opcode_ok; repeat sigT_eq; eauto.
  Qed.

  Theorem assgn_ok : forall t (v: var t) val,
      tid |- {{ F,
             | PRE d m s: d |= F /\
                          StateI (set m val v) s d /\
                          StateR tid (d, m, s) (d, set m val v, s)
       | POST d' m' s' _: d' |= F /\
                          m' = set m val v /\
                          s' = s
      }} Assgn v val.
  Proof.
    opcode_ok; repeat sigT_eq; eauto.
  Qed.

  Theorem get_tid_ok :
    tid |- {{ F,
           | PRE d m s: d |= F
           | POST d' m' s' r: d' |= F /\
                              m' = m /\
                              s' = s /\
                              r = tid
          }} GetTID.
  Proof.
    opcode_ok.
  Qed.

  (** This is a bit dangerous, but assumes that we don't get stuck
      acquiring a lock because the invariants don't allow us to give
      you the lock. For our lock protocol, it's always possible to  *)
  Hypothesis lock_step_available : forall tid d m s l,
      (d |= StateI m s)%judgement ->
      let m' := set m (Locked tid) l in
      exists d' s', (d' |= StateI m' s')%judgement /\
               star (StateR' tid) (d, m, s) (d', m', s').

  Theorem acquire_lock_ok : forall l,
      tid |- {{ (_:unit),
             | PRE d m s: d |= StateI m s
             | POST d' m' s' _: d' |= StateI m' s' /\
                                get m' l = Locked tid
            }} AcquireLock l.
              (* Proof remove lock_step_available *)
              opcode_ok.
              subst m'.
              rewrite get_set; auto.
              edestruct lock_step_available; eauto; deex.
              eauto.
  Qed.

  Theorem yield_ok :
    tid |- {{ (_:unit),
           | PRE d m s: d |= StateI m s
           | POST d' m' s' _: d' |= StateI m' s'
           /\ star (StateR' tid) (d, m, s) (d', m', s')
    }} Yield.
  Proof.
    opcode_ok.
  Qed.

  Theorem commit_ok : forall up,
    tid |- {{ F,
           | PRE d m s: d |= F /\
                        StateR tid (d,m,s) (d,m,up s) /\
                        (F =p=> StateI m (up s))
           | POST d' m' s' _: d' |= F /\
                              s' = up s /\
                              m' = m
          }} Commit up.
  Proof.
    opcode_ok.
  Qed.

  Theorem pimpl_ok : forall tid (pre pre': _ -> _ -> _ -> _ -> Prop) p,
      valid tid pre p ->
      (forall done d m s, pre' done d m s -> pre done d m s) ->
      valid tid pre' p.
  Proof.
    unfold valid.
    firstorder.
  Qed.

  Definition If_ P Q (b: {P} + {Q}) (ptrue pfalse : prog) :=
    if b then ptrue else pfalse.

  Theorem if_ok:
    forall tid P Q (b : {P}+{Q}) (p1 p2 : prog),
      valid tid (fun done d m s => exists pre,
                 pre d m s /\
                 valid tid (fun done' d' m' s' => pre d' m' s' /\
                                           P /\
                                           done' = done) p1 /\
                 valid tid (fun done' d' m' s' => pre d' m' s' /\
                                           Q /\
                                           done' = done) p2
                ) (If_ b p1 p2).
  Proof.
    intros_pre.
    destruct b; eauto.
  Qed.

End EventCSL.

(** transitions defines a transition system, grouping the StateR and StateI
variables above.

This makes the notation more convenient, since R and I can be specified in one
ident.
*)
Record transitions Mcontents S := {
      (* StateR s s' holds when s -> s' is a valid transition *)
      StateR: Relation Mcontents S;
      (* StateI s d holds when s is a valid state and represents the memory d *)
      StateI: Invariant Mcontents S
      }.

(** Copy-paste metaprogramming:

* Copy the above notation
* add sigma, tid |- in front to specify the transition system and thread ID
* quantify over T and tid and change prog to prog _ _ T (the state/mem types should be inferred)
* add (StateR sigma) (StateI sigma) as arguments to valid *)
Notation "sigma 'TID' ':' tid |- {{ e1 .. e2 , | 'PRE' d m s : pre | 'POST' d' m' s' r : post }} p" :=
  (forall T (rx: _ -> prog _ _ T) (tid:ID),
      valid (StateR sigma) (StateI sigma) tid
            (fun done d m s =>
               (ex (fun e1 => .. (ex (fun e2 =>
                                     pre%judgement /\
                                     forall ret_,
                                       valid (StateR sigma) (StateI sigma) tid
                                             (fun done_rx d' m' s' =>
                                                (fun r => post%judgement) ret_ /\
                                                done_rx = done)
                                             (rx ret_)
                              )) .. ))
            ) (p rx))
    (at level 0, p at level 60,
     e1 binder, e2 binder,
     d at level 0,
     d' at level 0,
     m at level 0,
     m' at level 0,
     s at level 0,
     s' at level 0,
     r at level 0,
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
Notation "{{ f ; '_' }}" := (valid _ _ _ _ (progseq f _)).

Hint Extern 1 {{ Read _; _ }} => apply read_ok : prog.
Hint Extern 1 {{ Write _ _; _ }} => apply write_ok : prog.
Hint Extern 1 {{ Get _; _ }} => apply get_ok : prog.
Hint Extern 1 {{ Assgn _ _; _ }} => apply assgn_ok : prog.
Hint Extern 1 {{ GetTID ; _ }} => apply get_tid_ok : prog.
Hint Extern 1 {{ Yield; _ }} => apply yield_ok : prog.
Hint Extern 1 {{ Commit _; _ }} => apply commit_ok : prog.

(* creating member variables for an hlist is painful, so define notation for it.

Ideally we'd have a function nth_member, but the dependent types are too painful
(one problem is that n might be out-of-bounds). *)
Notation "'VAR' 0 'IN' contents" := (@HFirst _ (nth 0 contents unit) (skipn (0+1) contents)) (at level 30).
