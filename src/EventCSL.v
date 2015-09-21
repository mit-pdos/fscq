Require Import Mem.
Require Import Pred.
Require Import Word.
Require Import Omega.
Require Import SepAuto.
Require Import Star.
Require Import Hlist.
Require Import List.
Import List.ListNotations.
Open Scope list.

(* defined in Prog. which we don't want to import here *)
Definition addrlen := 64.
Definition valulen := 64.
Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).

Set Implicit Arguments.

Definition pred_in AT AEQ V (F: @pred AT AEQ V) m := F m.

Notation "m '|=' F ;" :=
  (pred_in F%pred m) (at level 30, F at level 0) : mem_judgement_scope.

Delimit Scope mem_judgement_scope with judgement.

Section EventCSL.
  Set Default Proof Using "Type".

  (* a disk state *)
  Implicit Type d : @mem addr (@weq addrlen) valu.

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

  Definition var t := @member Set t Mcontents.

  (** Define the transition system for the ghost state.
      The semantics will reject transitions that do not obey these rules. *)
  Variable StateR : S -> S -> Prop.
  Variable StateI : S -> @pred addr (@weq addrlen) valu.

  Inductive prog :=
  | Read (a: addr) (rx: valu -> prog)
  | Write (a: addr) (v: valu) (rx: unit -> prog)
  | Get t (v: var t) (rx: t -> prog)
  | Assgn t (v: var t) (val:t) (rx: unit -> prog)
  | Yield (rx: unit -> prog)
  | Commit (up: S -> S) (rx: unit -> prog)
  | Done (v: T).

  Ltac inv_prog :=
    match goal with
    | [ H: @eq prog _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type p : prog.

  Inductive state :=
    | sigma : forall d m (s:S), state.

  Notation "{| d ; m ; s |}" := (sigma d m s) (at level 0).

  Reserved Notation "p '/' st '==>' p' '/' st'" (at level 40, p' at level 39).

  Inductive step : forall st p st' p', Prop :=
  | StepRead : forall d m s a rx v, d a = Some v ->
                             Read a rx / {|d; m; s|} ==> rx v / {|d; m; s|}
  | StepWrite : forall d m s a rx v v', d a = Some v ->
                                 Write a v' rx / {|d; m; s|} ==> rx tt / {|upd d a v'; m; s|}
  | StepYield : forall d m s s' d' rx,
      StateI s d ->
      StateI s' d' ->
      star StateR s s' ->
      Yield rx / {|d; m; s|} ==> rx tt / {|d'; m; s'|}
  | StepCommit : forall d m s up rx,
      StateR s (up s) ->
      StateI (up s) d ->
      Commit up rx / {|d; m; s|} ==> rx tt / {|d; m; up s|}
  | StepGet : forall d m s t (v: var t) rx,
      Get v rx / {|d; m; s|} ==> rx (get m v) / {|d; m; s|}
  | StepAssgn : forall d m s t (v: var t) val rx,
      Assgn v val rx / {|d; m; s|} ==> rx tt / {|d; set m val v; s|}
  where "p '/' st '==>' p' '/' st'" := (step st p st' p').

  Hint Constructors step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Inductive outcome :=
  | Failed
  | Finished d (v:T).

  Inductive exec : forall st p (out:outcome), Prop :=
  | ExecStep : forall st p st' p' out,
      p / st ==> p' / st' ->
      exec st' p' out ->
      exec st p out
  | ExecFail : forall st p,
      (~ exists st' p', p / st ==> p' / st') ->
      (forall v, p <> Done v) ->
      exec st p Failed
  | ExecDone : forall d m s v,
      exec {|d; m; s|} (Done v) (Finished d v).

  Hint Constructors exec.

  Ltac invalid_address :=
    match goal with
    | [ H: ~ exists st' p', step _ _ _ _ |- ?d ?a = None ] =>
      case_eq (d a); auto; intros;
      contradiction H;
      eauto
    end.

  Ltac no_step :=
    match goal with
    | [  |- ~ (exists st' p', step _ _ _ _) ] =>
      let Hcontra := fresh in
      intro Hcontra;
        repeat deex;
        inversion Hcontra; congruence
    end.

  Ltac address_failure :=
    intros; split; intros;
    try invalid_address;
    try no_step.

  Theorem read_failure_iff : forall d m s rx a,
      (~ exists st' p', Read a rx / {|d; m; s|} ==> p' / st') <->
      d a = None.
  Proof.
    address_failure.
  Qed.

  Theorem read_failure : forall d m s rx a,
      (~ exists st' p', Read a rx / {|d; m; s|} ==> p' / st') ->
      d a = None.
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem read_failure' : forall d m s rx a,
      d a = None ->
      (~ exists st' p', Read a rx / {|d; m; s|} ==> p' / st').
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem write_failure_iff : forall d m s v rx a,
      (~ exists st' p', Write a v rx / {|d; m; s|} ==> p' / st') <->
      d a = None.
  Proof.
    address_failure.
  Qed.

  Theorem write_failure : forall d m s v rx a,
      (~ exists st' p', Write a v rx / {|d; m; s|} ==> p' / st') ->
      d a = None.
  Proof.
    apply write_failure_iff.
  Qed.

  Theorem write_failure' : forall d m s v rx a,
      d a = None ->
      (~ exists st' p', Write a v rx / {|d; m; s|} ==> p' / st').
  Proof.
    apply write_failure_iff.
  Qed.

  Ltac not_sidecondition_fail :=
    intros; intro Hcontra;
    repeat deex;
    inv_step;
    congruence.

  Theorem yield_failure'_inv : forall d m s rx,
      (~StateI s d) ->
      (~ exists st' p', Yield rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure'_inv : forall d m s up rx,
    (~StateI (up s) d) ->
    (~ exists st' p', Commit up rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure'_rel : forall d m s up rx,
    (~StateR s (up s)) ->
    (~ exists st' p', Commit up rx / {|d; m; s|} ==> p' / st').
  Proof.
    not_sidecondition_fail.
  Qed.

  Hint Extern 2 (forall v, _ <> Done v) => intro; congruence.

  Theorem exec_progress :
      forall (StateI_dec: forall s d, {StateI s d} + {~StateI s d}),
      forall (StateR_dec: forall s s', {StateR s s'} + {~StateR s s'}),
      forall p st,
      exists out, exec st p out.
  Proof.

    Ltac rx_specialize new_st :=
      match goal with
      | [ H : forall w:?t, forall _, exists out, exec _ _ out |- _ ] =>
        match t with
        | unit => specialize (H tt new_st); inversion H
        | _ => match goal with
              | [ _ : _ _ = Some ?w |- _ ] =>
                specialize (H w new_st); inversion H
              end
        end
      end.

    Hint Resolve read_failure'.
    Hint Resolve write_failure'.
    Hint Resolve yield_failure'_inv.
    Hint Resolve commit_failure'_inv.
    Hint Resolve commit_failure'_rel.

    induction p; intros; destruct st.
    - case_eq (d a); intros.
      rx_specialize {|d; m; s|}.
      all: eauto 15.
    - case_eq (d a); intros.
      rx_specialize {| upd d a v; m; s |}.
      all: eauto 15.
    - specialize (H (get m v) {|d; m; s|}).
      inversion H.
      eauto.
    - rx_specialize {|d; set m val v; s|}.
      eauto.
    - rx_specialize {|d; m; s|}.
      destruct (StateI_dec s d); eauto.
    - case_eq (StateR_dec s (up s));
      case_eq (StateI_dec (up s) d).
      rx_specialize {|d; m; up s|}.
      all: eauto 15.
    - eauto.
  Qed.

  Definition donecond := T -> @pred addr (@weq addrlen) valu.

  Definition valid (pre: donecond -> mem -> M -> S -> Prop) p : Prop :=
    forall d m s done out,
      pre done d m s ->
      exec {|d; m; s|} p out ->
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
    | [ H : exec ?st ?p _ |- _ ] =>
      remember st; remember p;
      induction H; subst;
      try (destruct st; inv_st);
      try inv_step;
      try inv_prog
    end.

  Ltac prove_rx :=
    match goal with
    | [ H: forall _, valid _ _ |- _ ] =>
      edestruct H; eauto
    end.

  Notation "{{ e1 .. e2 , | 'PRE' d m s : pre | 'POST' d' m' s' r : post }} p" :=
    (forall (rx: _ -> prog),
        valid (fun done d m s =>
                 (ex (fun e1 => .. (ex (fun e2 =>
                                           pre%judgement /\
                                           forall ret_,
                                             valid (fun done_rx d' m' s' =>
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

  Theorem write_ok : forall a v0 v,
      {{ F,
         | PRE d m s: d |= F * a |-> v0;
         | POST d' m' s' _: d' |= F * a |-> v; /\
                                               s' = s /\
                                               m' = m
      }} Write a v.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - match goal with
      | [ H: ~ exists st' p', step _ _ _ _ |- _] =>
        apply write_failure in H
      end.
      match goal with
      | [ H: context[ptsto a  _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Theorem read_ok : forall a v0,
    {{ F,
      | PRE d m s: d |= F * a |-> v0;
       | POST d' m' s' v: d' |= F * a |-> v0; /\
                       v = v0 /\
                       s' = s /\
                       m' = m
    }} Read a.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
      assert (d a = Some v0).
      eapply ptsto_valid; eauto.
      pred_apply; cancel.
      congruence.
    - match goal with
      | [ H: ~ exists st' p', step _ _ _ _ |- _ ] =>
        apply read_failure in H
      end.
      match goal with
      | [ H: context[ptsto a _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Ltac sigT_eq :=
    match goal with
    | [ H: @eq (sigT _) _ _ |- _ ] =>
      apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
        subst
    end.

  Theorem get_ok : forall t (v: var t),
      {{ F,
       | PRE d m s: d |= F;
       | POST d' m' s' r: d' |= F; /\
                                  r = get m v /\
                                  m' = m /\
                                  s' = s
      }} Get v.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post; eauto.
      repeat sigT_eq.
      eauto.
    - contradiction H; eauto.
  Qed.

  Theorem assgn_ok : forall t (v: var t) val,
      {{ F,
       | PRE d m s: d |= F;
       | POST d' m' s' _: d' |= F; /\
                                  m' = set m val v /\
                                  s' = s
      }} Assgn v val.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post; eauto.
      repeat sigT_eq.
      eauto.
    - contradiction H; eauto.
  Qed.

  Theorem yield_ok :
    {{ (_:unit),
      | PRE d m s: d |= StateI s;
      | POST d' m' s' _: d' |= StateI s'; /\
                                           star StateR s s' /\
                                           m' = m
    }} Yield.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
    - contradiction H; eauto.
  Qed.

  Theorem commit_ok : forall up,
    {{ F,
     | PRE d m s: d |= F;
       /\ StateR s (up s)
       /\ (F =p=> StateI (up s))
     | POST d' m' s' _: d' |= F;
       /\ s' = up s
       /\ m' = m
    }} Commit up.
  Proof.
    intros_pre.
    ind_exec.
    - prove_rx; simpl_post.
    - contradiction H0; eauto 10.
  Qed.

  Theorem pimpl_ok : forall (pre pre': _ -> _ -> _ -> _ -> Prop) p,
      valid pre p ->
      (forall done d m s, pre' done d m s -> pre done d m s) ->
      valid pre' p.
  Proof.
    unfold valid.
    intros.
    match goal with
    | [ H: context[?pre _ _ _ _ -> _], H1: ?pre _ _ _ _ |- _ ] =>
      apply H in H1
    end.
    eauto.
  Qed.

End EventCSL.

(** transitions defines a transition system, grouping the StateR and StateI
variables above.

This makes the notation more convenient, since R and I can be specified in one
ident.
*)
Record transitions S := {
      (* StateR s s' holds when s -> s' is a valid transition *)
      StateR: S -> S -> Prop;
      (* StateI s d holds when s is a valid state and represents the memory d *)
      StateI: S -> @pred addr (@weq addrlen) valu
      }.

(** Copy-paste metaprogramming:

* Copy the above notation
* add sigma |- in front to specify the transition system
* quantify over T and change prog to prog T _ (the state type should be inferred)
* add (StateR sigma) (StateI sigma) as arguments to valid *)
Notation "sigma |- {{ e1 .. e2 , | 'PRE' d m s : pre | 'POST' d' m' s' r : post }} p" :=
  (forall T (rx: _ -> prog _ _ T),
      valid (StateR sigma) (StateI sigma)
            (fun done d m s =>
               (ex (fun e1 => .. (ex (fun e2 =>
                                     pre%judgement /\
                                     forall ret_,
                                       valid (StateR sigma) (StateI sigma)
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

(* maximally insert the return/state types for Yield, which is always called
   without applying it to any arguments *)
Arguments Yield {Mcontents} {S} {T} rx.

(** This notation is intended to produce the patterns for prog hints.

The ; _ is merely a visual indicator that the pattern applies to any Hoare
statement beginning with f and followed by anything else. *)
Notation "{{ f ; '_' }}" := (valid _ _ _ (progseq f _)).

Hint Extern 1 {{ Read _; _ }} => apply read_ok : prog.
Hint Extern 1 {{ Write _ _; _ }} => apply write_ok : prog.
Hint Extern 1 {{ Get _; _ }} => apply get_ok : prog.
Hint Extern 1 {{ Assgn _ _; _ }} => apply assgn_ok : prog.
Hint Extern 1 {{ Yield; _ }} => apply yield_ok : prog.
Hint Extern 1 {{ Commit _; _ }} => apply commit_ok : prog.
