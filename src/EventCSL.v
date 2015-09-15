Require Import Mem.
Require Import Pred.
Require Import Word.
Require Import Omega.
Require Import SepAuto.

(* defined in Prog. which we don't want to import here *)
Definition addrlen := 64.
Definition valulen := 64.
Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word valulen).

Set Implicit Arguments.

Section EventCSL.
  Set Default Proof Using "Type".

  Implicit Type m : @mem addr (@weq addrlen) valu.

  (** Our programs will return values of type T *)
  Variable T:Type.

  (** Programs can manipulate ghost state of type S *)
  Variable S:Type.

  (** Yield will respect this invariant. *)
  Variable Inv : @pred addr (@weq addrlen) valu.

  (** Define the transition system for the ghost state.
      The semantics will reject transitions that do not obey these rules. *)
  Variable StateR : S -> S -> Prop.
  Variable StateI : S -> @pred addr (@weq addrlen) valu.

  Axiom InvDec : forall m, {Inv m} + {~ Inv m}.
  Axiom StateStutter : forall s m, StateI s m -> StateR s s.

  Inductive prog :=
  | Read (a: addr) (rx: valu -> prog)
  | Write (a: addr) (v: valu) (rx: unit -> prog)
  | Yield (rx: unit -> prog)
  | Commit (up: S -> S) (rx: unit -> prog)
  | Done (v: T).

  Ltac ind_prog :=
    match goal with
    | [ H: @eq prog _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type p : prog.

  Inductive step : forall m s p m' s' p', Prop :=
  | StepRead : forall m s a rx v, m a = Some v ->
                           step m s (Read a rx) m s (rx v)
  | StepWrite : forall m s a rx v v', m a = Some v ->
                               step m s (Write a v' rx) (upd m a v') s (rx tt)
  | StepYield : forall m s m' rx,
      StateI s m ->
      Inv m ->
      StateI s m' ->
      Inv m' ->
      step m s (Yield rx) m' s (rx tt)
  | StepCommit : forall m s up rx,
      StateR s (up s) ->
      StateI s m ->
      step m s (Commit up rx) m (up s) (rx tt).

  Hint Constructors step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Inductive outcome :=
  | Failed
  | Finished m (v:T).

  Inductive exec : forall m s p (out:outcome), Prop :=
  | ExecStep : forall m s p m' s' p' out,
      step m s p m' s' p' ->
      exec m' s' p' out ->
      exec m s p out
  | ExecFail : forall m s p,
      (~ exists m' s' p', step m s p m' s' p') ->
      (forall v, p <> Done v) ->
      exec m s p Failed
  | ExecDone : forall m s v,
      exec m s (Done v) (Finished m v).

  Hint Constructors exec.

  Ltac invalid_address :=
    match goal with
    | [ H: ~ exists m' s' p', step _ _ _ _ _ _ |- ?m ?a = None ] =>
      case_eq (m a); auto; intros;
      contradiction H;
      eauto
    end.

  Ltac no_step :=
    match goal with
    | [  |- ~ exists m' s' p', step _ _ _ _ _ _ ] =>
      let Hcontra := fresh in
      intro Hcontra;
        do 3 deex;
        inversion Hcontra; congruence
    end.

  Ltac address_failure :=
    intros; split; intros;
    try invalid_address;
    try no_step.

  Theorem read_failure_iff : forall m s rx a,
      (~ exists m' s' p', step m s (Read a rx) m' s' p') <->
      m a = None.
  Proof.
    address_failure.
  Qed.

  Theorem read_failure : forall m s rx a,
      (~ exists m' s' p', step m s (Read a rx) m' s' p') ->
      m a = None.
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem read_failure' : forall m s rx a,
      m a = None ->
      (~ exists m' s' p', step m s (Read a rx) m' s' p').
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem write_failure_iff : forall m s v rx a,
      (~ exists m' s' p', step m s (Write a v rx) m' s' p') <->
      m a = None.
  Proof.
    address_failure.
  Qed.

  Theorem write_failure : forall m s v rx a,
      (~ exists m' s' p', step m s (Write a v rx) m' s' p') ->
      m a = None.
  Proof.
    apply write_failure_iff.
  Qed.

  Theorem write_failure' : forall m s v rx a,
      m a = None ->
      (~ exists m' s' p', step m s (Write a v rx) m' s' p').
  Proof.
    apply write_failure_iff.
  Qed.

  Ltac not_sidecondition_fail :=
    intros; intro Hcontra;
    repeat deex;
    inv_step;
    congruence.

  Theorem yield_failure'_inv : forall m s rx,
      (~Inv m) ->
      (~ exists m' s' p', step m s (Yield rx) m' s' p').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem yield_failure'_state_inv : forall m s rx,
      (~StateI s m) ->
      (~ exists m' s' p', step m s (Yield rx) m' s' p').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure'_inv : forall m s up rx,
    (~StateI s m) ->
    (~ exists m' s' p', step m s (Commit up rx) m' s' p').
  Proof.
    not_sidecondition_fail.
  Qed.

  Theorem commit_failure'_rel : forall m s up rx,
    (~StateR s (up s)) ->
    (~ exists m' s' p', step m s (Commit up rx) m' s' p').
  Proof.
    not_sidecondition_fail.
  Qed.

  Hint Extern 2 (forall v, _ <> Done v) => intro; congruence.

  Theorem exec_progress :
      forall (StateI_dec: forall s m, {StateI s m} + {~StateI s m}),
      forall (StateR_dec: forall s s', {StateR s s'} + {~StateR s s'}),
      forall p m s,
      exists out, exec m s p out.
  Proof.

    Ltac rx_specialize new_mem new_s :=
      match goal with
      | [ H : forall w:?t, forall _ _, exists out, exec _ _ _ out |- _ ] =>
        match t with
        | unit => specialize (H tt new_mem new_s); inversion H
        | _ => match goal with
              | [ _ : _ _ = Some ?w |- _ ] =>
                specialize (H w new_mem new_s); inversion H
              end
        end
      end.

    Hint Resolve read_failure'.
    Hint Resolve write_failure'.
    Hint Resolve yield_failure'_inv.
    Hint Resolve yield_failure'_state_inv.
    Hint Resolve commit_failure'_inv.
    Hint Resolve commit_failure'_rel.

    induction p; intros.
    - case_eq (m a); intros.
      rx_specialize m s.
      all: eauto 15.
    - case_eq (m a); intros.
      rx_specialize (upd m a v) s.
      all: eauto 15.
    - rx_specialize m s.
      destruct (InvDec m);
      destruct (StateI_dec s m); eauto.
    - case_eq (StateR_dec s (up s));
      case_eq (StateI_dec s m).
      rx_specialize m (up s).
      all: eauto 15.
    - eauto.
  Qed.

  Definition donecond := T -> @pred addr (@weq addrlen) valu.

  Definition valid (pre: donecond -> S -> pred) p : Prop :=
    forall m s d out,
      pre d s m ->
      exec m s p out ->
      exists m' v,
        out = Finished m' v /\
        d v m'.

  Notation "'RET' : r post" :=
  (fun F =>
    (fun r => (F * post)%pred)
  )%pred
  (at level 0, post at level 90, r at level 0, only parsing).

  Notation "{{ e1 .. e2 , | 'PRE' s1 : pre | 'POST' s2 : post }} p" :=
    (forall (rx: _ -> prog),
        valid (fun done s1 =>
                 (exis (fun e1 => .. (exis (fun e2 =>
                                           (pre%pred *
                                            [[ forall ret_,
                                                 valid (fun done_rx s2 =>
                                                          post emp ret_ *
                                                          [[ done_rx = done ]])
                                                       (rx ret_)
                                            ]])%pred)) .. ))
              ) (p rx))
      (at level 0, p at level 60,
       e1 binder, e2 binder,
       s1 at level 0,
       s2 at level 0,
       only parsing).

  (** Programs are written in continuation-passing style, where sequencing
  is simply function application. We wrap this sequencing in a function for
  automation purposes, so that we can recognize when logically instructions
  are being sequenced. B is a continuation, of the type (input -> prog), while
  A is the type of the whole expression, (output -> prog). *)
  Definition progseq (A B:Type) (p1 : B -> A) (p2: B) := p1 p2.

  Ltac ind_exec :=
    match goal with
    | [ H : exec _ _ ?p _ |- _ ] =>
      remember p;
        induction H; subst;
        try inv_step;
        try ind_prog
    end.

  Ltac prove_rx :=
    match goal with
    | [ H: forall _, valid _ _ |- _ ] =>
      edestruct H; eauto
    end.

  Theorem write_ok : forall a v0 v,
      {{ F s0,
         | PRE s: F * a |-> v0 * [[ s = s0 ]]
         | POST s: RET:_ F * a |-> v * [[ s = s0 ]]
      }} Write a v.
  Proof.
    unfold valid at 1; intros.
    destruct_lift H.
    ind_exec.
    - prove_rx.
      eapply pimpl_apply.
      cancel.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - match goal with
      | [ H: ~ exists m' s' p', step _ _ _ _ _ _ |- _] =>
        apply write_failure in H
      end.
      match goal with
      | [ H: context[ptsto a  _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Theorem read_ok : forall a v0,
    {{ F s0,
      | PRE s: F * a |-> v0 * [[ s = s0 ]]
      | POST s: RET:v F * a |-> v0 * [[ v = v0 ]] * [[ s = s0 ]]
    }} Read a.
  Proof.
    unfold valid at 1; intros.
    destruct_lift H.
    ind_exec.
    - prove_rx.
      pred_apply; cancel.
      assert (m' a = Some v0).
      eapply ptsto_valid; eauto.
      pred_apply; cancel.
      congruence.
    - match goal with
      | [ H: ~ exists m' s' p', step _ _ _ _ _ _ |- _ ] =>
        apply read_failure in H
      end.
      match goal with
      | [ H: context[ptsto a _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Theorem yield_ok :
    {{ s0,
      | PRE s: and (Inv * [[ s = s0 ]]) (StateI s)
      | POST s : RET:_ and (Inv * [[ s = s0 ]]) (StateI s)
    }} Yield.
  Proof.
    unfold valid at 1; intros.
    destruct_lift H.
    destruct_and H.
    destruct_lift H1.
    ind_exec.
    - prove_rx.
      simpl.
      eapply pimpl_apply; [cancel | auto].
      split; auto.
      pred_apply; cancel.
    - contradiction H0; eauto.
  Qed.

  Theorem pimpl_ok : forall pre pre' p,
      valid pre p ->
      (forall d s, pre' d s =p=> pre d s) ->
      valid pre' p.
  Proof.
    unfold valid.
    intros.
    apply H0 in H1.
    eauto.
  Qed.

End EventCSL.

(* FIXME: these notations are needed both inside and outside the EventCSL
   section, resulting in duplication.

   The Hoare triple notation isn't quite the same because the invariant
   has to be passed explicitly rather than captured from the environment. *)
Notation "'RET' : r post" :=
(fun F =>
  (fun r => (F * post)%pred)
)%pred
(at level 0, post at level 90, r at level 0, only parsing).

(** transitions defines a transition system, which is nothing more than a
struct with the StateR relation and StateI state invariant variables used
above.

This makes the notation more convenient, since R and I can be grouped together.
*)
Inductive transitions S :=
  | Transitions
      (* StateR s s' holds when s -> s' is a valid transition *)
      (StateR: S -> S -> Prop)
      (* StateI s m holds when s is a valid state and represents the memory m *)
      (StateI: S -> @pred addr (@weq addrlen) valu).

(* projection functions for transitions *)
Definition transition_r S (sigma: transitions S) :=
  match sigma with
  | Transitions StateR _ => StateR
  end.

Definition transition_i S (sigma: transitions S) :=
  match sigma with
  | Transitions _ StateI => StateI
  end.

(** Copy-paste metaprogramming:

* Copy the above notation
* add gamma, sigma |- in front to specify the invariant/transition system
* quantify over T and change prog to prog T _ (the state type should be inferred)
* add gamma (transition_r sigma) (transition_i sigma) as arguments to valid
    (you'll need %pred on the outer valid due to scope stacks) *)
Notation "gamma , sigma |- {{ e1 .. e2 , | 'PRE' s1 : pre | 'POST' s2 : post }} p" :=
  (forall T (rx: _ -> prog T _),
      valid gamma (transition_r sigma%pred) (transition_i sigma%pred) (fun done s1 =>
               (exis (fun e1 => .. (exis (fun e2 =>
                                         (pre%pred *
                                          [[ forall ret_,
                                               valid gamma (transition_r sigma) (transition_i sigma) (fun done_rx s2 =>
                                                        post emp ret_ *
                                                        [[ done_rx = done ]])
                                                     (rx ret_)
                                          ]])%pred)) .. ))
            ) (p rx))
    (at level 0, p at level 60,
     e1 binder, e2 binder,
     s1 at level 0,
     s2 at level 0,
     only parsing).

Notation "p1 ;; p2" := (progseq p1 (fun _:unit => p2))
                         (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq p1 (fun x => p2))
                              (at level 60, right associativity).

(* maximally insert the return/state types for Yield, which is always called
   without applying it to any arguments *)
Arguments Yield {T} {S} rx.

Hint Extern 1 (valid _ _ _ _ (progseq (Read _) _)) => apply read_ok : prog.
Hint Extern 1 (valid _ _ _ _ (progseq (Write _ _) _)) => apply write_ok : prog.
Hint Extern 1 (valid _ _ _ _ (progseq (Yield) _)) => apply yield_ok : prog.

Section Bank.
  Definition acct1 : addr := $0.
  Definition acct2 : addr := $1.

  Definition rep bal1 bal2 : @pred addr (@weq addrlen) valu :=
    acct1 |-> bal1 * acct2 |-> bal2.

  Definition inv_rep bal1 bal2 : pred :=
    rep bal1 bal2 *
    [[ #bal1 + #bal2 = 100 ]].

  Definition Inv : pred := (exists F bal1 bal2,
    F * inv_rep bal1 bal2)%pred.

  (** The bank transition system.

  Currently a fake system to illustrate the ideas, but will eventually
  represent a ledger that is read-only and sums up to the current balances.
   *)
  Definition State := nat.

  Definition bankR n1 n2 := n2 > n1.
  Definition bankI n := n > 5.

  Definition bankS : transitions State :=
    Transitions bankR (fun n => lift (bankI n)).

  Local Hint Unfold rep inv_rep Inv bankI : prog.

  Lemma max_balance : forall bal1 bal2,
    (exists F, F * inv_rep bal1 bal2) =p=>
    (exists F, F * inv_rep bal1 bal2) *
    [[ #bal1 <= 100 ]] *
    [[ #bal2 <= 100 ]].
  Proof.
    unfold inv_rep, rep.
    intros.
    intros m H.
    pred_apply; cancel.
  Qed.

  Definition transfer {T S} rx : prog T S :=
    bal1 <- Read acct1;
    bal2 <- Read acct2;
    Write acct1 (bal1 ^- $1);;
    Write acct2 (bal2 ^+ $1);;
    rx tt.

  Ltac step :=
    repeat (autounfold with prog);
    eapply pimpl_ok; [ auto with prog | ];
    repeat (autounfold with prog);
    try cancel;
    eauto.

  Ltac hoare := intros; repeat step.

  Theorem transfer_ok : forall bal1 bal2,
    Inv, bankS |-
    {{ F s0,
      | PRE s: F * rep bal1 bal2 * [[ s = s0 ]]
      | POST s: RET:_ F * rep (bal1 ^- $1) (bal2 ^+ $1) * [[ s = s0 ]]
    }} transfer.
  Proof.
    unfold transfer.
    hoare.
  Qed.

  Hint Extern 1 (valid _ _ _ _ (progseq (transfer) _)) => apply transfer_ok : prog.

  Definition transfer_yield {T} rx : prog T State :=
    transfer;; Yield;; rx tt.

  Lemma inv_transfer_stable : forall (bal1 bal2 : valu),
    #bal1 + #bal2 = 100 ->
    #bal1 > 0 ->
    # (bal1 ^- $1) + # (bal2 ^+ $1) = 100.
  Proof.
    intros.
    rewrite wordToNat_minus_one.
    erewrite wordToNat_plusone.
    omega.
    apply lt_wlt.
    instantiate (1 := $101).
    simpl; omega.
    apply gt0_wneq0; auto.
  Qed.

  Lemma pimpl_and_l : forall AT AEQ V (p q r: @pred AT AEQ V),
    p =p=> r -> p /\ q =p=> r.
  Proof.
    firstorder.
  Qed.

  Hint Extern 4 (pimpl _ (and _ _)) => apply pimpl_and_split; try cancel.

  Theorem transfer_yield_ok : forall bal1 bal2,
    Inv, bankS |-
    {{ F,
      | PRE s: F * inv_rep bal1 bal2 *
           [[ #bal1 > 0 ]] * [[ bankI s ]]
      | POST s: RET:_ Inv * [[ bankI s ]]
    }} transfer_yield.
  Proof.
    Local Hint Resolve inv_transfer_stable.
    unfold transfer_yield.
    intros.
    step.
    step.
    eapply pimpl_ok; [ auto with prog | ].
    autounfold with prog.
    intros.
    apply sep_star_lift_l; intros.
    rewrite star_emp_pimpl.
    (* cancel doesn't do this, although it could, if it handled and better *)
    apply pimpl_and_l.
    cancel.
  Qed.

End Bank.