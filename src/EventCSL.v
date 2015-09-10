Require Import Mem.
Require Import Pred.
Require Import Word.
Require Import SepAuto.

(* defined in Prog. which we don't want to import here *)
Definition addrlen := 64.
Notation "'addr'" := (word addrlen).
Notation "'valu'" := (word 64).

Set Implicit Arguments.

Section EventCSL.
  Set Default Proof Using "Type".

  Implicit Type m : @mem addr (@weq addrlen) valu.

  (** Our programs will return values of type T *)
  Variable T:Type.

  (** Yield will respect this invariant. *)
  Variable Inv : @pred addr (@weq addrlen) valu.
  Axiom InvDec : forall m, {Inv m} + {~ Inv m}.

  Inductive prog :=
  | Read (a: addr) (rx: valu -> prog)
  | Write (a: addr) (v: valu) (rx: unit -> prog)
  | Yield (rx: unit -> prog)
  | Done (v: T).

  Ltac ind_prog :=
    match goal with
    | [ H: @eq prog _ _ |- _ ] =>
      inversion H
    end.

  Implicit Type p : prog.

  Inductive step : forall m p m' p', Prop :=
  | StepRead : forall m a rx v, m a = Some v ->
                           step m (Read a rx) m (rx v)
  | StepWrite : forall m a rx v v', m a = Some v ->
                               step m (Write a v' rx) (upd m a v') (rx tt)
  | StepYield : forall m m' rx,
      Inv m ->
      Inv m' ->
      step m (Yield rx) m' (rx tt).

  Hint Constructors step.

  Ltac inv_step :=
    match goal with
    | [ H: step _ _ _ _ |- _ ] =>
      inversion H; subst
    end.

  Inductive outcome :=
  | Failed
  | Finished m (v:T).

  Inductive exec : forall m p (out:outcome), Prop :=
  | ExecStep : forall m p m' p' out,
      step m p m' p' ->
      exec m' p' out ->
      exec m p out
  | ExecFail : forall m p,
      (~ exists m' p', step m p m' p') ->
      (forall v, p <> Done v) ->
      exec m p Failed
  | ExecDone : forall m v,
      exec m (Done v) (Finished m v).

  Hint Constructors exec.

  Ltac invalid_address :=
    match goal with
    | [ H: ~ exists m' p', step _ _ _ _ |- ?m ?a = None ] =>
      case_eq (m a); auto; intros;
      contradiction H;
      eauto
    end.

  Ltac no_step :=
    match goal with
    | [  |- ~ exists m' p', step _ _ _ _ ] =>
      let Hcontra := fresh in
      intro Hcontra;
        do 2 deex;
        inversion Hcontra; congruence
    end.

  Ltac address_failure :=
    intros; split; intros;
    try invalid_address;
    try no_step.

  Theorem read_failure_iff : forall m rx a,
      (~ exists m' p', step m (Read a rx) m' p') <->
      m a = None.
  Proof.
    address_failure.
  Qed.

  Theorem read_failure : forall m rx a,
      (~ exists m' p', step m (Read a rx) m' p') ->
      m a = None.
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem read_failure' : forall m rx a,
      m a = None ->
      (~ exists m' p', step m (Read a rx) m' p').
  Proof.
    apply read_failure_iff.
  Qed.

  Theorem write_failure_iff : forall m v rx a,
      (~ exists m' p', step m (Write a v rx) m' p') <->
      m a = None.
  Proof.
    address_failure.
  Qed.

  Theorem write_failure : forall m v rx a,
      (~ exists m' p', step m (Write a v rx) m' p') ->
      m a = None.
  Proof.
    apply write_failure_iff.
  Qed.

  Theorem write_failure' : forall m v rx a,
      m a = None ->
      (~ exists m' p', step m (Write a v rx) m' p').
  Proof.
    apply write_failure_iff.
  Qed.

  Theorem yield_failure : forall m rx,
      (~ exists m' p', step m (Yield rx) m' p') ->
      (~Inv m).
  Proof.
    intros.
    intro.
    eauto.
  Qed.

  Theorem yield_failure' : forall m rx,
      (~Inv m) ->
      (~ exists m' p', step m (Yield rx) m' p').
  Proof.
    intros.
    intro.
    repeat deex.
    inv_step.
    congruence.
  Qed.

  Theorem exec_progress : forall p m,
      exists out, exec m p out.
  Proof.

    Ltac rx_specialize new_mem :=
      match goal with
      | [ H : forall w:?t, forall _, exists out, exec _ _ out |- _ ] =>
        match t with
        | unit => specialize (H tt new_mem); inversion H
        | _ => match goal with
              | [ _ : _ _ = Some ?w |- _ ] =>
                specialize (H w new_mem); inversion H
              end
        end
      end.

    Hint Resolve read_failure'.
    Hint Resolve write_failure'.
    Hint Resolve yield_failure'.

    induction p; intros.
    - case_eq (m a); intros.
      rx_specialize m; eexists; eauto.
      eexists; eapply ExecFail; eauto; try congruence.
    - case_eq (m a); intros.
      rx_specialize (upd m a v); eexists; eauto.
      eexists; eapply ExecFail; eauto; try congruence.
    - rx_specialize m.
      destruct (InvDec m); intros.
      eexists; eapply ExecStep; eauto.
      eexists; eapply ExecFail; eauto; try congruence.
    - eauto.
  Qed.

  Definition donecond := T -> @pred addr (@weq addrlen) valu.

  Definition valid (pre: donecond -> pred) p : Prop :=
    forall m d out,
      pre d m ->
      exec m p out ->
      exists m' v,
        out = Finished m' v /\
        d v m'.

  Notation "'RET' : r post" :=
  (fun F =>
    (fun r => (F * post)%pred)
  )%pred
  (at level 0, post at level 90, r at level 0, only parsing).

  Notation "{{ e1 .. e2 , | 'PRE' pre | 'POST' post }} p" :=
    (forall (rx: _ -> prog),
        valid (fun done =>
                 (exis (fun e1 => .. (exis (fun e2 =>
                                           (pre%pred *
                                            [[ forall ret_,
                                                 valid (fun done_rx =>
                                                          post emp ret_ *
                                                          [[ done_rx = done ]])
                                                       (rx ret_)
                                           ]])%pred )) .. ))
              ) (p rx))
      (at level 0, p at level 60,
       e1 binder, e2 binder,
       only parsing).

  Definition progseq (A:Type) (p1 : prog -> A) (p2: prog) := p1 p2.

  Notation "p1 ;; p2" := (progseq p1 (fun _:unit => p2))
                           (at level 60, right associativity).
  Notation "x <- p1 ;; p2" := (progseq p1 (fun x => p2 x))
                                (at level 60, right associativity).

  Ltac ind_exec :=
    match goal with
    | [ H : exec _ ?p _ |- _ ] =>
      remember p;
        induction H; subst;
        try inv_step;
        try ind_prog
    end.

  Theorem write_ok : forall a v0 v,
      {{ F,
         | PRE F * a |-> v0
         | POST RET:_ F * a |-> v
      }} Write a v.
  Proof.
    unfold valid; intros.
    destruct_lift H.
    ind_exec.
    - edestruct H3; eauto.
      eapply pimpl_apply.
      cancel.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - match goal with
      | [ H: ~ exists m' p', step _ _ _ _ |- _] =>
        apply write_failure in H
      end.
      match goal with
      | [ H: context[ptsto a  _] |- _ ] =>
        apply ptsto_valid' in H
      end.
      congruence.
  Qed.

  Theorem yield_ok :
    {{ (_:unit),
      | PRE Inv
      | POST RET:_ Inv
    }} Yield.
  Proof.
    unfold valid; intros.
    destruct_lift H.
    ind_exec.
    - edestruct H3; eauto.
      eapply pimpl_apply; [cancel | auto].
    - eapply yield_failure in H0.
      congruence.
  Qed.

  Theorem pimpl_ok : forall pre pre' p,
      (forall d, pre' d =p=> pre d) ->
      valid pre p ->
      valid pre' p.
  Proof.
    unfold valid.
    intros.
    apply H in H1.
    eauto.
  Qed.

  Theorem yield_ok' :
    {{ F,
     | PRE F * [[ F =p=> Inv ]]
     | POST RET:_ Inv
    }} Yield.
  Proof.
    intros.
    eapply pimpl_ok; [| apply yield_ok].
    cancel.
    auto.

    Grab Existential Variables.
    auto.
  Qed.

End EventCSL.