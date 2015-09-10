Require Import Mem.
Require Import Pred.
Require Import Word.

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
      (~Inv m) ->
      (~ exists m' p', step m (Yield rx) m' p').
  Proof.
    intros.
    intro.
    repeat deex.
    match goal with
    | [ H: step _ _ _ _ |- _ ] =>
      inversion H
    end.
    congruence.
  Qed.

  Theorem exec_progress : forall m p,
      exists out, exec m p out.
  Proof.

    Ltac rx_specialize new_mem :=
      match goal with
      | [ H : forall w:?t, forall _, exists out, exec _ (_ w) out |- _ ] =>
        match t with
        | unit => specialize (H tt new_mem); inversion H
        | _ => match goal with
              | [ _ : _ _ = Some ?w |- _ ] =>
                specialize (H w new_mem); inversion H
              end
        end
      end.

    Hint Resolve read_failure.
    Hint Resolve read_failure'.
    Hint Resolve write_failure.
    Hint Resolve write_failure'.
    Hint Resolve yield_failure.

    intros.
    generalize dependent m.
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
