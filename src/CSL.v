Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import Word.
Require Import Hoare.
Require Import SepAuto.

Import List.

Infix "::" := cons.

Set Implicit Arguments.

Section ConcurrentSepLogic.

  (** Resources will have names from this set. *)
  Variable R : Set.
  (** R must have decidable equality. *)
  Variable REQ : forall a b:R, {a = b} + {a <> b}.
  (** We will define programs that return T. *)
  Variable T:Type.

  Implicit Types r : R.
  Implicit Types m rm : @mem addr (@weq addrlen) valu.

  Inductive state :=
  | State : forall m (locks: list R), state.

  Inductive exec_label :=
  | AcqStep : forall r rm, exec_label
  | RelStep : forall r rm, exec_label.

  Inductive cprog :=
  | CDone (v: T)
  | CRead (a: addr) (rx: valu -> cprog)
  | CWrite (a: addr) (v: valu) (rx: unit -> cprog)
  | Acq r (rx: unit -> cprog)
  | Rel r (rx: unit -> cprog).

  Inductive coutcome :=
  | Finished : forall m, T -> coutcome
  | Failed.

  Inductive rexec : state -> cprog -> list exec_label -> coutcome -> Prop :=
  | EStepRead : forall m ls a v rx events out,
      m a = Some v ->
      rexec (State m ls) (rx v) events out ->
      rexec (State m ls) (CRead a rx) events out
  | EReadFail : forall m a ls rx events,
      m a = None ->
      rexec (State m ls) (CRead a rx) events (Failed)
  | EStepWrite : forall m ls a v0 v rx events out,
      m a = v0 ->
      rexec (State (upd m a v) ls) (rx tt) events out ->
      rexec (State m ls) (CWrite a v rx) events out
  | EWriteFail : forall m a v ls rx events,
      m a = None ->
      rexec (State m ls) (CWrite a v rx) events (Failed)
  | EStepAcq : forall m rm ls r rx events out,
      mem_disjoint m rm ->
      rexec (State (mem_union m rm) (r::ls)) (rx tt)
            events out ->
      rexec (State m ls) (Acq r rx)
            (AcqStep r rm::events) out
  | EStepRel : forall m m' rm ls r rx events out,
      mem_disjoint m' rm ->
      m = mem_union m' rm ->
      rexec (State m (remove REQ r ls)) (rx tt)
            events out ->
      rexec (State m ls) (Rel r rx)
            (RelStep r rm::events) out
  | EDone : forall m ls v events,
      rexec (State m ls) (CDone v)
            events (Finished m v).

  Definition donecond :=  T -> @pred addr (@weq addrlen) valu.

  Definition context := list (R * @pred addr (@weq addrlen) valu).

  Notation "r : p" := (r, p%pred) (at level 30) : context_scope.
  Delimit Scope context_scope with context.

  Notation "[G ri1 , .. , ri2 G]" :=
    (cons ri1%context .. (cons ri2%context nil) ..)
      (at level 0) : context_scope.

  Notation "[G]" := (nil (A := R * @pred addr (@weq addrlen) valu)) (at level 60) : context_scope.


  Fixpoint inv (gamma:context) :=
    match gamma with
    | nil => emp
    | (_, Ri) :: gamma' => (Ri * inv gamma')%pred
    end.

  Fixpoint rinv r (gamma:context) : pred :=
    match gamma with
    | nil => emp
    | (r', Ri) :: gamma' =>
      if REQ r r' then Ri else rinv r gamma'
    end.

  Notation "m |= p" := (p%pred m) (at level 90, only parsing).

  Definition valid gamma (pre: forall (done:donecond),
                             pred)
             (p:cprog) : Prop :=
    forall m d ls events out,
      m |= pre d * inv gamma ->
      (forall r rm, In (AcqStep r rm) events ->
               rm |= rinv r gamma) ->
      rexec (State m ls) p events out ->
      (forall r rm, In (RelStep r rm) events ->
               rm |= rinv r gamma) /\
      (exists md v, out = Finished md v /\
              (md |= d v * inv gamma)).

  Notation "gamma |- {{ e1 .. e2 , 'PRE' pre 'POST' post }} p" :=
    (forall (rx: _ -> cprog),
        valid gamma%context%pred
              (fun done =>
                 (exis (fun e1 => .. (exis (fun e2 =>
                                          (pre%pred *
                                          [[ forall ret_,
                                               valid gamma%context
                                                     (fun done_rx =>
                                                        post emp ret_ *
                                                        [[ done_rx = done ]])
                                                     (rx ret_)
                                          ]])%pred )) .. ))
              ) (p rx))
   (at level 0, p at level 60,
    e1 binder, e2 binder,
    only parsing).

  Ltac inv_cprog :=
    match goal with
    | [ H: @eq cprog ?a ?b |- _ ] =>
      inversion H; subst; clear H
    end.

  Ltac inv_state :=
    match goal with
    | [ H: @eq state ?a ?b |- _ ] =>
      inversion H; subst; clear H
    end.

  (** Save an equality to a non-variable expression so induction on an expression preserves
      information. *)
  Ltac remember_nonvar a :=
    (is_var a || remember a).

  Ltac inv_rexec :=
    match goal with
    | [ H : rexec ?s ?c _ _ |- _ ] =>
      remember_nonvar s;
        remember_nonvar c;
        induction H; inv_cprog; inv_state
    end.

  Theorem write_cok : forall a v,
      [G] |- {{ F v0,
               PRE F * a |-> v0
               POST RET:_ F * a |-> v
            }} CWrite a v.
  Proof.
    unfold valid.
    intros.
    destruct_lift H.
    inv_rexec.
    - edestruct H5; eauto.
      eapply pimpl_apply; [| eapply ptsto_upd].
      cancel.
      pred_apply; cancel.
    - assert (m a = Some v2).
      eapply ptsto_valid; pred_apply; cancel.
      congruence.
  Qed.

  Theorem read_cok : forall a,
      [G] |- {{ F v0,
               PRE F * a |-> v0
               POST RET:_ F * a |-> v0
            }} CRead a.
  Proof.
    unfold valid.
    intros.
    destruct_lift H.
    inv_rexec.
    - edestruct H5; eauto.
      pred_apply; cancel.
    - assert (m a = Some v1).
      eapply ptsto_valid; pred_apply; cancel.
      congruence.
  Qed.

End ConcurrentSepLogic.
