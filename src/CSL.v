Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import Word.

Import List.
Import List.ListNotations.

Open Scope list.

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

  Inductive cexec : state -> cprog -> list exec_label -> coutcome -> Prop :=
  | EStepRead : forall m ls a v rx events out,
      m a = Some v ->
      cexec (State m ls) (rx v) events out ->
      cexec (State m ls) (CRead a rx) events out
  | EReadFail : forall m a ls rx events,
      m a = None ->
      cexec (State m ls) (CRead a rx) events (Failed)
  | EStepWrite : forall m ls a v0 v rx events out,
      m a = v0 ->
      cexec (State (upd m a v) ls) (rx tt) events out ->
      cexec (State m ls) (CWrite a v rx) events out
  | EWriteFail : forall m a v ls rx events,
      m a = None ->
      cexec (State m ls) (CWrite a v rx) events (Failed)
  | EStepAcq : forall m rm ls r rx events out,
      mem_disjoint m rm ->
      cexec (State (mem_union m rm) (r::ls)) (rx tt)
            events out ->
      cexec (State m ls) (Acq r rx)
            (AcqStep r rm::events) out
  | EStepRel : forall m m' rm ls r rx events out,
      mem_disjoint m' rm ->
      m = mem_union m' rm ->
      cexec (State m (remove REQ r ls)) (rx tt)
            events out ->
      cexec (State m ls) (Rel r rx)
            (RelStep r rm::events) out
  | EDone : forall m ls v events,
      cexec (State m ls) (CDone v)
            events (Finished m v).

  Definition donecond :=  T -> @pred addr (@weq addrlen) valu.

  Definition context := list (R * @pred addr (@weq addrlen) valu).

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

  Notation "m |= p" := (p%pred m) (at level 90).

  Definition valid gamma (pre: forall (done:donecond),
                             pred)
             (p:cprog) : Prop :=
    forall m d events out,
      m |= pre d * inv gamma ->
      (forall r rm, In (AcqStep r rm) events ->
               rm |= rinv r gamma) ->
      cexec (State m nil) p events out ->
      (forall r rm, In (RelStep r rm) events ->
               rm |= rinv r gamma) /\
      (exists md v, out = Finished md v /\
              (md |= d v * inv gamma)).

End ConcurrentSepLogic.

Close Scope list.