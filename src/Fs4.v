Require Import List.
Require Import CpdtTactics.
Import ListNotations.

(* File system state *)
Definition state := nat.

(* Initial state *)
Definition IS : state := 0.

(* Definition of event and trace. 
 * Note that this definition treats histories "backwards": writing and then
 * reading a file is represented by: (Read 1) :: (Write 1) :: nil.
 *)

Inductive event : Set :=
  | Read: state -> event
  | Write: state -> event
  | Sync: event
  | Crash: event.

Definition trace := list event.

Inductive last_write_since_crash : trace -> state -> Prop :=
  | last_write_read:  forall (t:trace) (s rs:state),
    last_write_since_crash t s -> last_write_since_crash ((Read rs) :: t) s
  | last_write_sync:  forall (t:trace) (s:state),
    last_write_since_crash t s -> last_write_since_crash (Sync :: t) s
  | last_write_write: forall (t:trace) (s:state),
    last_write_since_crash ((Write s) :: t) s.

Definition no_write_since_crash (t:trace) : Prop :=
  ~ exists (s:state), last_write_since_crash t s.

Inductive could_persist : trace -> state -> Prop :=
  | persist_nil:
    could_persist nil IS
  | persist_write:       forall (t:trace) (s:state),
    could_persist ((Write s) :: t) s
  | persist_read:        forall (t:trace) (s:state),
    no_write_since_crash t -> could_persist ((Read s) :: t) s
  | persist_sync:        forall (t:trace) (s:state),
    last_write_since_crash t s -> could_persist (Sync :: t) s
  | persist_crash_intro: forall (t:trace) (s:state),
    could_persist t s -> could_persist (Crash :: t) s
  | persist_write_intro: forall (t:trace) (s ws:state),
    could_persist t s -> could_persist ((Write ws) :: t) s
  | persist_read_intro:  forall (t:trace) (s rs:state),
    last_write_since_crash t rs -> could_persist t s -> could_persist ((Read rs) :: t) s
  | persist_sync_intro:  forall (t:trace) (s:state),
    no_write_since_crash t -> could_persist t s -> could_persist (Sync :: t) s.

Inductive trace_legal : trace -> Prop :=
  | trace_legal_nil:
    trace_legal nil
  | trace_legal_sync_intro:       forall (t:trace),
    trace_legal t -> trace_legal (Sync :: t)
  | trace_legal_crash_intro:      forall (t:trace),
    trace_legal t -> trace_legal (Crash :: t)
  | trace_legal_write_intro:      forall (t:trace) (s:state),
    trace_legal t -> trace_legal ((Write s) :: t)
  | trace_legal_read_after_write: forall (t:trace) (s:state),
    last_write_since_crash t s -> trace_legal t -> trace_legal ((Read s) :: t)
  | trace_legal_read_after_crash: forall (t:trace) (s:state),
    no_write_since_crash t -> could_persist t s -> trace_legal t -> trace_legal ((Read s) :: t).

(* Testing *)

Ltac trace_resolve :=
  match goal with
  | |- no_write_since_crash ?T => 
        unfold no_write_since_crash; crush; inversion H
  | _ => constructor
  end.

Theorem test_1 : 
  trace_legal [ Read 1; Write 1; Read 0; Write 0; Sync; Read 1; Crash; Read 2; Write 2; Write 1 ] .
Proof.
  do 5 constructor.
  constructor 6;  repeat trace_resolve.
Qed.

Theorem test_2 :
  trace_legal [ Read 1; Crash; Read 3; Write 3; Crash; Write 2; Write 1 ] .
Proof.
  constructor 6; repeat trace_resolve.
Qed.

Theorem test_3:
  trace_legal [ Read 1; Crash; Read 3; Sync; Write 3; Crash; Write 2; Write 1 ].
Proof.
  constructor 6; repeat trace_resolve.
  Abort.

Theorem test_4:
  trace_legal [ Read 2; Crash; Read 3; Write 3; Read 1; Crash; Write 2 ; Write 1 ] .
Proof.
  constructor 6; repeat trace_resolve.
  Abort.

Theorem test_5:
  trace_legal [ Read 1; Read 2; Crash;  Write 1; Write 2 ].
Proof.
  constructor 6; repeat trace_resolve.
  Abort.

(* Some theorems *)

Theorem leagl_subtrace:
  forall (t:trace) (e:event),
  trace_legal (e :: t) -> trace_legal t.
Proof.
  intros.
  inversion H; crush.
Qed.

Lemma last_write_uniqueness:
  forall (t:trace) (a b:state),
  last_write_since_crash t a /\ last_write_since_crash t b -> a = b.
Proof.
  crush.
  induction H0; inversion H1; crush.
Qed.

Ltac write_contradict :=
  match goal with
  | H1: last_write_since_crash ?T ?s, 
    H2: no_write_since_crash ?T |- _ =>
      unfold no_write_since_crash in H2; destruct H2; exists s; assumption
  | H1: last_write_since_crash ?T ?a,
    H2: last_write_since_crash ?T ?b |- _ =>
      apply last_write_uniqueness with (t:=T); crush
  | _ => idtac
  end.

Theorem read_immutability:
  forall (t:trace) (a b: state),
  trace_legal ((Read a) :: (Read b) :: t) -> a = b.
Proof.
  intros.  inversion H.
  - inversion H3; inversion H2; write_contradict.
  - inversion H4.
    + apply last_write_read with (rs:=b) in H7;  write_contradict.
    + inversion H3; crush; write_contradict.
Qed.

