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

(* Some theorems *)

Theorem legal_subtrace:
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

Lemma write_complement:
  forall (t:trace),
  (exists (s:state), last_write_since_crash t s) \/ no_write_since_crash t.
Proof.
  induction t; unfold no_write_since_crash.
  - right. crush. inversion H.
  - unfold no_write_since_crash in IHt; destruct IHt; destruct a.
    + left. crush. exists x. constructor. assumption.
    + left. exists s. constructor.
    + left. crush. exists x. constructor. assumption.
    + right. crush. inversion H0.
    + right. crush. inversion H0. apply H. exists x. assumption.
    + left. exists s. constructor.
    + right. crush. inversion H0. apply H. exists x. assumption.
    + right. crush. inversion H0.
Qed.
 
Lemma sync_before_read_irrelevence:
  forall (t:trace) (s:state),
  trace_legal ((Read s) :: Sync :: t) -> trace_legal ((Read s) :: t).
Proof.
  intros. inversion H; inversion H3.
  - inversion H2.
    cut (trace_legal (Read s ::t)); crush. 
    apply trace_legal_read_after_write; crush.
  - destruct H2. exists s. constructor. assumption.
  - inversion H4. apply trace_legal_read_after_crash; crush.
Qed.

Inductive could_read : trace -> state -> Prop :=
  | could_read_nil:
    could_read nil IS
  | could_read_write: forall (t:trace) (s:state),
    could_read ((Write s) :: t) s
  | could_read_crash: forall (t:trace) (s:state),
    could_persist t s -> could_read (Crash :: t) s
  | could_read_read:  forall (t:trace) (s rs:state),
    could_read t s -> could_read ((Read rs) :: t) s
  | could_read_sync:  forall (t:trace) (s:state),
    could_read t s -> could_read (Sync :: t) s.

Theorem legal_could_read :
  forall (t:trace) (s:state),
  trace_legal ((Read s) :: t) -> could_read t s.
Proof.
  induction t; intros.
  - inversion H. inversion H2. inversion H3. constructor.
  - destruct a.
    + constructor. assert (Hs:=H).
      apply read_immutability in H.
      apply legal_subtrace in Hs. crush.
    + replace s0 with s. constructor. inversion H; crush.
      * inversion H2. reflexivity.
      * destruct H2. exists s0. constructor.
    + constructor.
      apply sync_before_read_irrelevence in H. crush.
    + constructor.
      inversion H. inversion H2. inversion H3. assumption.
Qed.


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


(* Base implementations of a file system *)

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: nat -> invocation
  | do_sync: invocation
  | do_crash: invocation.

Fixpoint fs_apply_list (fsstate: Set)
                       (init: fsstate)
                       (applyfun: fsstate -> invocation -> trace -> fsstate * trace)
                       (l: list invocation)
                       : fsstate * trace :=
  match l with
  | i :: rest =>
    match fs_apply_list fsstate init applyfun rest with
    | (s, t) => applyfun s i t
    end
  | nil => (init, nil)
  end.

Definition fs_legal (fsstate: Set)
                     (init: fsstate)
                     (applyfun: fsstate -> invocation -> trace -> fsstate * trace) :=
  forall (l: list invocation) (t: trace) (s: fsstate),
  fs_apply_list fsstate init applyfun l = (s, t) ->
  trace_legal t.


(* Eager file system: sync after every write *)

Definition eager_state := state.

Definition eager_init := IS.

Definition eager_apply (s: eager_state) (i: invocation) (t: trace) : eager_state * trace :=
  match i with
  | do_read    => (s, (Read s) :: t)
  | do_write n => (n, Sync :: (Write n) :: t)
  | do_sync    => (s, Sync :: t)
  | do_crash   => (s, Crash :: t)
  end.

Hint Constructors trace_legal.
Hint Constructors last_write_since_crash.
Hint Constructors could_persist.

Theorem eager_correct:
  fs_legal eager_state eager_init eager_apply.
Proof.
  unfold fs_legal.  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l); crush.
    +  constructor.
      * admit.
      * apply IHl with (s:=s). assumption.
    + repeat constructor. apply IHl with (s:=e). assumption.
    + constructor. apply IHl with (s:=s). assumption.
    + constructor. apply IHl with (s:=s). assumption.
Qed.

