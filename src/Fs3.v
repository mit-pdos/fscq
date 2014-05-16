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
  | Sync: event.

(* Crash-free trace *)
Definition trace := list event.

(* List of crash-free traces, with crashes in between *)
Definition traces_with_crash := list trace.

Definition append_to_last_trace (e : event) (h: traces_with_crash) : traces_with_crash :=
    match h with
    | nil => [[e]]
    | x :: h1  => (e :: x):: h1
    end.

(* Potential persistent states for a trace *)
Definition ppstates := list state.

(* Find the latest write event in a trace *)
Fixpoint trace_last_write (t:trace) : option event :=
  match t with
  | nil           => None
  | Write x :: t' => Some (Write x)
  | Read _  :: t' => trace_last_write(t')
  | Sync    :: t' => trace_last_write(t')
  end.

(* Get a list of possilbe persistent states after applying a trace  *)
Fixpoint find_ppstates (t:trace) (init: ppstates) : ppstates :=
  match t with
  | nil =>  (init)
  | Write x :: t' => (x :: (find_ppstates t' init))
    (* 'Write' always adds a potential state *)
  | Read x :: t' =>
    match (trace_last_write t') with
    | None  => (x :: nil)
    | _ => (find_ppstates t' init)
    end
    (* 'Read' fixiates a potential state when there's no preceding writes *)
  | Sync :: t' =>
    match (trace_last_write t') with
    | Some (Write x) => (x :: nil)
    | _ => (find_ppstates t' init)
    end
    (* 'Sync' fixiates the potential state to the latest Write *)
  end.

(* Is a crash-free trace legal?  *)
Fixpoint is_trace_legal (t:trace) (init:ppstates) : Prop :=
  match t with
  | nil => True
  | Sync    :: t' => (is_trace_legal t' init)
  | Write _ :: t' => (is_trace_legal t' init)
  | Read x  :: t' =>
    match (trace_last_write t') with
    | Some (Write y) => (is_trace_legal t' init) /\ (x = y) 
    | _              => (is_trace_legal t' init) /\ (In x (find_ppstates t' init))
    end
    (* 'Read' shall always reveal the last written state;
     * if no writes, it can reveal any states in ppstates of t'.  *)
  end.

Fixpoint find_ppstates_traces (tc:traces_with_crash) : ppstates :=
  match tc with
  | nil => [ IS ]
  | t :: tc' => (find_ppstates t (find_ppstates_traces tc'))
  end.

Fixpoint is_legal (tc:traces_with_crash) : Prop :=
  match tc with
  | nil => True
  | t :: tc' => (is_legal(tc') /\ (is_trace_legal t (find_ppstates_traces tc')))
  end.


(* Testing *)

Definition test_1 := [ [ Read 1 ; Write 1 ; Read 0 ; Write 0 ; Sync ; Read 1 ] ;
                       [ Read 2 ; Write 2 ; Write 1 ] ] .
Theorem test_legal_1:
  is_legal test_1.
Proof.
  simpl.
  tauto.
Qed.

Definition test_2 := [ [ Read 1 ] ; [ Read 3 ; Write 3 ] ; [ Write 2 ; Write 1 ] ] .
Theorem test_legal_2:
  is_legal test_2.
Proof.
  simpl.
  tauto.
Qed.

Definition test_3 := [ [ Read 1 ] ; [ Read 3 ; Sync ; Write 3 ] ; [ Write 2 ; Write 1 ] ] .
Theorem test_legal_3:
  is_legal test_3.
Proof.
  simpl.
  try tauto.
  Abort.

Definition test_4 := [ [ Read 2 ] ; [ Read 3 ; Write 3 ; Read 1 ] ; [ Write 2 ; Write 1 ] ] .
Theorem test_legal_4:
  is_legal test_4.
Proof.
  simpl.
  try tauto.
  Abort.

Definition test_5 := [ [ Read 1; Read 2 ] ; [ Write 1; Write 2 ] ].
Theorem test_legal_5:
  is_legal test_5.
Proof.
  simpl.
  try tauto.
  Abort.

(* Toy implementations of a file system *)

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: nat -> invocation
  | do_sync: invocation
  | do_crash: invocation.

(* Eager file system *)

Definition eager_state := nat.

Definition eager_init := 0.

(* gen traces with crash: *)

Definition eager_apply (s: eager_state) (i: invocation) (h: traces_with_crash) : eager_state * traces_with_crash :=
  match i with
  | do_read =>  (s, (append_to_last_trace (Read s) h))
  | do_write n => (n, (append_to_last_trace (Write n) h))
  | do_sync => (s, (append_to_last_trace Sync h))
  | do_crash => (s, [] :: h)
  end.

(* What does it mean for a file system to be correct? *)

Fixpoint fs_apply_list (state_type: Set)
                       (fs_init: state_type)
                       (fs_apply: state_type -> invocation -> traces_with_crash -> state_type * traces_with_crash)
                       (l: list invocation)
                       : state_type * traces_with_crash :=
  match l with
  | i :: rest =>
    match fs_apply_list state_type fs_init fs_apply rest with
    | (s, h) => fs_apply s i h
    end
  | nil => (fs_init, nil)
  end.

Definition fs_legal (state_type: Set)
                     (fs_init: state_type)
                     (fs_apply: state_type -> invocation -> traces_with_crash -> state_type * traces_with_crash) :=
  forall (l: list invocation) (h: traces_with_crash) (s: state_type),
  fs_apply_list state_type fs_init fs_apply l = (s, h) ->
  is_legal h.

Theorem eager_correct:
  fs_legal eager_state eager_init eager_apply.
Proof.
  unfold fs_legal.
  induction l.
  - crush.
  - destruct a; unfold fs_apply_list; fold fs_apply_list; case_eq (fs_apply_list eager_state eager_init eager_apply l); crush.
  

