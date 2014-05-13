Require Import List.
Require Import ListSet.
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

(* Is a crash-free trace legal?  *)
Fixpoint is_trace_legal (t:trace) (init:ppstates) : Prop :=
  match t with
  | nil => True
  | Sync    :: t' => (is_trace_legal t' init)
  | Write _ :: t' => (is_trace_legal t' init)
  | Read x  :: t' =>
    match (trace_last_write t') with
    | Some (Write y) => (is_trace_legal t' init) /\ (x = y) 
    | _              => (is_trace_legal t' init) /\ (In x init)
    end
    (* 'Read' shall always reveal the last written state;
     * if no writes, it can reveal any states in 'init'.  *)
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

Eval simpl in find_ppstates [ Read 1 ; Write 1 ; Read 0 ; Write 0 ; Sync ; Read 1 ] [ 1 ; 2 ] .

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
                       [ Read 2 ; Write 2 ; Write 1] ] .

Theorem test_legal_1:
  is_legal test_1.

Proof.
  simpl.
  tauto.
Qed.
