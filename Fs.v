Require Import List.
Require Import CpdtTactics.
Require Import Arith.

(* Take a trivial history of file operations (e.g., [ (Read, 0) (Write, 1)
(Crash, 0) (Sync, 0) (Read, 1)]), and say whether it is legal.  Perhaps a proof
of an implementation of actual file operations, then would be a theorem saying
that the implementation produces only legal histories, and therefore is
correct. *)

(* Trivial file system API, including Sync and Crash events.  XXX Each call
should be probably split in invoke and result, to model concurrency. *)

Inductive event : Set :=
  | Read: nat -> event
  | Write: nat -> event
  | Sync: event
  | Crash: event.

(* To define what crash and sync do, file has two values: its in-memory value
and its on-disk value. Only 1 file with a single integer has content. *)

Record file : Type := mkfile {
  Vmem : nat;
  Vdisk: nat
}.

Definition history := list event.

(* A event returns whether its return value was legal and what the file's state
is after the processing the event. Write updates the in-memory state. Sync
flushes the in-memory state to on-disk state. Crash resets the in-memory state
to the on-disk state. n in (Read, n) must match the in-memory state of the file. *)

Definition eventDenote (e : event) (f : file) : bool * file :=
  match e with 
  | Read n => 
    if beq_nat n f.(Vmem) then (true, f)
    else (false, f)
  | Write n => (true, (mkfile n f.(Vmem)))
  | Sync => (true, (mkfile f.(Vmem) f.(Vmem)))
  | Crash => (true, (mkfile f.(Vdisk) f.(Vdisk)))
  end.

(* check if a history is legal, given a starting file state. *)
Fixpoint legal (h: history) (f : file) : bool  := 
  match h with
    | nil => true
    | e :: h1 => 
      let i := (eventDenote e f) in
      match i with
        | (false, _) => false
        | (true, f1) => legal h1 f1
      end
  end.

(* Check some histories: *)
Eval simpl in legal ((Write 1) :: (Read 1) :: nil) (mkfile 0 0).
Eval simpl in legal ((Write 1) :: (Read 0) :: nil) (mkfile 0 0).
Eval simpl in legal ((Write 1) :: Sync :: (Read 1) :: nil) (mkfile 0 0).
Eval simpl in legal ((Write 1) :: Sync :: (Read 0) :: nil) (mkfile 0 0).
Eval simpl in legal ((Write 1) :: (Read 1) :: Crash :: nil) (mkfile 0 0).
Eval simpl in legal ((Write 1) :: (Read 1) :: Crash :: (Read 0) :: nil) (mkfile 0 0).
Eval simpl in legal ((Write 1) :: (Read 1) :: Crash :: (Read 1) :: nil) (mkfile 0 0).
