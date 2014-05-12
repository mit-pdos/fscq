Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

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

Definition history := list event.

(* To define what crash and sync do, file has two values: its in-memory value
and its on-disk value. Only 1 file with a single integer has content. *)

Record file : Type := mkfile {
  Vmem : nat;
  Vdisk: nat
}.

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

(* An alternative definition of legal histories.  Note that this
 * definition treats histories "backwards": writing and then reading
 * a file is represented by: (Read 1) :: (Write 1) :: nil.
 *)

(* (last_wrote h n) means n was the last data written *)
Inductive last_wrote: history -> nat -> Prop :=
  | last_wrote_read:
    forall (h:history) (n:nat) (rn:nat),
    last_wrote h n -> last_wrote ((Read rn) :: h) n
  | last_wrote_write:
    forall (h:history) (n:nat),
    last_wrote ((Write n) :: h) n
  | last_wrote_sync:
    forall (h:history) (n:nat),
    last_wrote h n -> last_wrote (Sync :: h) n
  | last_wrote_crash:
    forall (h:history) (n:nat),
    last_wrote h n -> last_wrote (Crash :: h) n.

(* (wrote_since_sync h n) means n was either the last thing written before
   the last sync, or was written after the last sync *)
Inductive wrote_since_sync: history -> nat -> Prop :=
  | wrote_since_sync_read:
    forall (h:history) (n:nat) (rn:nat),
    wrote_since_sync h n -> wrote_since_sync ((Read rn) :: h) n
  | wrote_since_sync_write_1:
    forall (h:history) (n:nat),
    wrote_since_sync ((Write n) :: h) n
  | wrote_since_sync_write_2:
    forall (h:history) (n:nat) (wn:nat),
    wrote_since_sync h n -> wrote_since_sync ((Write wn) :: h) n
  | wrote_since_sync_sync:
    forall (h:history) (n:nat),
    last_wrote h n -> wrote_since_sync (Sync :: h) n
  | wrote_since_sync_crash:
    (* XXX
       One sensible requirement that this fails to model is that,
       once a system crashes, each file gets a well-defined value.
       So this allows a file to keep flip-flopping between values,
       across many crashes, until it's finally Sync'ed.
     *)
    forall (h:history) (n:nat),
    wrote_since_sync h n -> wrote_since_sync (Crash :: h) n.

(* (could_read h n) means n could be the return value of a read *)
Inductive could_read: history -> nat -> Prop :=
  | could_read_read:
    forall (h:history) (n:nat) (rn:nat),
    could_read h n -> could_read ((Read rn) :: h) n
  | could_read_write:
    forall (h:history) (n:nat),
    could_read ((Write n) :: h) n
  | could_read_sync:
    forall (h:history) (n:nat),
    could_read h n -> could_read (Sync :: h) n
  | could_read_crash:
    forall (h:history) (n:nat),
    wrote_since_sync h n -> could_read (Crash :: h) n.

Inductive legal2: history -> Prop :=
  | legal2_read:
    forall (h:history) (n:nat),
    could_read h n ->
    legal2 h -> legal2 ((Read n) :: h)
  | legal2_write:
    forall (h:history) (n:nat),
    legal2 h -> legal2 ((Write n) :: h)
  | legal2_sync:
    forall (h:history),
    legal2 h -> legal2 (Sync :: h)
  | legal2_crash:
    forall (h:history),
    legal2 h -> legal2 (Crash :: h)
  | legal2_nil:
    legal2 nil.

Theorem test_legal2_1:
  legal2 [ Read 1 ; Crash ; Write 0 ; Sync ; Write 1 ].
Proof.
  repeat constructor.
Qed.

Theorem test_legal2_0:
  legal2 [ Read 0 ; Crash ; Write 0 ; Sync ; Write 1 ].
Proof.
  repeat constructor.
Qed.
