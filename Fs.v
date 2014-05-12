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
    last_wrote h n -> last_wrote (Crash :: h) n
  | last_wrote_nil:
    last_wrote nil 0.

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
    wrote_since_sync h n -> wrote_since_sync (Crash :: h) n
  | wrote_since_sync_nil:
    wrote_since_sync nil 0.

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
    wrote_since_sync h n -> could_read (Crash :: h) n
  | could_read_nil:
    could_read nil 0.

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

Theorem test_legal2_weird:
  legal2 [ Read 1 ; Crash ; Read 0 ; Crash ; Write 1 ; Write 0 ].
Proof.
  repeat constructor.
Qed.

(* Toy implementations of a file system *)

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: nat -> invocation
  | do_sync: invocation
  | do_crash: invocation.

(* Eager file system *)

Definition eager_state := nat.

Definition eager_init := 0.

Definition eager_apply (s: eager_state) (i: invocation) : eager_state * event :=
  match i with
  | do_read => (s, Read s)
  | do_write n => (n, Write n)
  | do_sync => (s, Sync)
  | do_crash => (s, Crash)
  end.

(* Lazy file system *)

Record lazy_state : Set := mklazy {
  LazyMem: nat;
  LazyDisk: nat
}.

Definition lazy_init := mklazy 0 0.

Definition lazy_apply (s: lazy_state) (i: invocation) : lazy_state * event :=
  match i with
  | do_read => (s, Read s.(LazyMem))
  | do_write n => (mklazy n s.(LazyDisk), Write n)
  | do_sync => (mklazy s.(LazyMem) s.(LazyMem), Sync)
  | do_crash => (mklazy s.(LazyDisk) s.(LazyDisk), Crash)
  end.

(* What does it mean for a file system to be correct? *)

Fixpoint fs_apply_list (state_type: Set)
                       (fs_init: state_type)
                       (fs_apply: state_type -> invocation -> state_type * event)
                       (l: list invocation)
                       : state_type * history :=
  match l with
  | i :: rest =>
    match fs_apply_list state_type fs_init fs_apply rest with
    | (s, h) =>
      match fs_apply s i with
      | (s', e) => (s', e :: h)
      end
    end
  | nil => (fs_init, nil)
  end.

Definition fs_legal2 (state_type: Set)
                     (fs_init: state_type)
                     (fs_apply: state_type -> invocation -> state_type * event) :=
  forall (l: list invocation) (h: history) (s: state_type),
  fs_apply_list state_type fs_init fs_apply l = (s, h) ->
  legal2 h.

(* Eager FS is correct *)

Lemma eager_last_wrote:
  forall (l: list invocation) (s: eager_state) (h: history),
  fs_apply_list eager_state eager_init eager_apply l = (s, h) ->
  last_wrote h s.
Proof.
  induction l.
  - crush; inversion H; unfold eager_init; constructor.
  - destruct a; unfold fs_apply_list; fold fs_apply_list; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    intros; inversion H0.
    + constructor.  apply IHl.  crush.
    + constructor.
    + constructor.  apply IHl.  crush.
    + constructor.  apply IHl.  crush.
Qed.

Lemma last_wrote_wrote_since_sync:
  forall h n,
  last_wrote h n -> wrote_since_sync h n.
Proof.
  induction h.
  - crush.  inversion H.  constructor.
  - destruct a; intros; inversion H.
    + constructor.  apply IHh.  auto.
    + constructor.
    + constructor.  auto.
    + constructor.  apply IHh.  auto.
Qed.

Lemma last_wrote_could_read:
  forall h n,
  last_wrote h n -> could_read h n.
Proof.
  induction h.
  - crush.  inversion H.  constructor.
  - destruct a; intros; inversion H.
    + constructor.  apply IHh.  auto.
    + constructor.
    + constructor.  apply IHh.  auto.
    + constructor.  apply last_wrote_wrote_since_sync.  auto.
Qed. 

Theorem eager_correct:
  fs_legal2 eager_state eager_init eager_apply.
Proof.
  unfold fs_legal2.
  induction l.
  - crush; inversion H; constructor.
  - destruct a; unfold fs_apply_list; fold fs_apply_list; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    intros; inversion H0.
    + constructor.
      * apply last_wrote_could_read.  eapply eager_last_wrote.  rewrite <- H2.  exact H.
      * apply IHl with (s:=e).  auto.
    + constructor; apply IHl with (s:=e); crush.
    + constructor; apply IHl with (s:=e); crush.
    + constructor; apply IHl with (s:=e); crush.
Qed.

(* Lazy FS correct *)

Inductive wrote_before_sync: history -> nat -> Prop :=
  | wrote_before_sync_read:
    forall (h:history) (n:nat) (rn:nat),
    wrote_before_sync h n -> wrote_before_sync ((Read rn) :: h) n
  | wrote_before_sync_write:
    forall (h:history) (n:nat) (wn:nat),
    wrote_before_sync h n -> wrote_before_sync ((Write wn) :: h) n
  | wrote_before_sync_sync:
    forall (h:history) (n:nat),
    last_wrote h n -> wrote_before_sync (Sync :: h) n
  | wrote_before_sync_crash:
    forall (h:history) (n:nat),
    wrote_before_sync h n -> wrote_before_sync (Crash :: h) n
  | wrote_before_sync_nil:
    wrote_before_sync nil 0.

Lemma lazy_could_read:
  forall (l: list invocation) (s: lazy_state) (h: history),
  fs_apply_list lazy_state lazy_init lazy_apply l = (s, h) ->
  could_read h (LazyMem s) /\ wrote_before_sync h (LazyDisk s).
Proof.
  induction l.
  - crush; inversion H; unfold eager_init; constructor.
  - destruct a; unfold fs_apply_list; fold fs_apply_list; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    intros; inversion H0.
    + split.
      * constructor.  apply IHl.  crush.
      * constructor.  apply IHl.  crush.
    + split.
      * constructor.
      * constructor.  simpl.  apply IHl.  crush.
    + split.
      * constructor.  simpl.  apply IHl.  auto.
      * simpl.  constructor.
        (* XXX not provable due to the weirdness illustated by test_legal2_weird:
           according to the spec, Sync forces the last write to disk, even if that
           last write happened before a Crash!
         *)
Abort.

(*
Theorem lazy_correct:
  fs_legal2 lazy_state lazy_init lazy_apply.
Proof.
  unfold fs_legal2.
  induction l.
  - crush; inversion H; constructor.
  - destruct a; unfold fs_apply_list; fold fs_apply_list; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    intros; inversion H0.
    + constructor.
      * apply lazy_could_read with (l:=l).  rewrite <- H2.  auto.
      * apply IHl with (s:=l0).  auto.
    + constructor; apply IHl with (s:=l0); crush.
    + constructor; apply IHl with (s:=l0); crush.
    + constructor; apply IHl with (s:=l0); crush.
Qed.
*)
