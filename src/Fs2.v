Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

(* An alternative definition of legal histories.  Note that this
 * definition treats histories "backwards": writing and then reading
 * a file is represented by: (Read 1) :: (Write 1) :: nil.
 *)

Inductive event : Set :=
  | Read: nat -> event
  | Write: nat -> event
  | Flush: nat -> event
  | Sync: event
  | Crash: event.

Definition history := list event.

(* (last_flush h n) means n was the last thing flushed in h *)
Inductive last_flush: history -> nat -> Prop :=
  | last_flush_read:
    forall (h:history) (n:nat) (rn:nat),
    last_flush h n -> last_flush ((Read rn) :: h) n
  | last_flush_write:
    forall (h:history) (n:nat) (wn:nat),
    last_flush h n -> last_flush ((Write wn) :: h) n
  | last_flush_flush:
    forall (h:history) (n:nat),
    last_flush ((Flush n) :: h) n
  | last_flush_sync:
    forall (h:history) (n:nat),
    last_flush h n -> last_flush (Sync :: h) n
  | last_flush_crash:
    forall (h:history) (n:nat),
    last_flush h n -> last_flush (Crash :: h) n
  | last_flush_nil:
    last_flush nil 0.

(* (could_read h n) means n could be the return value of a read *)
Inductive could_read: history -> nat -> Prop :=
  | could_read_read:
    forall (h:history) (n:nat) (rn:nat),
    could_read h n -> could_read ((Read rn) :: h) n
  | could_read_write:
    forall (h:history) (n:nat),
    could_read ((Write n) :: h) n
  | could_read_flush:
    forall (h:history) (n:nat) (fn:nat),
    could_read h n -> could_read ((Flush fn) :: h) n
  | could_read_sync:
    forall (h:history) (n:nat),
    could_read h n -> could_read (Sync :: h) n
  | could_read_crash:
    forall (h:history) (n:nat),
    last_flush h n -> could_read (Crash :: h) n
  | could_read_nil:
    could_read nil 0.

Inductive could_flush: history -> nat -> Prop :=
  | could_flush_read:
    forall (h:history) (n:nat) (rn:nat),
    could_flush h n -> could_flush ((Read rn) :: h) n
  | could_flush_write_1:
    forall (h:history) (n:nat),
    could_flush ((Write n) :: h) n
  | could_flush_write_2:
    forall (h:history) (n:nat) (wn:nat),
    could_flush h n -> could_flush ((Write wn) :: h) n
  | could_flush_flush:
    forall (h:history) (n:nat) (fn:nat),
    could_flush h n -> could_flush ((Flush fn) :: h) n
  | could_flush_sync:
    forall (h:history) (n:nat),
    could_read h n -> could_flush (Sync :: h) n
  | could_flush_crash:
    forall (h:history) (n:nat),
    last_flush h n -> could_flush (Crash :: h) n
  | could_flush_nil:
    could_flush nil 0.

Inductive legal: history -> Prop :=
  | legal_read:
    forall (h:history) (n:nat),
    could_read h n ->
    legal h -> legal ((Read n) :: h)
  | legal_write:
    forall (h:history) (n:nat),
    legal h -> legal ((Write n) :: h)
  | legal_flush:
    forall (h:history) (n:nat),
    could_flush h n -> legal ((Flush n) :: h)
  | legal_sync:
    forall (h:history) (n:nat),
    could_read h n ->
    last_flush h n ->
    legal h ->
    legal (Sync :: h)
  | legal_crash:
    forall (h:history),
    legal h -> legal (Crash :: h)
  | legal_nil:
    legal nil.

Theorem test_legal_1:
  legal [ Read 1 ; Crash ; Write 0 ; Sync ; Flush 1 ; Write 1 ].
Proof.
  constructor.
  - repeat constructor.
  - constructor.  constructor.
    apply legal_sync with (n:=1); repeat constructor.
Qed.

Theorem test_legal_0:
  legal [ Read 0 ; Crash ; Flush 0 ; Write 0 ; Sync ; Flush 1 ; Write 1 ].
Proof.
  constructor.
  - repeat constructor.
  - constructor.  constructor.  repeat constructor.
Qed.

Theorem test_legal_nondeterm_0:
  legal [ Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ].
Proof.
  repeat constructor.
Qed.

Theorem test_legal_nondeterm_1:
  legal [ Read 1 ; Crash ; Flush 1 ; Write 1 ; Write 0 ].
Proof.
  repeat constructor.
Qed.

Theorem test_legal_weird_1:
  legal [ Read 1 ; Crash ; Read 0 ; Crash ; Flush 1 ; Write 1 ; Write 0 ].
Proof.
  constructor.
  - repeat constructor.
  - constructor.  constructor.
    + constructor.
Abort.

Theorem test_legal_weird_2:
  legal [ Read 1 ; Crash ; Flush 1 ; Read 0 ; Crash ; Flush 0 ; Write 1 ; Write 0 ].
Proof.
  constructor.
  - repeat constructor.
  - constructor.  constructor.  constructor.  constructor.
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

Definition eager_apply (s: eager_state) (i: invocation) (h: history) : eager_state * history :=
  match i with
  | do_read => (s, (Read s) :: h)
  | do_write n => (n, (Flush n) :: (Write n) :: h)
  | do_sync => (s, Sync :: h)
  | do_crash => (s, Crash :: h)
  end.

(* Lazy file system *)

Record lazy_state : Set := mklazy {
  LazyMem: nat;
  LazyDisk: nat
}.

Definition lazy_init := mklazy 0 0.

Definition lazy_apply (s: lazy_state) (i: invocation) (h: history) : lazy_state * history :=
  match i with
  | do_read => (s, (Read s.(LazyMem)) :: h)
  | do_write n => (mklazy n s.(LazyDisk), (Write n) :: h)
  | do_sync => (mklazy s.(LazyMem) s.(LazyMem), Sync :: (Flush s.(LazyMem)) :: h)
  | do_crash => (mklazy s.(LazyDisk) s.(LazyDisk), Crash :: h)
  end.

(* What does it mean for a file system to be correct? *)

Fixpoint fs_apply_list (state_type: Set)
                       (fs_init: state_type)
                       (fs_apply: state_type -> invocation -> history -> state_type * history)
                       (l: list invocation)
                       : state_type * history :=
  match l with
  | i :: rest =>
    match fs_apply_list state_type fs_init fs_apply rest with
    | (s, h) => fs_apply s i h
    end
  | nil => (fs_init, nil)
  end.

Definition fs_legal (state_type: Set)
                     (fs_init: state_type)
                     (fs_apply: state_type -> invocation -> history -> state_type * history) :=
  forall (l: list invocation) (h: history) (s: state_type),
  fs_apply_list state_type fs_init fs_apply l = (s, h) ->
  legal h.

(* Eager FS is correct *)

Hint Constructors last_flush.
Hint Constructors could_read.
Hint Constructors could_flush.
Hint Constructors legal.

Lemma eager_last_flush:
  forall (l: list invocation) (s: eager_state) (h: history),
  fs_apply_list eager_state eager_init eager_apply l = (s, h) ->
  last_flush h s.
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    crush.
Qed.

Lemma eager_could_read:
  forall (l: list invocation) (s: eager_state) (h: history),
  fs_apply_list eager_state eager_init eager_apply l = (s, h) ->
  could_read h s.
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    crush.
    + constructor.  apply eager_last_flush with (l:=l).  crush.
Qed.

Theorem eager_correct:
  fs_legal eager_state eager_init eager_apply.
Proof.
  unfold fs_legal.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list eager_state eager_init eager_apply l);
    crush.
    + constructor.
      * apply eager_could_read with (l:=l).  crush.
      * apply IHl with (s:=s).  crush.
    + apply legal_sync with (n:=s).
      * apply eager_could_read with (l:=l).  crush.
      * apply eager_last_flush with (l:=l).  crush.
      * apply IHl with (s:=s).  crush.
    + constructor.  apply IHl with (s:=s).  crush.
Qed.

(* Lazy FS correct *)

Lemma lazy_last_flush:
  forall (l: list invocation) (s: lazy_state) (h: history),
  fs_apply_list lazy_state lazy_init lazy_apply l = (s, h) ->
  last_flush h (LazyDisk s).
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    crush.
Qed.

Lemma lazy_could_read:
  forall (l: list invocation) (s: lazy_state) (h: history),
  fs_apply_list lazy_state lazy_init lazy_apply l = (s, h) ->
  could_read h (LazyMem s).
Proof.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    crush.
    + constructor.  apply lazy_last_flush with (l:=l).  crush.
Qed.

Lemma could_read_2_could_flush:
  forall h v,
  could_read h v ->
  could_flush h v.
Proof.
  induction h.
  - crush.  inversion H.  crush.
  - destruct a; intros; inversion H; crush.
Qed.

Theorem lazy_correct:
  fs_legal lazy_state lazy_init lazy_apply.
Proof.
  unfold fs_legal.
  induction l.
  - crush.
  - destruct a; simpl;
    case_eq (fs_apply_list lazy_state lazy_init lazy_apply l);
    crush.
    + constructor.
      * apply lazy_could_read with (l:=l).  crush.
      * apply IHl with (s:=s).  crush.
    + constructor.  apply IHl with (s:=l0).  crush.
    + apply legal_sync with (n:=(LazyMem l0)).
      * constructor.  apply lazy_could_read with (l:=l).  crush.
      * constructor.
      * constructor.
        apply could_read_2_could_flush.
        apply lazy_could_read with (l:=l).
        crush.
    + constructor.  apply IHl with (s:=l0).  crush.
Qed.
