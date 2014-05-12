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

Inductive wrote_since_crash_or_flush: history -> nat -> Prop :=
  | wrote_since_crash_or_flush_read:
    forall (h:history) (n:nat) (rn:nat),
    wrote_since_crash_or_flush h n -> wrote_since_crash_or_flush ((Read rn) :: h) n
  | wrote_since_crash_or_flush_write_1:
    forall (h:history) (n:nat),
    wrote_since_crash_or_flush ((Write n) :: h) n
  | wrote_since_crash_or_flush_write_2:
    forall (h:history) (n:nat) (wn:nat),
    wrote_since_crash_or_flush h n -> wrote_since_crash_or_flush ((Write wn) :: h) n
  | wrote_since_crash_or_flush_sync:
    forall (h:history) (n:nat),
    wrote_since_crash_or_flush h n -> wrote_since_crash_or_flush (Sync :: h) n.

Inductive no_write_since_crash: history -> Prop :=
  | no_write_since_crash_read:
    forall (h:history) (n:nat),
    no_write_since_crash h -> no_write_since_crash ((Read n) :: h)
  | no_write_since_crash_sync:
    forall (h:history),
    no_write_since_crash h -> no_write_since_crash (Sync :: h)
  | no_write_since_crash_flush:
    forall (h:history) (n:nat),
    no_write_since_crash h -> no_write_since_crash ((Flush n) :: h)
  | no_write_since_crash_crash:
    forall (h:history),
    no_write_since_crash (Crash :: h).

Inductive last_write_since_crash: history -> nat -> Prop :=
  | last_write_since_crash_read:
    forall (h:history) (n:nat) (rn:nat),
    last_write_since_crash h n -> last_write_since_crash ((Read rn) :: h) n
  | last_write_since_crash_sync:
    forall (h:history) (n:nat),
    last_write_since_crash h n -> last_write_since_crash (Sync :: h) n
  | last_write_since_crash_flush:
    forall (h:history) (n:nat) (fn:nat),
    last_write_since_crash h n -> last_write_since_crash ((Flush fn) :: h) n
  | last_write_since_crash_write:
    forall (h:history) (n:nat),
    last_write_since_crash ((Write n) :: h) n.

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
    wrote_since_crash_or_flush h n -> legal ((Flush n) :: h)
  | legal_sync_nop:
    forall (h:history),
    no_write_since_crash h ->
    legal h -> legal (Sync :: h)
  | legal_sync_flushed:
    forall (h:history) (n:nat),
    last_write_since_crash h n ->
    last_flush h n ->
    legal h -> legal (Sync :: h)
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
    apply legal_sync_flushed with (n:=1); repeat constructor.
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
  - constructor.  constructor.  constructor.
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

Definition fs_legal (state_type: Set)
                     (fs_init: state_type)
                     (fs_apply: state_type -> invocation -> state_type * event) :=
  forall (l: list invocation) (h: history) (s: state_type),
  fs_apply_list state_type fs_init fs_apply l = (s, h) ->
  legal h.

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
  fs_legal eager_state eager_init eager_apply.
Proof.
  unfold fs_legal.
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
        (* XXX not provable due to the weirdness illustated by test_legal_weird:
           according to the spec, Sync forces the last write to disk, even if that
           last write happened before a Crash!
         *)
Abort.

(*
Theorem lazy_correct:
  fs_legal lazy_state lazy_init lazy_apply.
Proof.
  unfold fs_legal.
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
