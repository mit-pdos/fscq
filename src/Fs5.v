Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

(* disk with atomicity of two writes.  can i use the spec from from Fs2.v and
extend with ABwrite and AEwrite? *)

(* XXX need two blocks to make it more interesting ... *)

Inductive event : Set :=
  | Read: nat -> event
  | Write: nat -> event
  | Flush: nat -> event
  | Sync: event
  | Crash: event
  | ABwrite: nat -> event
  | AEwrite: nat -> event.

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
  | last_flush_ABwrite:
    forall (h:history) (n:nat) (wn: nat),
    last_flush ((ABwrite wn) :: h) n
  | last_flush_nil:
    last_flush nil 0.

Inductive atomic: history -> nat -> Prop :=
  | atomic_begin_write:
    forall (h:history) (n:nat) (rn:nat),
      atomic ((ABwrite rn) :: h) n.

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
  | could_read_begin:
    forall (h:history) (n:nat),
    could_read ((ABwrite n) :: h) n
  | could_read_end:
    forall (h:history) (n:nat),
    could_read ((AEwrite n) :: h) n
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
    could_flush h n ->
    legal h ->
    legal ((Flush n) :: h)
  | legal_sync:
    forall (h:history) (n:nat),
    could_read h n ->
    last_flush h n ->
    legal h ->
    legal (Sync :: h)
  | legal_AEwrite:
    forall (h:history) (n:nat),
    atomic h n ->
    legal h ->
    legal ((AEwrite n) :: h)
  | legal_ABwrite:
    forall (h:history) (n:nat),
    legal h ->
    legal ((ABwrite n) :: h)
  | legal_crash:
    forall (h:history),
    legal h -> legal (Crash :: h)
  | legal_nil:
    legal nil.

Theorem test_legal_1:
  legal [ Read 1 ;  AEwrite 1 ; ABwrite 2 ].
Proof.
  repeat constructor.
Qed.

Theorem test_legal_2:
  legal [ Read 0 ; Crash; ABwrite 2 ].
Proof.
  repeat constructor.
Qed.

Theorem test_legal_3:
  ~ legal [ Read 1 ;  AEwrite 1 ; Crash; ABwrite 2 ].
Proof.
  intro.
  inversion H.
  inversion H2.
  inversion H3.
  inversion H8.
Qed.

Theorem test_legal_4:
  ~ legal [ Read 2 ; Crash; ABwrite 2 ].
Proof.
  intro.
  inversion H.
  clear H.
  inversion H2.
  clear H2.
  (* last_flush [ABwrite 2] 2 is false but i lose last_flush [] 2 *)
  admit.
Qed.

(* now can do refinement. use two lazy2 disks to implement an atomic disk, or use two lazy2 disks to implement a disk with 2 blocks (but that seems stupid, because we want 1 cache. *)

(* how to split in separate modules: i want to use lazy2_state *)

Record AtomicLazy2 : Set := mkAtomicLazy2 {
  Lazy2Log: lazy2_state;
  Lazy2Data: lazy2_state
}.

Definition AtomicLazy2_init := mkAtomicLazy2 (mklazy2 None 0) (mklazy2 None 0).

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: nat -> invocation
  | do_ABwrite: nat -> invocation
  | do_AEwrite: nat -> invocation
  | do_sync: invocation
  | do_crash: invocation.

Definition lazy2_read (s : lazy2_state) : nat * lazy2_state :=
  match s.(Lazy2Mem) with 
      | None => (s.(Lazy2Disk), mklazy2 (Some s.(Lazy2Disk)) s.(Lazy2Disk))
      | Some x => (x, s)
  end.

Definition lazy2_sync (s: lazy2_state) : lazy2_state * history :=
    match s.(Lazy2Mem) with
    | None => (s, [Sync])
    | Some x => (mklazy2 (Some x) x, [ Sync ; Flush x ])
    end.


(* All ops run from Lazy2Data, except when doing ABwrite, which applies to logging disk *)
(* AEwrite installs logging disk into data disk. *)

Definition AtomicLazy2_apply (s: lazy2_state) (i: invocation) (h: history) : lazy2_state * history :=
  match i with
  | do_read => let (x, s1) := lazy2_read(s) in 
               (s1, (Read x) :: h)
  | do_write n => (mklazy2 (Some n) s.(Lazy2Disk), (Write n) :: h)
  | do_sync =>
    let (s1, h1) := lazy2_sync(s) in 
               (s1, h1 ++ h)
  | do_crash => (mklazy2 None s.(Lazy2Disk), Crash :: h)
  end.
