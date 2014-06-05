Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Import ListNotations.

(* Disk with atomicity of n writes. Histories are "backwards": writing and then
reading a block with value n is represented by: (Read d n) :: (Write d n) ::
nil. *)

Inductive event : Set :=
  | Read: nat -> nat -> event
  | Write: nat -> nat -> event
  | Sync: event
  | Crash: event    (* XXX crash should come from somewhere else *)
  | TBegin: event
  | TEnd: event.

Definition history := list event.

(* (last_flush h n) means n was the last thing flushed in h *)
Inductive last_flush: history -> nat -> nat -> Prop :=
  | last_flush_read:
    forall (h:history) (d: nat) (n:nat) (rn:nat),
    last_flush h d n -> last_flush ((Read d rn) :: h) d n
  | last_flush_write:
    forall (h:history) (d: nat) (n:nat) (wn:nat),
    last_flush h d n -> last_flush ((Write d wn) :: h) d n
  | last_flush_sync:
    forall (h:history) (d: nat) (n:nat),
    last_flush h d n -> last_flush (Sync :: h) d n
  | last_flush_crash:
    forall (h:history) (d:nat) (n:nat),
    last_flush h d n -> last_flush (Crash :: h) d n
  | last_flush_Tbegin:
    forall (h:history) (d:nat) (n:nat),
    last_flush h d n -> last_flush (TBegin :: h) d n
  | last_flush_Tend:
    forall (h:history) (d:nat) (n:nat),
    last_flush h d n -> last_flush (TEnd :: h) d n
  | last_flush_nil:
    forall (d:nat),
    last_flush nil d 0.

(* Is this a transaction? XXX don't accept recursive transactions? *)
Inductive could_begin: history -> nat -> Prop :=
  | could_Tbegin:
    forall (h:history) (d: nat),
      could_begin (TBegin :: h) d
  | could_begin_write:
    forall (h:history) (d: nat) (d1: nat) (n1:nat),
      could_begin h d ->
      could_begin ((Write d1 n1) :: h) d
  | could_begin_read:
    forall (h:history) (d: nat) (d1: nat) (n1:nat),
      could_begin h d ->
      could_begin ((Read d1 n1) :: h) d.

(* (could_read h n) means n could be the return value of a read *)
Inductive could_read: history -> nat -> nat -> Prop :=
  | could_read_read1:
    forall (h:history) (d: nat) (n:nat) (rn:nat),
    could_read h d n -> could_read ((Read d rn) :: h) d n
 | could_read_read2:
    forall (h:history) (d: nat) (d1: nat) (n:nat) (rn:nat),
    could_read h d n -> could_read ((Read d1 rn) :: h) d n
  | could_read_write1:
    forall (h:history) (d: nat) (n:nat),
    could_read ((Write d n) :: h) d n
  | could_read_write2:
    forall (h:history) (d: nat) (d1: nat) (n:nat) (n1: nat),
    could_read h d n ->
    could_read ((Write d1 n1) :: h) d n
  | could_read_sync:
    forall (h:history) (d: nat) (n:nat),
    could_read h d n -> could_read (Sync :: h) d n
  | could_read_crash:
    forall (h:history) (d: nat) (n:nat),
    last_flush h d n -> could_read (Crash :: h) d n
  | could_read_begin1:
    forall (h:history) (d:nat) (n:nat),
    could_read (TBegin :: h) d n
  | could_read_end1:
    forall (h:history) (d:nat) (n:nat),
    could_read (TEnd:: h) d n
  | could_read_nil:
    forall (d: nat),
    could_read nil d 0.

(* XXX really could_sync *)
Inductive could_flush: history -> nat -> nat -> Prop :=
  | could_flush_read:
    forall (h:history) (d: nat) (n:nat) (rn:nat),
    could_flush h d n -> could_flush ((Read d rn) :: h) d n
  | could_flush_write_1:
    forall (h:history) (d: nat) (n:nat),
    could_flush ((Write d n) :: h) d n
  | could_flush_write_2:
    forall (h:history) (d : nat) (n:nat) (wn:nat),
    could_flush h d n -> could_flush ((Write d wn) :: h) d n
  | could_flush_sync:
    forall (h:history) (d : nat) (n:nat),
    could_read h d n -> could_flush (Sync :: h) d n
  | could_flush_crash:
    forall (h:history) (d : nat) (n:nat),
    last_flush h d n -> could_flush (Crash :: h) d n
  | could_flush_nil:
    forall (d : nat),
    could_flush nil d 0.

(* legal h d means that h is legal for disk block d *)
Inductive legal: history -> nat -> Prop :=
  | legal_read1:
    forall (h:history) (d : nat) (n:nat),
    could_read h d n ->
    legal h d -> 
    legal ((Read d n) :: h) d
  | legal_read2:
    forall (h:history) (d : nat) (d1: nat) (n:nat) (n1: nat),
    legal h d ->
    could_read h d1 n1 ->
    legal ((Read d1 n1) :: h) d
  | legal_write:
    forall (h:history) (d : nat) (d1: nat) (n:nat) (n1: nat),
    legal h d -> legal h d1 -> legal ((Write d1 n1) :: h) d
  | legal_sync:
    forall (h:history) (d : nat) (n:nat),
    could_read h d n ->
    last_flush h d n ->
    legal h d ->
    legal (Sync :: h) d
  | legal_begin:
    forall (h:history) (d:nat),
    legal h d ->
    legal (TBegin :: h) d
  | legal_end:
    forall (h:history) (d : nat),
    could_begin h d  ->
    legal h d ->
    legal (TEnd:: h) d
  | legal_crash:
    forall (h:history) (d:nat),
    legal h d -> legal (Crash :: h) d
  | legal_nil:
    forall (d:nat),
    legal nil d.

Theorem test_legal_1:
  forall (d:nat),
    legal [ Read 1 1 ;  Write 1 1 ] d.
Proof.
  intro.
  repeat constructor.
Qed.

Theorem test_legal_2:
  forall (d:nat),
  ~ legal [ Read 0 1 ;  Write 1 1 ] d. 
Proof.
  intro.
  intuition.
  inversion H.
  - clear H.
    inversion H4.
    inversion H10.
  - intros.
    inversion H4.
    inversion H5.
    inversion H17.
Qed.

Theorem test_legal_3:
  forall (d:nat),
    legal [ Read 0 1; Read 1 1 ; Write 0 1; Write 1 1 ] d.
Proof.
  intro.
  repeat constructor.
Qed.

Theorem test_legal_4:
  forall (d:nat),
    legal [ Read 0 1 ; Read 1 1 ; TEnd; Write 0 1 ; Write 1 1 ; TBegin] d.
Proof.
  intro.
  repeat constructor.
Qed.

Theorem test_legal_5: 
  forall (d:nat),
    legal [ Read 0 0 ;  Crash ; Write 0 1 ] d.
Proof.
  intro.
  repeat constructor.
Qed.

Theorem test_legal_6:
  forall (d: nat),
    legal [ Read 1 0 ; Crash; Write 1 1; TBegin ] d.
Proof.
  intro.
  repeat constructor.
Qed.

(* An atomic abstract disk that implements the above spec. The abstract disk has
a storage device and a list of actions in a transactions that haven't been
applied yet. They will be applied when the transaction ends/commits atomically.
*)

Definition addr := nat.
Definition val := nat.
Definition storage := addr -> val.

Parameter st_init  : storage.
Parameter st_write : storage -> addr -> val -> storage.
Parameter st_read  : storage -> addr -> val.

Axiom st_write_eq:
  forall s a v, st_write s a v a = v.

Axiom st_write_ne:
  forall s a v a', a <> a' -> st_write s a v a' = s a'.

Axiom st_read_eq:
  forall s a, st_read s a = s a.

Inductive invocation : Set :=
  | do_read: nat -> invocation
  | do_write: nat -> nat -> invocation
  | do_begin: invocation
  | do_end: invocation
  | do_crash: invocation.

Record TDisk: Set := mkTDisk {
  disk : storage;
  pending : list invocation   (* list of pending invocations in a transaction *)
}.

Definition abstract_apply (s: TDisk) (i: invocation) (h: history) : TDisk * history :=
  match i with
      | do_read d => (s, (Read d (st_read s.(disk) d)) :: h)
      | do_write d n => let disk1 := (st_write s.(disk) d n) in
                        ((mkTDisk disk1 s.(pending)),  (Write d n) :: h)
      | _ => (s, h)
  end.
  
Fixpoint apply_pending (s: TDisk) (l : list invocation) (h: history) : TDisk * history := 
  match l with
  | i :: rest =>
    let (s1, h1) := (apply_pending s rest h) in 
      (abstract_apply s1 i h1)
  | nil => (s, h)
  end.

Fixpoint apply_to_TDisk (s : TDisk) (l : list invocation) (h: history) : (bool * TDisk) * history := 
  match l with
  | i :: rest =>
    let (bDisk, h1) := (apply_to_TDisk s rest h) in
    let (intransaction, s1) := bDisk in
    match i with
    | do_begin => (true, s1, (TBegin :: h1))
    | do_end => (* apply pending list *)
      let (s2, h2) := (apply_pending s1 s1.(pending) h1) in
              (false, s2, (TEnd :: h2))
    | do_crash => (false, (mkTDisk s1.(disk) []), (Crash :: h1))    (* reset pending list *)
    | _ => 
      match intransaction with
      | true => (true, (mkTDisk s1.(disk) (i :: s1.(pending))), h1)
      | _ => let (s2, h2) := (abstract_apply s1 i h1) in
        (false, s2, h2)
      end
    end
  | nil => (false, s, h)
  end.

(* Eval apply_to_TDisk in (mkTDisk st_init []) [] []. *)

Theorem TDisk_legal:
  forall (l: list invocation) (h: history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) l [] = (b, s, h) -> legal h d.
Proof.
  intros.
  admit.
Qed.

(* a simple disk that models crashes by losing its volatile memory content, from Fs2.v *)

Record lazy2_state : Set := mklazy2 {
  Lazy2Mem: option nat;
  Lazy2Disk: nat
}.

Definition lazy2_init := mklazy2 None 0.

Definition lazy2_read (s : lazy2_state) : lazy2_state :=
  match s.(Lazy2Mem) with 
      | None => mklazy2 (Some s.(Lazy2Disk)) s.(Lazy2Disk)
      | Some x => s
  end.

Definition lazy2_sync (s: lazy2_state) : lazy2_state :=
    match s.(Lazy2Mem) with
    | None => s
    | Some x => mklazy2 (Some x) x
    end.

Definition lazy2_apply (s: lazy2_state) (i: invocation) : lazy2_state :=
  match i with
  | do_read => lazy2_read(s)
  | do_write n => mklazy2 (Some n) s.(Lazy2Disk)
  | do_sync => lazy2_sync(s)
  | do_crash => mklazy2 None s.(Lazy2Disk)
  end.

(* XXX maybe we can adopt a use theories from Fs2.v. *)

(* Use two lazy2 disks to implement an atomic disk. reserve 0 for commit record? *)
Record AtomicLazy2 : Set := mkAtomicLazy2 {
  Lazy2Log: lazy2_state;   (* needs to have some structure *)
  Lazy2Data: lazy2_state
}.

Definition AtomicLazy2_init := mkAtomicLazy2 (mklazy2 None 0) (mklazy2 None 0).

Inductive invocation : Set :=
  | do_read: invocation
  | do_write: nat -> invocation
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
