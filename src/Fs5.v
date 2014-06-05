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
  | Sync: event     (* XXX don't apply to transactions; i.e., TEnd syncs *)
  | Crash: event    (* what does it mean in begin and end: ignore? *)
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

(* need to nail down spec: 
Theorem test_legal_5:
  forall (d:nat),
    legal [ Read 0 1 ; Read 1 1 ; Crash; TEnd; Write 0 1 ; Write 1 1 ; TBegin] d.
Proof.
  intro.
  repeat constructor.
Qed.
*)

Theorem test_legal_6: 
  forall (d:nat),
    legal [ Read 0 0 ;  Crash ; Write 0 1 ] d.
Proof.
  intro.
  repeat constructor.
Qed.

Theorem test_legal_7:
  forall (d: nat),
    legal [ Read 1 0 ; Crash; Write 1 1; TBegin ] d.
Proof.
  intro.
  repeat constructor.
Qed.

(* A disk whose reads and writes don't fail *)

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

Axiom disk_read_eq:
  forall s a v,
  st_read (st_write s a v) a = v.

Axiom disk_read_same:
  forall s a a' v,
  a = a' -> st_read (st_write s a' v) a = v.

Axiom disk_read_other:
  forall s a a' v,
  a <> a' -> st_read (st_write s a' v) a = st_read s a.

(*
Lemma read_write_commute:
  forall a a' v v' s,
  a <> a' -> st_read (st_write s a v) a' = st_write s a v.
Proof.
Qed.

(st_read (st_write (st_write st_init 0 1) 1 1) 0)

*)

(* The interface to an atomic disk: *)

Inductive invocation : Set :=
  | do_read: nat -> invocation
  | do_write: nat -> nat -> invocation
  | do_begin: invocation
  | do_end: invocation
  | do_crash: invocation.

(* An atomic abstract disk that implements the above interface with the above
spec. The abstract disk has a storage device and a list of actions in a
transactions that haven't been applied yet. They will be applied when the
transaction ends/commits atomically.  *)

Record TDisk: Set := mkTDisk {
  disk : storage;
  pending : list invocation   (* list of pending invocations in a transaction *)
}.

Definition Tdisk_apply (s: TDisk) (i: invocation) (h: history) : TDisk * history :=
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
      (Tdisk_apply s1 i h1)
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
      | _ => let (s2, h2) := (Tdisk_apply s1 i h1) in
        (false, s2, h2)
      end
    end
  | nil => (false, s, h)
  end.

(* plan for getting some confidence (ie., fix spec and implementation): *)
Theorem TDisk_legal_1:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  crush.
  constructor.
Qed.

Theorem TDisk_legal_2:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [do_read 0; do_write 0 1] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  inversion H.
  rewrite disk_read_eq.
  repeat constructor.
Qed.

Theorem TDisk_legal_3:
  forall (l: list invocation) (h:history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) [do_read 1; do_read 0; do_end; do_write 1 1; do_write 0 1; do_begin] [] = (b, s, h) -> legal h d.
Proof.
  intros.
  inversion H.
  repeat rewrite disk_read_eq.

  crush.

  repeat constructor.
Qed.

(* the main unproven theorem: *)
Theorem TDisk_legal:
  forall (l: list invocation) (h: history) (s: TDisk) (b: bool) (d: nat),
    apply_to_TDisk (mkTDisk st_init []) l [] = (b, s, h) -> legal h d.
Proof.
  intros.
  admit.
Qed.

(* Use two disks to implement to implement the same behavior as Tdisk but with a
disk for which read or write to disk can crash (jelle's disk).  *)

Record AtomicDisk : Set := mkAtomicLazy2 {
  LogDisk : storage_fail;
  DataDisk : storage_fail
}.

Definition AtomicLazy2_init := mkAtomicLazy2 st_fail_init st_fail_init.

(* An implementation of the interface using logging.  Tend writes a commit
record, and then applies to the logged updates to the data disk.  On recovery,
atomic disk applies any committed logdisk updates to data disk. *)

(* A refinement proof that every state AtomicDisk can be in is a legal state of
Tdisk. The mapping function is something along the line if there is a commit
record, then the atomic disks DataDisk is Tdisk.disk with pending applied.  If
there is no commit record, then the atomic DataDisk is Tdisk.disk (i.e., w/o
pending applied) Maybe a la Nickolai's coqfs implementation? *)

(* Standard refinement conclusion: because AtomicDisk implements TDisk and Tdisk
is correct, then AtomicDisk is correct. *)
