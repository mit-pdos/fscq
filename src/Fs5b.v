Require Import List.
Require Import CpdtTactics.
Require Import Arith.
Require Import Le.
Import ListNotations.

(* An implementation of the Fs5 interface using a logging disk.  Tend writes a
commit record, and then applies to the logged updates to the data disk.  On
recovery, atomic disk applies any committed logdisk updates to data disk. *)

(* Borrowed from Fs5: *)
Definition value := nat.
Definition block := nat.
Definition addr := nat.
Definition val := nat.

Definition trans := nat.


Parameter storage : Set.
Parameter st_init  : storage.
Parameter st_write : storage -> addr -> val -> option storage.
Parameter st_read  : storage -> addr -> option val.

Axiom st_eq:
  forall s a wv s' v,
  st_write s a wv = Some s' ->
  st_read s' a = Some v ->  v = wv.

Axiom st_ne:
  forall s a a' wv s' v v',
  a <> a' ->
  st_write s a wv = Some s' ->
  st_read s  a' = Some v ->
  st_read s' a' = Some v' ->  v = v'.

Axiom st_read_init:
  forall a v, st_read st_init a = Some v -> v = 0.

Inductive invocation : Set :=
  | do_read: block -> invocation
  | do_write: block -> value -> invocation
  | do_begin: trans-> invocation
  | do_end: trans -> invocation
  | do_sync_trans: trans -> invocation.

Inductive result : Set :=
  | rs_read: value -> result
  | rs_bool: bool -> result
  | rs_void: result.


(* A logging disk has an index disk (which stores the block number b to be
written) and a value disk that stores the value to be written to block b.  It
also stores the end of the log, index, which will be recovered on reboot. *)
Record LogDisk : Set := mkLogDisk {
  Size : nat;
  Index : nat;
  LogIndexDisk : storage;
  LogValueDisk : storage 
}.

Definition LogDisk_init := mkLogDisk 100 100 st_init st_init.

(* An atomic disk has two disks: a logging and data disk *)
Record AtomicDisk : Set := mkAtomicDisk {
  Log : LogDisk;
  Data : storage
}.

Definition AtomicDisk_init := mkAtomicDisk LogDisk_init st_init.

Definition read_disk (s:storage) (b:block) : value :=
  match (st_read s b) with
  | Some v => v
  | None   => 0  (* TODO: recovery *)
  end.

Definition write_disk (s:storage) (b:block) (v:value) : storage :=
  match (st_write s b v) with
    | Some d => d
    | None   => s  (* TODO: recovery *)
  end.

(* XXX recovery for logdisk should find end of log, i.e., index, so maybe don't hide
the need for recovery from logdisk_write and logdisk_read *)

(* Write a log entry: first the value disk and then the index disk, so that there
always a value for an index. *)
Definition logdisk_write (s:LogDisk) (b:block) (v:value) : LogDisk :=
  let d := write_disk s.(LogValueDisk) s.(Index) v in
  let d1 := write_disk s.(LogIndexDisk) s.(Index) b in
    mkLogDisk s.(Size) (s.(Index)-1) d1 d.

(* None means log entry wasn't for b *)
Definition logdisk_read (s:LogDisk) (b:block) : option value :=
  let v := read_disk s.(LogIndexDisk) b in
  if eq_nat_dec v 0 then None
  else Some (read_disk s.(LogValueDisk) b).

(* XXX lemma: there is always a value for an index on the LogDisk *)

(* Scan the log for write to block b and read the last write b, if any. *)
Fixpoint scan_reverse_uncommitted_write (index: nat) (s : LogDisk) (b:block) : option value :=
  match index with
  | O => None
  | S n =>
    match logdisk_read s index with
    | None => scan_reverse_uncommitted_write n s b (* continue scan of log *)
    | Some v => Some v
    end
  end.

Definition logdisk_read_last_write (s:LogDisk) (b:block) : option value :=
  scan_reverse_uncommitted_write s.(Index) s b.

(* XXX lemma: logdisk_read_last_write returns last uncommitted write for b, if b in log *)

(* An implementation of the interface using logging.  Tend writes a commit
record, and then applies to the logged updates to the data disk.  On recovery,
atomic disk applies any committed logdisk updates to data disk. *)

Fixpoint TDisk_commit (s:TDisk) (p:list invocation): TDisk :=
  match p with
  | nil => s
  | i :: rest => match i with
    | do_write b v =>
        let s' := TDisk_commit s rest in
        TDisk_write_disk s' b v
    | _ => (* ignore, should not happen *)
        TDisk_commit s rest
    end
  end.

Definition TDisk_apply (s: AtomicDisk) (i: invocation) : TDisk * result :=
  Match i with
    | do_read b => match (atomic_read_uncommitted s.(LogDisk) b) with
                     | Some v => (s, rs_read v)
                     | None => TDisk_read_disk s b
                   end
    | do_write b v =>
      (mkTDisk s.(disk) true ((do_write b v) :: s.(pending)), rs_void)
    | do_sync b =>       (s, rs_bool false)
    | do_begin t =>      (s, rs_bool false)
    | do_end _ =>
      let s' := TDisk_commit s s.(pending) in
      (mkTDisk s'.(disk) false nil, rs_bool true)
    | do_sync_trans t => (s, rs_bool false)
  end

  else

    match i with
      | do_read b =>       TDisk_read_disk s b
      | do_write b v =>    (TDisk_write_disk s b v, rs_void)
      | do_sync b =>       (s, rs_bool true) (* do nothing *)
      | do_begin t =>      (mkTDisk s.(disk) true nil, rs_bool true)
      | do_end t =>        (s, rs_bool false)
      | do_sync_trans t => (s, rs_bool true) (* do nothing *)
    end.

