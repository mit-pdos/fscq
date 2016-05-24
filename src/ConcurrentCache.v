Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Import List.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.
Require Import WriteBuffer.

Section ConcurrentCache.

  Definition Sigma := defState [Cache; WriteBuffer] [Cache; WriteBuffer; DISK; Disk].

  Section Variables.

    Tactic Notation "var" constr(n) constr(f) :=
      let t := constr:(ltac:(hmember n (f Sigma))) in
      let t' := eval cbn in t in
          exact (t': var (f Sigma) _).

    Tactic Notation "mvar" constr(n) := var n mem_types.
    Tactic Notation "absvar" constr(n) := var n abstraction_types.

    (* memory variables *)
    Definition mCache := ltac:(mvar 0).
    Definition mWriteBuffer := ltac:(mvar 1).

    (* abstraction ("virtual") variables *)
    Definition vCache := ltac:(absvar 0).
    Definition vWriteBuffer := ltac:(absvar 1).
    (* the linearized disk, which evolves at each syscall *)
    Definition vDisk0 := ltac:(absvar 2).
    (* the disk from the perspective of the current syscall *)
    Definition vdisk := ltac:(absvar 3).

  End Variables.

  Definition no_wb_reader_conflict c wb :=
    forall a, cache_get c a = Invalid ->
         wb_get wb a = WbMissing.

  Definition cacheI : Invariant Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      get mWriteBuffer m = get vWriteBuffer s /\
      cache_rep d (get vCache s) (get vDisk0 s) /\
      wb_rep (get vDisk0 s) (get vWriteBuffer s) (get vdisk s) /\
      no_wb_reader_conflict (get vCache s) (get vWriteBuffer s).

  (* not sure whether to say this about vDisk0, vDisk, or both *)
  Definition cacheR (tid:TID) : Relation Sigma :=
    fun s s' =>
      let vd := get vDisk0 s in
      let vd' := get vDisk0 s' in
      same_domain vd vd' /\
      (* a locking-like protocol, but true for any provable program
      due to the program semantics themselves *)
      (forall a v tid', vd a = Some (v, Some tid') ->
                   tid <> tid' ->
                   vd' a = Some (v, Some tid')).

  Hint Resolve same_domain_refl same_domain_trans.
  Hint Resolve lock_protocol_refl.

  Theorem cacheR_trans_closed : forall tid s s',
      star (cacheR tid) s s' ->
      cacheR tid s s'.
  Proof.
    intro tid.
    apply trans_closed; unfold cacheR; intuition eauto.
  Qed.

  Definition delta : Protocol Sigma :=
    defProtocol cacheI cacheR cacheR_trans_closed.

  (* abstraction helpers *)

  Definition modify_cache (up: Cache -> Cache) rx : prog Sigma :=
    c <- Get mCache;
      _ <- Assgn mCache (up c);
      _ <- var_update vCache up;
      rx tt.

  Definition modify_wb (up: WriteBuffer -> WriteBuffer) rx : prog Sigma :=
    wb <- Get mWriteBuffer;
      _ <- Assgn mWriteBuffer (up wb);
      _ <- var_update vWriteBuffer up;
      rx tt.

  (** safe read: returns None upon cache miss  *)
  Definition cache_maybe_read a rx : prog Sigma :=
    c <- Get mWriteBuffer;
      match wb_val c a with
      | Some v => rx (Some v)
      | None =>
        c <- Get mCache;
          rx (cache_val c a)
      end.

  Definition AsyncRead a rx : prog Sigma :=
    tid <- GetTID;
      _ <- StartRead_upd a;
      (* note that no updates to Disk are needed since the readers are
    hidden *)
      _ <- var_update vDisk0
        (fun vd => add_reader vd a tid);
      _ <- Yield a;
      v <- FinishRead_upd a;
      _ <- var_update vDisk0
        (fun vd => remove_reader vd a);
      rx v.

  Definition cache_fill a rx : prog Sigma :=
      (* invalidating + adding a reader makes the address locked,
      expressed via a reader locking protocol and restrictions on
      readers in cache_rep *)
    _ <- modify_cache (fun c => cache_invalidate c a);
      v <- AsyncRead a;
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      rx v.

  (** buffer a new write: fails (returns false) if the write overlaps
  with the address being read filled *)
  Definition cache_write a v rx : prog Sigma :=
    c <- Get mCache;
      match cache_get c a with
      | Invalid => rx false
      | _ =>
        _ <- modify_wb (fun wb => wb_write wb a v);
          _ <- var_update vdisk
            (fun vd => upd vd a v);
          rx true
      end.

  (** low level operation to move one value to the mCache *)
  Definition wb_evict a v rx : prog Sigma :=
    _ <- modify_cache (fun c => cache_add c a (Dirty v));
      _ <- var_update vDisk0
        (fun vd => upd vd a (v, None));
      rx tt.

  (** commit all the buffered writes into the global cache

    safety is provided by the invariant no_wb_reader_conflict enforced
    by cache_write's checks *)
  Definition cache_commit rx : prog Sigma :=
    c <- Get mCache;
      wb <- Get mWriteBuffer;
      (* need to wb_evict everything in wb_entries wb; requires list
      For loop *)
      _ <- Assgn mWriteBuffer emptyWriteBuffer;
      rx tt.

  (** abort all buffered writes, restoring vDisk0 *)
  Definition cache_abort rx : prog Sigma :=
    _ <- Assgn mWriteBuffer emptyWriteBuffer;
      _ <- GhostUpdate (fun s =>
                         let vd' := hide_readers (get vDisk0 s) in
                         set vdisk vd' s);
      rx tt.


End ConcurrentCache.