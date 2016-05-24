Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.

Section ConcurrentCache.

  Definition Sigma := defState [Cache; Cache] [Cache; Cache; DISK; DISK; Disk].

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
    Definition vDisk := ltac:(absvar 3).
    (* the public, linearized disk, which hides readers from vDisk0 *)
    Definition vdisk0 := ltac:(absvar 4).

  End Variables.

  Definition cacheI : Invariant Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      get mWriteBuffer m = get vWriteBuffer s /\
      cache_rep d (get vCache s) (get vDisk0 s) /\
      cache_rep (get vDisk0 s) (get vWriteBuffer s) (get vDisk s) /\
      get vdisk0 s = hide_readers (get vDisk0 s).

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

  Definition cache_maybe_read a rx : prog Sigma :=
    c <- Get mCache;
      rx (cache_val c a).

  Definition modify_cache (up: Cache -> Cache) rx : prog Sigma :=
    c <- Get mCache;
      _ <- Assgn mCache (up c);
      _ <- var_update vCache up;
      rx tt.

  Definition cache_maybe_write a v rx : prog Sigma :=
    tid <- GetTID;
      c <- Get mCache;
      match cache_get c a with
      | Invalid => rx false
      | _ =>
        _ <- modify_cache (fun c => cache_add c a (Dirty v));
          _ <- var_update vDisk0
            (* update virtual disk *)
            (fun vd => upd vd a (v, None));
          _ <- var_update vdisk0
            (fun vd => upd vd a v);
          rx true
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
    _ <- modify_cache (fun c => cache_invalidate c a);
      v <- AsyncRead a;
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      rx v.

  Definition cache_writeback a rx : prog Sigma :=
    c <- Get mCache;
      match cache_get c a with
      | Dirty v =>
        _ <- Write a v;
          _ <- Assgn mCache (cache_add c a (Clean v));
          _ <- var_update vCache
            (fun c => cache_add c a (Clean v));
          rx tt
      | _ => rx tt
      end.

End ConcurrentCache.