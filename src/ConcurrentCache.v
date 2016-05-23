Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Star.
Require Import DiskReaders.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.

Section ConcurrentCache.

  Definition Sigma := defState [Cache] [Cache; DISK; Disk].

  (* memory variables *)
  Definition mCache : var (mem_types Sigma) _ := ltac:(hmember 0 (mem_types Sigma)).

  (* abstraction ("virtual") variables *)
  Definition vCache : var (abstraction_types Sigma) _
    := ltac:(hmember 0 (abstraction_types Sigma)).
  Definition vDISK : var (abstraction_types Sigma) _
    := ltac:(hmember 1 (abstraction_types Sigma)).
  Definition vDisk : var (abstraction_types Sigma) _
    := ltac:(hmember 2 (abstraction_types Sigma)).

  Definition cacheR (tid:TID) : Relation Sigma :=
    fun s s' =>
      let ld := get vDISK s in
      let ld' := get vDISK s' in
      same_domain ld ld' /\
      (* a locking-like protocol, but true for any provable program
      due to the program semantics themselves *)
      (forall a v tid', ld a = Some (v, Some tid') ->
                   tid <> tid' ->
                   ld' a = Some (v, Some tid')).

  Definition addr_lock (l:Flags) (a:addr) :=
    get_lock l #a.

  Definition cacheI : Invariant Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      cache_rep d (get vCache s) (get vDISK s) /\
      get vDisk s = hide_readers (get vDISK s).

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

  Definition cache_write a v rx : prog Sigma :=
    tid <- GetTID;
      (* may fill an invalid entry - filling thread will notice this
      and keep the new value *)
      _ <- modify_cache (fun c => cache_add c a (Dirty v));
      _ <- var_update vDISK
        (* update virtual disk *)
        (fun vd => upd vd a (v, None));
      _ <- var_update vDisk
        (fun vd => upd vd a v);
      rx tt.

  Definition AsyncRead a rx : prog Sigma :=
    tid <- GetTID;
      _ <- StartRead_upd a;
      (* note that no updates to Disk are needed since the readers are
    hidden *)
      _ <- var_update vDISK
        (fun vd => add_reader vd a tid);
      _ <- Yield a;
      v <- FinishRead_upd a;
      _ <- var_update vDISK
        (fun vd => remove_reader vd a);
      rx v.

  Definition cache_fill a rx : prog Sigma :=
    _ <- modify_cache (fun c => cache_invalidate c a);
      v <- AsyncRead a;
      _ <- modify_cache (fun c => cache_add c a (Clean v));
      (* note that the memory cache has been updated so its
      abstraction must be updated, but the external disk abstractions
      are unaffected by another cache entry *)
      _ <- var_update vCache
        (fun c => cache_add c a (Clean v));
      rx tt.

End ConcurrentCache.