Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Locking.
Require Import DiskReaders.
Require Import Star.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.

Section ConcurrentCache.

  Definition Sigma := defState [Flags; Cache] [Locks addr; Cache; DISK].

  (* memory variables *)
  Definition mLocks : var (mem_types Sigma) _ := ltac:(hmember 0 (mem_types Sigma)).
  Definition mCache : var (mem_types Sigma) _ := ltac:(hmember 1 (mem_types Sigma)).

  (* abstraction ("virtual") variables *)
  Definition vLocks : var (abstraction_types Sigma) _
    := ltac:(hmember 0 (abstraction_types Sigma)).
  Definition vCache : var (abstraction_types Sigma) _
    := ltac:(hmember 1 (abstraction_types Sigma)).
  Definition vDisk : var (abstraction_types Sigma) _
    := ltac:(hmember 2 (abstraction_types Sigma)).

  Definition cacheR (tid:TID) : Relation Sigma :=
    fun s s' =>
      let ld := get vDisk s in
      let ld' := get vDisk s' in
      let locks := get vLocks s in
      let locks' := get vLocks s' in
      same_domain ld ld' /\
      (* lock protects virtual disk *)
      (forall a, locks a = Owned tid ->
            ld' a = ld a) /\
      lock_protocol tid locks locks'.

  Definition addr_lock (l:Flags) (a:addr) :=
    get_lock l #a.

  Definition cacheI : Invariant Sigma :=
    fun d m s =>
      get mCache m = get vCache s /\
      locks_rep (addr_lock (get mLocks m)) (get vLocks s) /\
      cache_rep d (get vCache s) (get vDisk s).

  Hint Resolve same_domain_refl.
  Hint Resolve lock_protocol_refl.

  Theorem cacheR_trans_closed : forall tid s s',
      star (cacheR tid) s s' ->
      cacheR tid s s'.
  Proof.
    intros.
    apply trans_closed; auto; intuition.
    unfold cacheR; intuition.
    admit.
  Admitted.

  Definition delta : Protocol Sigma :=
    defProtocol cacheI cacheR cacheR_trans_closed.

  Definition cache_maybe_read {T} a rx : prog Sigma T :=
    c <- Get mCache;
      rx (cache_val c a).

  Definition cache_write {T} a v rx : prog Sigma T :=
    tid <- GetTID;
    c <- Get mCache;
      let c' := cache_add c a (Dirty v) in
      _ <- Assgn mCache c';
        _ <- var_update vCache
          (* fix cache *)
          (fun c => cache_add c a (Dirty v));
        _ <- var_update vDisk
          (* update virtual disk *)
          (fun vd => upd vd a (v, Some tid));
        rx tt.

  Definition AsyncRead {T} a rx : prog Sigma T :=
    tid <- GetTID;
      _ <- StartRead a;
      _ <- var_update vDisk
        (fun vd => add_reader vd a tid);
      _ <- Yield a;
      v <- FinishRead a;
      _ <- var_update vDisk
        (fun vd => remove_reader vd a);
      rx v.

  Definition lock {T} (a: addr) rx : prog Sigma T :=
    tid <- GetTID;
      _ <- wait_for mLocks (is_open #a) a;
      l <- Get mLocks;
      _ <- Assgn mLocks (set_locked l #a);
      _ <- var_update vLocks
        (fun l => upd_lock l a (Owned tid));
      rx tt.

  Definition unlock {T} (a: addr) rx : prog Sigma T :=
    l <- Get mLocks;
      _ <- Assgn mLocks (free_lock l #a);
      _ <- var_update vLocks
        (fun l => upd_lock l a NoOwner);
      rx tt.

  Definition cache_fill {T} a rx : prog Sigma T :=
    _ <- lock a;
      v <- AsyncRead a;
      c <- Get mCache;
      let c' := cache_add c a (Clean v) in
      _ <- Assgn mCache c';
        _ <- var_update vCache
          (fun c => cache_add c a (Clean v));
        _ <- unlock a;
        rx tt.

End ConcurrentCache.