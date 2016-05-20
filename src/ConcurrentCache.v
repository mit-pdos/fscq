Require Import CoopConcur.
Require Import CoopConcurAuto.
Require Import Protocols.
Require Import Locking.
Require Import Star.
Import List.ListNotations.
Import Hlist.HlistNotations.

Require Import MemCache.

Section ConcurrentCache.

  Variable Sigma:State.

  Definition CacheSigma := defState [Flags; Cache] [Locks addr; Cache; DISK].

  Variable cacheProj : StateProj Sigma CacheSigma.

  (* memory variables *)

  Definition mLocks := ltac:(hget 0 (memVars cacheProj)).
  Definition mCache := ltac:(hget 1 (memVars cacheProj)).

  (* abstraction ("virtual") variables *)

  Definition vLocks := ltac:(hget 0 (abstractionVars cacheProj)).
  Definition vCache := ltac:(hget 1 (abstractionVars cacheProj)).
  Definition vDisk := ltac:(hget 2 (abstractionVars cacheProj)).

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

  Variable delta:Protocol Sigma.

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

  Definition CacheProtocol : Protocol Sigma :=
    defProtocol cacheI cacheR cacheR_trans_closed.

  Hypothesis cacheProtocolDerive : SubProtocol delta CacheProtocol.
  Hypothesis cacheProtocolRespected : SubProtocolUnder
                                        (privateVars [( mLocks; mCache )] [( vLocks; vCache )])
                                        CacheProtocol delta.

  Definition cache_maybe_read {T} a rx : prog Sigma T :=
    c <- Get mCache;
      rx (cache_val c a).

  Definition cache_write {T} a v rx : prog Sigma T :=
    c <- Get mCache;
      let c' := cache_add c a (Dirty v) in
      Assgn mCache c';;
            rx tt.

  (* TODO: add ghost updates for reader state *)
  Definition AsyncRead {T} a rx : prog Sigma T :=
    StartRead a;;
              Yield a;;
              v <- FinishRead a;
      rx v.

  Definition lock {T} (a: addr) rx : prog Sigma T :=
    tid <- GetTID;
      wait_for mLocks (is_open #a) a;;
               l <- Get mLocks;
      Assgn mLocks (set_locked l #a);;
            GhostUpdate
            (fun s =>
               let l := get vLocks s in
               let l' := upd_lock l a (Owned tid) in
               set vLocks l' s);;
            rx tt.

  Definition cache_fill {T} a rx : prog Sigma T :=
    v <- AsyncRead a;
      c <- Get mCache;
      let c' := cache_add c a (Clean v) in
      Assgn mCache c';;
            rx tt.

End ConcurrentCache.