Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import Preservation.
Require Import MemCache2.
Require Import Automation.
Require Import Locks.
Require Import Linearizable.

Import List.
Import List.ListNotations.

Module AddrM <: Word.WordSize.
                 Definition sz := addrlen.
End AddrM.

Module Addr_as_OT := Word_as_OT AddrM.

Module Locks := Locks.Make(Addr_as_OT).
Import Locks.

Module Type CacheVars (Sem:Semantics).
  Import Sem.
  Parameter memVars : variables Mcontents [BlockCache; Locks.M].
  Parameter stateVars : variables Scontents [linearized DISK; DISK; linearized BlockFun; Locks.S].

  Axiom no_confusion_memVars : NoDup (hmap var_index memVars).
  Axiom no_confusion_stateVars : NoDup (hmap var_index stateVars).
End CacheVars.

Module CacheTransitionSystem (Sem:Semantics) (CVars : CacheVars Sem).
  Import Sem.
  Import CVars.

  Definition Cache := ltac:(hget 0 memVars).
  Definition MLocks := ltac:(hget 1 memVars).

  Definition GDisk := ltac:(hget 0 stateVars).
  Definition GDisk0 := ltac:(hget 1 stateVars).
  Definition GCache := ltac:(hget 2 stateVars).
  Definition GLocks := ltac:(hget 3 stateVars).

  Definition cacheR (tid:ID) : Relation Scontents :=
    fun s s' =>
      let vd := get GDisk0 s in
      let vd' := get GDisk0 s' in
      let c := get GCache s in
      let c' := get GCache s' in
      let locks := get GLocks s in
      let locks' := get GLocks s' in
      same_domain vd vd' /\
      (forall a, lock_transition tid (Locks.get locks a) (Locks.get locks' a)).

  Definition cacheI : Invariant Mcontents Scontents :=
    fun m s d =>
      let mlocks := get MLocks m in
      let locks := get GLocks s in
      let mc := get Cache m in
      let vc := get GCache s in
      let vd0 := get GDisk0 s in
      let vd := get GDisk s in
      cache_fun_rep mc (view NoOwner vc) /\
      (forall a, ghost_lock_invariant (Locks.mem mlocks a) (Locks.get locks a)) /\
      linearized_consistent vd (Locks.get locks) /\
      (forall o, cache_rep (view o vc) (view o vd) d) /\
      vd0 = view NoOwner vd.

End CacheTransitionSystem.

Module Type CacheSemantics (Sem:Semantics) (CVars:CacheVars Sem).

  Module Transitions := CacheTransitionSystem Sem CVars.

  Import Sem.
  Import CVars.
  Import Transitions.

  Axiom cache_invariant_holds : forall m s d,
    Inv m s d ->
    cacheI m s d.

  Axiom cache_relation_holds : forall s s' tid,
      R tid s s' ->
      cacheR tid s s'.

  (* Here need to incorporate linearizability in order to say
  something powerful enough that specs can export Inv/R but can still
  freely modify variables in critical sections. *)

  Axiom cache_invariant_preserved : forall m s d m' s' d',
    Inv m s d ->
    cacheI m' s' d' ->
    (* only memVars/stateVars were modified *)
    modified memVars m m' ->
    modified stateVars s s' ->
    Inv m' s' d'.

  Axiom cache_relation_preserved : forall tid s s' s'',
    R tid s s' ->
    modified stateVars s' s'' ->
    cacheR tid s' s'' ->
    R tid s s''.

End CacheSemantics.