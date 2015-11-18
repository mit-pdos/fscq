Require Import EventCSL.
Require Import EventCSLauto.
Require Import Locking.
Require Import ConcurrentCache.
Require Import Star.
Import List.
Import List.ListNotations.

Open Scope list.

Definition block0 : addr := $0.

Module Type TwoBlockVars (Sem:Semantics).
  Import Sem.
  Parameter stateVars : variables Scontents [ID:Type].
End TwoBlockVars.

Module TwoBlockTransitions (Sem:Semantics)
  (CVars:CacheVars Sem)
  (TBVars:TwoBlockVars Sem).

  Module CacheTransitions := CacheTransitionSystem Sem CVars.
  Definition GDisk := CacheTransitions.GDisk.

  Import Sem.
  Import TBVars.

  Definition BOwner := get HFirst stateVars.

  Definition twoblockR (tid:ID) : Relation Scontents :=
    fun s s' =>
      get BOwner s <> tid ->
      get GDisk s block0 = get GDisk s' block0.

  Definition twoblockI : Invariant Mcontents Scontents :=
    fun m s d => True.

  Definition lockR (_:ID) : Relation Scontents :=
    fun s s' => True.

  Definition lockI : Invariant Mcontents Scontents :=
    fun m s d => True.

End TwoBlockTransitions.

Module Type TwoBlockSemantics (Sem : Semantics)
  (CVars : CacheVars Sem)
  (TBVars : TwoBlockVars Sem).

  Import Sem.
  Import TBVars.

  Module TBTrans := TwoBlockTransitions Sem CVars TBVars.
  Import TBTrans.

  Axiom twoblock_relation_holds : forall tid,
    rimpl (R tid) (twoblockR tid).

  Axiom twoblock_relation_preserved : forall tid s s' s'',
    R tid s s' ->
    modified stateVars s' s'' ->
    twoblockR tid s' s'' ->
    R tid s s''.
End TwoBlockSemantics.

Module TwoBlocks (Sem:Semantics)
  (CVars:CacheVars Sem)
  (CSem:CacheSemantics Sem CVars)
  (TBVars:TwoBlockVars Sem)
  (TBSem:TwoBlockSemantics Sem CVars TBVars).
  Module CacheM := Cache Sem CVars CSem.
  Import CacheM.
  Import TBSem.

  Definition write_yield_read {T} rx a v' : prog _ _ T :=
    disk_write a v';;
      Yield;;
      v <- disk_read a;
      rx v.

End TwoBlocks.
