Require Import EventCSL.
Require Import EventCSLauto.
Require Import Automation.
Require Import Locking.
Require Import MemCache.
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

  Axiom twoblock_invariant_holds : forall d m s,
    Inv d m s ->
    twoblockI d m s.

  Axiom twoblock_invariant_preserved : forall d m s d' m' s',
    Inv m s d ->
    twoblockI m' s' d' ->
    m' = m ->
    modified stateVars s s' ->
    Inv m' s' d'.

End TwoBlockSemantics.

Module TwoBlocks (Sem:Semantics)
  (CVars:CacheVars Sem)
  (CSem:CacheSemantics Sem CVars)
  (TBVars:TwoBlockVars Sem)
  (TBSem:TwoBlockSemantics Sem CVars TBVars).
  Import Sem.
  Module CacheM := Cache Sem CVars CSem.
  Import CacheM.
  Import CSem.Transitions.
  Import TBSem.
  Import TBTrans.

  Ltac solve_global_transitions ::=
  (* match only these types of goals *)
  lazymatch goal with
  | [ |- R _ _ _ ] =>
    eapply twoblock_relation_preserved; [
      solve [ eassumption | eauto ] | .. ]
  | [ |- Inv _ _ _ ] =>
    eapply twoblock_invariant_preserved
(*
  | [ |- inv _ _ _ ] => unfold inv; intuition; try solve_global_transitions
*)
  end;
  unfold lockR, lockI, cacheR, cacheI, (* stateI, *) lockI,
    lock_protects, pred_in;
  repeat lazymatch goal with
  | [ |- forall _, _ ] => progress intros
  | [ |- _ /\ _ ] => split
  end; simpl_get_set.

  Definition write_yield_read {T} v' rx : prog _ _ T :=
    disk_write block0 v';;
    Yield;;
    v <- locked_disk_read block0;
    v <- locked_disk_read (block0 ^+ $1);
    rx v.

  Hint Resolve ptsto_valid_iff.

(*
  Theorem write_yield_read_ok : forall v',
    stateS TID: tid |-
    {{ F v rest,
     | PRE d m s0 s: let vd := virt_disk s in
                     inv m s d /\
                     vd |= F * block0 |-> (Valuset v rest) /\
                     R tid s0 s /\
                     get GCacheL s = Owned tid
     | POST d' m' s0' s' r: let vd' := virt_disk s' in
                            inv m' s' d' /\
                            (exists F' rest', vd' |= F' * block0 |-> (Valuset v' rest')) /\
                            R tid s s' /\
                            r = v' /\
                            get GCacheL s' = Owned tid /\
                            R tid s0' s'
     | CRASH d'c: True
    }} write_yield_read v'.
Proof.
  let simp_step :=
    simplify_step
    || destruct_valusets in
  time "hoare" hoare pre (simplify' simp_step) with finish.
  (* TODO: learn equality of block0 from twoblockR *)
*)

End TwoBlocks.

Module MySemantics <: Semantics.
  Definition Mcontents := [AssocCache ; BusyFlag : Type ].
  Definition Scontents := [DISK ; AssocCache ; BusyFlagOwner : Type ; ID : Type].
  Definition Inv := fun (_ : M Mcontents) (_ : S Scontents) => (emp : DISK_PRED).
  Definition R := fun (_ : ID) (_ _ : S Scontents) => True.

  Theorem R_stutter : forall tid s,
    R tid s s.
  Proof. firstorder. Qed.
End MySemantics.

Module MyCacheVars <: CacheVars MySemantics.
  Definition memVars : variables MySemantics.Mcontents [AssocCache; BusyFlag:Type] :=
    HCons (HFirst) (HCons (HNext HFirst) HNil).
  Definition stateVars : variables MySemantics.Scontents [DISK; AssocCache; BusyFlagOwner:Type] :=
    HCons (HFirst) (HCons (HNext HFirst) (HCons (HNext (HNext HFirst)) HNil)).

  Theorem no_confusion_memVars : NoDup (hmap var_index memVars).
  Proof.
    cbn.
    repeat ( constructor; cbn; firstorder ).
  Qed.

  Theorem no_confusion_stateVars : NoDup (hmap var_index stateVars).
    cbn.
    repeat ( constructor; cbn; firstorder ).
  Qed.
End MyCacheVars.

Module MyCacheSemantics : CacheSemantics MySemantics MyCacheVars.
  Module Transitions := CacheTransitionSystem MySemantics MyCacheVars.

  Theorem cache_invariant_holds : forall m s d,
    MySemantics.Inv m s d ->
    Transitions.cacheI m s d.
  Proof.
    unfold MySemantics.Inv.
    unfold Transitions.cacheI.
  Admitted.

  Theorem cache_relation_holds : forall tid,
    rimpl (MySemantics.R tid) (Transitions.cacheR tid).
  Proof.
    unfold MySemantics.R.
    unfold Transitions.cacheR.
  Admitted.

  Theorem cache_invariant_preserved : forall m s d m' s' d',
    MySemantics.Inv m s d ->
    Transitions.cacheI m' s' d' ->
    modified MyCacheVars.memVars m m' ->
    modified MyCacheVars.stateVars s s' ->
    MySemantics.Inv m' s' d'.
  Proof.
    unfold Transitions.cacheI.
    intros.
    (* XXX this might be broken! *)
  Admitted.

  Theorem cache_relation_preserved : forall tid s s' s'',
    MySemantics.R tid s s' ->
    modified MyCacheVars.stateVars s' s'' ->
    Transitions.cacheR tid s' s'' ->
    MySemantics.R tid s s''.
  Proof.
    unfold Transitions.cacheR.
    intros.
    unfold MySemantics.R; auto.
  Qed.
End MyCacheSemantics.

Module MyTwoBlockVars : TwoBlockVars MySemantics.
  Definition stateVars : variables MySemantics.Scontents [ID:Type] :=
    HCons (HNext (HNext (HNext HFirst))) HNil.
End MyTwoBlockVars.

Module MyTwoBlockSemantics : TwoBlockSemantics MySemantics MyCacheVars MyTwoBlockVars.
  Module TBTrans := TwoBlockTransitions MySemantics MyCacheVars MyTwoBlockVars.

  Theorem twoblock_relation_holds : forall tid,
    rimpl (MySemantics.R tid) (TBTrans.twoblockR tid).
  Proof.
    unfold TBTrans.twoblockR.
    intros.
  Admitted.

  Theorem twoblock_relation_preserved : forall tid s s' s'',
    MySemantics.R tid s s' ->
    modified MyTwoBlockVars.stateVars s' s'' ->
    TBTrans.twoblockR tid s' s'' ->
    MySemantics.R tid s s''.
  Proof.
  Admitted.

  Theorem twoblock_invariant_holds : forall d m s,
    MySemantics.Inv d m s ->
    TBTrans.twoblockI d m s.
  Proof.
    unfold TBTrans.twoblockI.
    auto.
  Qed.

  Theorem twoblock_invariant_preserved : forall d m s d' m' s',
    MySemantics.Inv m s d ->
    TBTrans.twoblockI m' s' d' ->
    m' = m ->
    modified MyTwoBlockVars.stateVars s s' ->
    MySemantics.Inv m' s' d'.
  Proof.
    unfold TBTrans.twoblockI.
    intros; subst.
    (* XXX this is broken *)
  Admitted.

End MyTwoBlockSemantics.

Module TwoBlocksI := TwoBlocks MySemantics MyCacheVars MyCacheSemantics MyTwoBlockVars MyTwoBlockSemantics.
