Require Import EventCSL.
Require Import EventCSLauto.
Require Import Automation.
Require Import Locking.
Require Import MemCache2.
Require Import ConcurrentCache2.
Require Import Star.
Import List.
Import List.ListNotations.
Require Import HlistMem.
Require Import Preservation.
Require Import Linearizable2.

Definition block0 : addr := $0.
Definition block1 : addr := $1.

Module Type TwoBlockVars (SemVars:SemanticsVars).
  Import SemVars.
  Parameter stateVars : variables Scontents [ID:Type].
End TwoBlockVars.

Module TwoBlockTransitions (SemVars:SemanticsVars)
  (CVars:CacheVars SemVars)
  (TBVars:TwoBlockVars SemVars).

  Module CacheTransitions := CacheTransitionSystem SemVars CVars.
  Definition GDisk := CacheTransitions.GDisk.
  Definition GDisk0 := CacheTransitions.GDisk0.

  Import SemVars.
  Import TBVars.

  Definition BOwner := ltac:(hget 0 stateVars).

  Definition twoblockR (tid:ID) : Relation Scontents :=
    fun s s' => True.

  Definition twoblockI : Invariant Mcontents Scontents :=
    fun m s d =>
      get GDisk0 s block0 = get GDisk0 s block1.


End TwoBlockTransitions.

Module Type TwoBlockSemantics
  (SemVars: SemanticsVars)
  (Sem : Semantics SemVars)
  (CVars : CacheVars SemVars)
  (TBVars : TwoBlockVars SemVars).

  Import Sem.
  Import TBVars.

  Module TBTrans := TwoBlockTransitions SemVars CVars TBVars.
  Import TBTrans.

  Axiom twoblock_relation_holds : forall tid,
    rimpl (R tid) (twoblockR tid).

  Axiom twoblock_relation_preserved : forall tid s s',
    modified stateVars s s' ->
    twoblockR tid s s' ->
    R tid s s'.

  Axiom twoblock_invariant_holds : forall d m s,
    Inv d m s ->
    twoblockI d m s.

  Axiom twoblock_invariant_preserved : forall d m s d' m' s',
    Inv m s d ->
    twoblockI m' s' d' ->
    modified HNil m m' ->
    modified stateVars s s' ->
    Inv m' s' d'.

End TwoBlockSemantics.

Module TwoBlocks
  (SemVars:SemanticsVars)
  (Sem:Semantics SemVars)
  (CVars:CacheVars SemVars)
  (CSem:CacheSemantics SemVars Sem CVars)
  (TBVars:TwoBlockVars SemVars)
  (TBSem:TwoBlockSemantics SemVars Sem CVars TBVars).
  Import Sem.
  Module CacheM := Cache SemVars Sem CVars CSem.
  Import CacheM.
  Import CSem.Transitions.
  Import TBSem.
  Import TBTrans.

  Definition update_block {T} v' rx : prog _ _ T :=
    lock block0;;
    lock block1;;
    write block0 v';;
    write block1 v';;
    unlock block0;;
    unlock block1;;
    rx tt.

  Ltac derive_local :=
    match goal with
    | [ H: Inv _ _ _ |- _ ] =>
      learn that (twoblock_invariant_holds H)
    | [ H: R _ _ _ |- _ ] =>
      learn that (twoblock_relation_holds H)
    end.

  Ltac simplify_reduce_step ::=
  (* this binding just fixes PG indentation *)
  let unf := autounfold with prog in * in
          deex_local
          || destruct_ands
          || descend
          || subst
          || derive_local
          || unf.

  Ltac solve_global_transitions ::=
  (* match only these types of goals *)
  lazymatch goal with
  | [ |- R _ _ _ ] =>
    eapply twoblock_relation_preserved
  | [ |- Inv _ _ _ ] =>
    eapply twoblock_invariant_preserved
  end.

  Lemma cache_locked_emp : forall s tid,
    cache_locked s tid emp <=p=> emp.
  Proof.
    unfold cache_locked, locks_held, piff, pimpl, emp; split;
      intuition.
    congruence.
  Qed.

  Lemma lin_pred_emp : forall AT AEQ V o,
    @lin_pred AT AEQ V o emp <=p=> emp.
  Proof.
    unfold lin_pred, view, piff, pimpl, emp; split; intros;
      specialize_all AT;
      destruct matches in *.
  Qed.

  (* not sure how else to do this, but the work of proving that the locked
  portion doesn't change should be handled by the cache *)
  Theorem preserves'_any_locked : forall P F tid,
    preserves' (get GDisk) (star (othersR R tid)) F any
      (fun s => lin_pred Latest (cache_locked tid s P)).
  Proof.
  Admitted.

  Theorem preserves'_any_cache_rep : forall F tid,
    preserves' (fun s => hlistmem s) (star (othersR R tid)) F any
      (fun s => CacheM.rep (get GDisk s)).
  Proof.
    unfold preserves', rep; intros.
    apply sep_star_comm.
    apply pimpl_exists_r_star.
    apply exis_to_exists.
    exists (get GCache s').
    apply pimpl_exists_r_star.
    apply exis_to_exists.
    exists (get GLocks s').
    (* this is true, but could be difficult to prove -
    for one thing, the proof of sep_star must rely on
    the no_confusion_stateVars axiom *)
  Admitted.

  Polymorphic Theorem update_block_ok : forall v',
    stateS TID: tid |-
    {{ Fs vd vd0 v,
     | PRE d m s0 s: hlistmem s |= Fs * haddr GDisk0 |-> vd0 * CacheM.rep vd /\
                     Inv m s d /\
                     vd0 |= any * block0 |-> v /\
                     R tid s0 s
     | POST d' m' s0' s' _:
      exists Fs' vd' vd0',
        hlistmem s' |= Fs' * haddr GDisk0 |-> vd0' * CacheM.rep vd' /\
        Inv m' s' d' /\
        vd0' |= any * block0 |-> v' /\
        R tid s0' s'
    }} update_block v'.
Proof.
  time "hoare" hoare pre simplify with try solve [ finish ].

  instantiate (2 := (any * block1 |->?)%pred).
  instantiate (1 := emp).
  admit.
  eapply preserves'_any_cache_rep.
  instantiate (1 := any).
  admit. (* block0 and block1 should still point to something *)
  eapply preserves'_any_cache_rep.
  instantiate (1 := any).
  admit.

  instantiate (1 := v0).
  instantiate (1 := (block1 |-> (v1, None))%pred).
  instantiate (1 := any).
  admit.

  eapply preserves'_any_cache_rep.
  eapply preserves'_any_locked.
  Ltac lin_pred_apply :=
    idtac;
    match goal with
    | [ H: (?vd |= ?F' * lin_pred ?o (cache_locked ?tid ?s ?LF'))%judgement
      |- (?vd |= ?F * lin_pred ?o (cache_locked ?tid ?s ?LF))%judgement ] =>
      assert (LF' =p=> LF)
    end.
  lin_pred_apply.
  (* cancel works here but is extremely slow (even pimpl setoid rewriting is
  very slow) *)
  instantiate (1 := v1).
  instantiate (1 := (block0 |-> (v', None))%pred).
  admit.
  instantiate (1 := any).
  admit.

  instantiate (1 := any).
  admit.
  eapply preserves'_any_locked.
  apply CSem.cache_invariant_holds; auto.

  lin_pred_apply.
  instantiate (1 := v').
  instantiate (1 := v').
  instantiate (1 := emp).
  admit.
  instantiate (1 := any).
  admit.
  (* need to make sure block1 still points to something... *)
  (* not sure why we only know vd0' has block0 |-> v' *)
  admit.

  (* oops, unlock_ok probably doesn't need R s0 s in its precondition *)
  admit.

  (* need to re-prove Inv: know that cacheI holds and can prove that
  twoblockI holds - probably want some extra information about other things
  not changing; unlock only changes GDisk0, after all. *)
  admit.

  (* another case of forgetting facts about GDisk0 for the other block *)
  admit.

  (* need to re-prove R: again, need some extra promises from Cache that
  other variables don't change so we can use twoblock_relation_preserved
  to prove this *)
  admit.
Admitted.

End TwoBlocks.

Module MySemanticsVars <: SemanticsVars.
  Definition Mcontents : list Type := [BlockCache; ConcurrentCache2.Locks.M].
  Definition Scontents : list Type := [ID:Type; linearized DISK; Disk;
    linearized BlockFun; ConcurrentCache2.Locks.S].
End MySemanticsVars.

Theorem NoDup_nat : forall (l: list nat),
  l = nodup nat_dec l ->
  NoDup l.
Proof.
  intros.
  rewrite H.
  apply NoDup_nodup.
Qed.

Module MyCacheVars <: CacheVars MySemanticsVars.
  Import HlistNotations.
  Import MySemanticsVars.

  Definition memVars : variables Mcontents [BlockCache; ConcurrentCache2.Locks.M] :=
    [( HFirst; HNext HFirst )].

  Definition stateVars : variables Scontents [linearized DISK; Disk;
    linearized BlockFun; ConcurrentCache2.Locks.S] :=
    [( HNext HFirst; HNext (HNext HFirst);
      HNext (HNext (HNext HFirst));
      HNext (HNext (HNext (HNext HFirst))) )].

  Theorem no_confusion_memVars : NoDup (hmap var_index memVars).
  Proof.
    apply NoDup_nat; auto.
  Qed.

  Theorem no_confusion_stateVars : NoDup (hmap var_index stateVars).
  Proof.
    apply NoDup_nat; auto.
  Qed.
End MyCacheVars.

Module MyTBVars <: TwoBlockVars MySemanticsVars.
  Import MySemanticsVars.
  Import HlistNotations.
  Definition stateVars : variables Scontents [ID:Type] :=
    [( HFirst )].
End MyTBVars.

Module TBTransitions := TwoBlockTransitions MySemanticsVars MyCacheVars MyTBVars.
Import TBTransitions.
Import CacheTransitions.

Module MySemantics <: Semantics MySemanticsVars.
  Import MySemanticsVars.

  Definition R tid s s' :=
    cacheR tid s s' /\
    twoblockR tid s s'.

  Definition Inv m s d :=
    cacheI m s d /\
    twoblockI m s d.

  Theorem R_trans : forall tid s s',
    star (R tid) s s' ->
    R tid s s'.
  Proof.
    intros.
    eapply trans_closed_from_refl_trans; eauto.
    unfold R; intuition.
    apply cacheR_refl.
    intros.
    unfold R in *; intuition.
    eapply cacheR_trans; eauto.
  Qed.

End MySemantics.

Module MyCacheSemantics <: CacheSemantics MySemanticsVars MySemantics MyCacheVars.

  Module Transitions := CacheTransitionSystem MySemanticsVars MyCacheVars.

  Import MySemantics.
  Export Transitions.
  Import TBTransitions.

  Import HlistNotations.

  Theorem cache_invariant_holds : forall m s d,
    Inv m s d ->
    cacheI m s d.
  Proof.
    unfold Inv; intuition.
  Qed.

  Theorem cache_relation_holds : forall tid,
      rimpl (R tid) (cacheR tid).
  Proof.
    unfold rimpl, R; intuition.
  Qed.

  Transparent get.

  Theorem cache_invariant_preserved : forall m s d m' s' d',
      Inv m s d ->
      cacheI m' s' d' ->
      modified [( Cache; MLocks )] m m' ->
      modified [( GDisk; GCache; GLocks )] s s' ->
      Inv m' s' d'.
  Proof.
    unfold Inv; intuition.
    unfold twoblockI in *.
    rewrite <- H2; auto; intros.
    apply hin_iff_index_in in H; cbn in *.
    intuition.
  Qed.

  Theorem cache_relation_preserved : forall tid s s',
      (* can actually also assume anything about s that Inv m s d
      implies (forall m and d) *)
      modified [( GDisk; GCache; GLocks )] s s' ->
      cacheR tid s s' ->
      R tid s s'.
  Proof.
    unfold R; intuition.
    unfold twoblockR; auto.
  Qed.

End MyCacheSemantics.

Module MyTBSemantics <: TwoBlockSemantics MySemanticsVars MySemantics MyCacheVars MyTBVars.
  Import MySemantics.
  Import MyTBVars.

  Module TBTrans := TwoBlockTransitions MySemanticsVars MyCacheVars MyTBVars.
  Import TBTrans.

  Theorem twoblock_relation_holds : forall tid,
    rimpl (R tid) (twoblockR tid).
  Proof.
    unfold R, rimpl; intuition.
  Qed.

  Transparent get.

  Theorem twoblock_relation_preserved : forall tid s s',
    modified stateVars s s' ->
    twoblockR tid s s' ->
    R tid s s'.
  Proof.
    unfold R, stateVars; intuition.
    unfold cacheR.
    repeat rewrite H; auto; intros.
    apply cacheR_refl.

    apply hin_iff_index_in in H1; cbn in *; intuition.
    apply hin_iff_index_in in H1; cbn in *; intuition.
  Qed.

  Theorem twoblock_invariant_holds : forall d m s,
    Inv d m s ->
    twoblockI d m s.
  Proof.
    unfold Inv; intuition.
  Qed.

  Theorem twoblock_invariant_preserved : forall d m s d' m' s',
    Inv m s d ->
    twoblockI m' s' d' ->
    modified HNil m m' ->
    modified stateVars s s' ->
    Inv m' s' d'.
  Proof.
    unfold Inv; intuition.
    unfold cacheI in *.
    repeat rewrite <- H2; auto; intros;
      try match goal with
      | [ H: HIn _ _ |- _ ] =>
        apply hin_iff_index_in in H; cbn in H; try solve [ intuition ]
      end.
    repeat rewrite <- H1; auto; intros;
      try match goal with
      | [ H: HIn _ _ |- _ ] =>
        apply hin_iff_index_in in H; cbn in H; try solve [ intuition ]
      end.
    intuition.
    admit. (* oops, cacheI maintained some fact about d that is now lost *)
  Admitted.

End MyTBSemantics.

Module MyTBImplementation := TwoBlocks MySemanticsVars MySemantics
  MyCacheVars MyCacheSemantics
  MyTBVars MyTBSemantics.
