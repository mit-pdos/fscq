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
Require Import Rec.
Require Import Arith.
Require Import GenericArray.

Import EqNotations.

Module Type RecArrayParams.

Parameter RAStart : nat.
Parameter RALen: nat.
Parameter itemtype : Rec.type.
Parameter items_per_valu : nat.
Axiom items_per_valu_ok : Rec.len itemtype * items_per_valu = valulen.

End RecArrayParams.

Module RecArray (Params:RecArrayParams).

  Import Params.

  Definition item := Rec.data itemtype.
  Definition item0 := @Rec.of_word itemtype $0.
  Definition blocktype : Rec.type := Rec.ArrayF itemtype items_per_valu.
  Definition block := Rec.data blocktype.
  Definition block0 := @Rec.of_word blocktype $0.
  Theorem blocksz_ok : valulen = Rec.len blocktype.
  Proof.
    cbn.
    rewrite mult_comm.
    apply (eq_sym items_per_valu_ok).
  Qed.

  Corollary blocksz_ok' : Rec.len blocktype = valulen.
  Proof.
    exact (eq_sym blocksz_ok).
  Qed.

  Definition valu_to_wreclen (v : valu) : word (Rec.len blocktype).
  Proof.
    refine (rew _ in v).
    exact blocksz_ok.
  Defined.

  Definition wreclen_to_valu (v : word (Rec.len blocktype)) : valu.
  Proof.
    refine (rew _ in v).
    exact blocksz_ok'.
  Defined.

  Definition rep_block (b : block) : valu := wreclen_to_valu (Rec.to_word b).
  Definition valu_to_block (v : valu) : block := Rec.of_word (valu_to_wreclen v).

  Lemma valu_wreclen_id : forall w, valu_to_wreclen (wreclen_to_valu w) = w.
  Proof.
    unfold valu_to_wreclen, wreclen_to_valu; intros.
    eq_rect_simpl; auto.
  Qed.

  Lemma rep_valu_id : forall b, Rec.well_formed b -> valu_to_block (rep_block b) = b.
  Proof.
    unfold valu_to_block, rep_block.
    intros.
    rewrite valu_wreclen_id.
    apply Rec.of_to_id; assumption.
  Qed.

  Lemma wreclen_valu_id : forall v,
    wreclen_to_valu (valu_to_wreclen v) = v.
  Proof.
    unfold valu_to_wreclen, wreclen_to_valu.
    intros.
    eq_rect_simpl; auto.
  Qed.

  Lemma valu_rep_id : forall v,
    rep_block (valu_to_block v) = v.
  Proof.
    unfold rep_block, valu_to_block; intros.
    rewrite Rec.to_of_id.
    apply wreclen_valu_id.
  Qed.

  Tactic Notation "assert done" :=
    let n := numgoals in guard n = 0.

  (* array_item_pairs *)
  Definition rep_blocks (vs : list block) : @pred addr _ (const valu) :=
    ([[ length vs = RALen ]] *
     [[ Forall Rec.well_formed vs ]] *
     array ($ RAStart) (map rep_block vs) $1)%pred.

  Definition rep_items (vs : list item) :=
    (exists vs_nested, rep_blocks vs_nested *
                  [[ vs = concat vs_nested ]])%pred.

  Module Type RecArrayVars (SemVars:SemanticsVars).
    Import SemVars.
    Parameter memVars : variables Mcontents [BusyFlag:Type].
    Parameter stateVars : variables Scontents [BusyFlagOwner:Type;
                                                list item;
                                                list item].

    Axiom stateVars_no_confusion : NoDup (hmap var_index stateVars).
  End RecArrayVars.

  Module RecArrayTransitions (SemVars:SemanticsVars)
         (CVars:CacheVars SemVars)
         (RAVars: RecArrayVars SemVars).

    Module CacheTransitions := CacheTransitionSystem SemVars CVars.
    Import CacheTransitions.

    Import SemVars RAVars.

    Definition Lock := ltac:(hget 0 memVars).
    Definition GLock := ltac:(hget 0 stateVars).
    Definition Items0 := ltac:(hget 1 stateVars).
    Definition Items := ltac:(hget 2 stateVars).

    Definition recarrayR (tid:ID) : Relation Scontents :=
      fun s s' =>
        lock_protocol (get GLock) tid s s' /\
        lock_protects (get GLock) (get Items) tid s s'.

    Definition recarrayI : Invariant Mcontents Scontents :=
      fun m s d =>
        ghost_lock_invariant (get Lock m) (get GLock s) /\
        (get GLock s = NoOwner -> get Items0 s = get Items s) /\
        exists F, (get GDisk0 s |= F * rep_items (get Items0 s))%judgement.

  End RecArrayTransitions.

  Module Type RecArraySemantics
         (SemVars:SemanticsVars)
         (Sem:Semantics SemVars)
         (CVars:CacheVars SemVars)
         (CSem: CacheSemantics SemVars Sem CVars)
         (RAVars:RecArrayVars SemVars).

    Import HlistNotations.

    Import Sem CSem.
    Module RATransitions := RecArrayTransitions SemVars CVars RAVars.
    Import RATransitions.

    Axiom recarray_relation_holds : forall tid,
        rimpl (R tid) (recarrayR tid).

    Axiom recarray_relation_preserved : forall tid s s',
        modified [( GLock; Items )] s s' ->
        recarrayR tid s s' ->
        R tid s s'.

    Axiom recarray_invariant_holds : forall m s d,
        Inv m s d ->
        recarrayI m s d.

    Axiom recarray_invariant_preserved : forall m s d m' s' d',
        Inv m s d ->
        modified [( Lock )] m m' ->
        modified [( GLock; Items )] s s' ->
        recarrayI m' s' d' ->
        cacheI m' s' d' ->
        Inv m' s' d'.

  End RecArraySemantics.

  Module RecArray
         (SemVars:SemanticsVars)
         (Sem:Semantics SemVars)
         (CVars:CacheVars SemVars)
         (CSem: CacheSemantics SemVars Sem CVars)
         (RAVars:RecArrayVars SemVars)
         (RASem: RecArraySemantics SemVars Sem CVars CSem RAVars).
    Import Sem.
    Module CacheM := Cache SemVars Sem CVars CSem.
    Import CacheM.
    Import CSem.Transitions.
    Import RASem.
    Import RATransitions.

    Definition rep (vs: list item) : type_pred Scontents :=
      (exists l vs0, haddr GLock |-> l * haddr Items0 |-> vs0 * haddr Items |-> vs)%pred.

    Ltac derive_local :=
      match goal with
      | [ H: Inv _ _ _ |- _ ] =>
        learn that (recarray_invariant_holds H)
      | [ H: R _ _ _ |- _ ] =>
        learn that (recarray_relation_holds H)
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
           eapply recarray_relation_preserved
         | [ |- Inv _ _ _ ] =>
           eapply recarray_invariant_preserved
         end.

    Definition block_idx i :=
      RAStart + (i / items_per_valu).

    Definition off_idx i :=
      i mod items_per_valu.

    Definition get_block_offset (b: block) (off: nat) : item :=
      selN b off item0.

    Definition get_item {T} i rx : prog Mcontents Scontents T :=
      let idx := $ (block_idx i) in
      let off := off_idx i in
      lock idx;;
           v <- read idx;
        unlock idx;;
               let b := valu_to_block v in
               rx (get_block_offset b off).

    Polymorphic Theorem get_item_ok : forall i,
        stateS TID: tid |-
        {{ Fs Fs' vs vd,
         | PRE d m s0 s:
             hlistmem s |= Fs * rep vs * CacheM.rep vd /\
             Inv m s d /\
             get GLock s = Owned tid /\
             preserves' (fun s:S => hlistmem s) (star (othersR R tid)) Fs Fs'
                        (fun s => rep (get Items s) * CacheM.rep (get GDisk s))%pred /\
             R tid s0 s
         | POST d' m' s0' s' r:
             exists vs' vd',
               hlistmem s' |= Fs' * rep vs' * CacheM.rep vd' /\
               Inv m' s' d' /\
               r = selN vs i item0 /\
               R tid s0' s'
        }} get_item i.
    Proof.
    Abort.


  End RecArray.

End RecArray.