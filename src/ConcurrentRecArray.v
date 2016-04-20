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
    now eq_rect_simpl.
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
    now eq_rect_simpl.
  Qed.

  Lemma valu_rep_id : forall v,
    rep_block (valu_to_block v) = v.
  Proof.
    unfold rep_block, valu_to_block; intros.
    rewrite Rec.to_of_id.
    apply wreclen_valu_id.
  Qed.

  (* temporarily explicitly say readers are None *)
  (* TODO: eventually cache should not expose readers anywhere *)
  Definition rep_block' b : wr_set := (rep_block b, None).

  (* array_item_pairs *)
  Definition rep_blocks (vs : list block) : @pred addr _ (const wr_set) :=
    ([[ length vs = RALen ]] *
     [[ Forall Rec.well_formed vs ]] *
     array ($ RAStart) (map rep_block' vs) $1)%pred.

  Definition rep_blocks_except (vs: list block) i : @pred addr _ (const wr_set) :=
    ([[ length vs = RALen ]] *
     [[ Forall Rec.well_formed vs ]] *
     let blocks := map rep_block' vs in
     array ($ RAStart) (firstn i blocks) $1 *
     array ($ RAStart ^+ $1) (skipn (i+1) blocks) $1)%pred.

  Polymorphic Theorem rep_blocks_split : forall vs i,
      i < RALen ->
      rep_blocks vs <=p=> rep_blocks_except vs i * ($ (RAStart) ^+ $(i)) |-> rep_block' (selN vs i block0).
  Proof.
    unfold rep_blocks, rep_blocks_except; split; intros; cancel.
  Admitted.

  Section Nesting.

    (* group l into a list k long in accum, recurse with k = k0 each time, concatenating all resulting values *)
    Fixpoint nest_list_f A (l: list A) k0 k accum : list (list A) :=
      match l with
      | nil => [accum]
      | a :: l' =>
        match k with
        | 0 => [accum] ++ nest_list_f l' k0 (k0-1) [a]
        | Datatypes.S k' => nest_list_f l' k0 k' (accum ++ [a])
        end
      end.

    Definition nest_list A (l: list A) k : list (list A) :=
      nest_list_f l k k nil.

    Theorem nest_list_f_concat : forall A (l: list A) k0 k accum,
        concat (nest_list_f l k0 k accum) = accum ++ l.
    Proof.
      induction l; cbn; intros; auto.
      destruct k; cbn.
      rewrite IHl; auto.

      rewrite IHl.
      rewrite <- app_assoc; auto.
    Qed.

    Require Import Omega.

    Ltac unify_in :=
      try lazymatch goal with
        | |- In _ _ => eassumption
        end; cbn; try omega.

    Theorem nest_list_f_length : forall k0 A (l: list A) k accum m,
        k < k0 ->
        length accum + k = k0 ->
        length (accum ++ l) = m * k0 ->
        0 < k0 ->
        (forall x, In x (nest_list_f l k0 k accum) -> length x = k0).
    Proof.
      induction l; intros; cbn in *.
      intuition subst.
      destruct m; cbn in *; try omega;
      rewrite app_nil_r in *.
      rewrite H1 in *.
      omega.
      assert (m * (length x + k) >= 0).
      apply Peano.le_0_n.
      omega.

      destruct k; cbn in *.
      intuition subst;
      rewrite plus_0_r in *; auto.
      eapply IHl; unify_in;
      rewrite app_length in *; cbn in *.
      set (n := length accum) in *.
      assert (n + Datatypes.S (length l) - n = m * n - n).
      omega.

      rewrite minus_plus in H0.
      rewrite mult_comm in H0.
      rewrite <- Nat.mul_pred_r in H0.
      rewrite mult_comm in H0.
      eauto.

      eapply IHl; unify_in;
      repeat rewrite app_length in *;
      cbn in *; try omega.
      rewrite <- plus_assoc.
      eauto.
    Qed.

    Theorem nest_list_concat : forall A (l: list A) k,
        concat (nest_list l k) = l.
    Proof.
      intros.
      apply nest_list_f_concat.
    Qed.

    Theorem nest_list_length : forall A (l: list A) k m,
        length l = m * k ->
        0 < length l ->
        0 < k ->
        Forall (fun l => length l = k) (nest_list l k).
    Proof.
      unfold nest_list; intros.
      destruct l, k; cbn in *; try omega.
      rewrite Forall_forall; intros.
      eapply nest_list_f_length;
        unify_in;
        eauto.
    Qed.

  End Nesting.


  (* array_item *)
  Definition rep_items (vs : list item) :=
    rep_blocks (nest_list vs items_per_valu).

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
        exists F, (get GDisk s |= F * lin_point_pred (rep_items (get Items0 s)))%judgement.

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
      (exists l, haddr GLock |-> l * haddr Items |-> vs)%pred.

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

    Theorem preserves'_star : forall AT AEQ V S
                                 (f: S -> @mem AT AEQ V) R F Q F' P,
        preserves' f R F F' (fun s => Q * P s)%pred ->
        preserves' f R (fun s => F s * Q)%pred (fun s => F' s * Q)%pred P.
    Proof.
      unfold preserves'; intros.
      eapply pimpl_apply;
        [ | eapply H; eauto ].
      cancel.
      pred_apply; cancel.
    Qed.

    Theorem preserves'_star_general : forall AT AEQ V S
                                 (f: S -> @mem AT AEQ V) R F Q F' P,
        preserves' f R F F' (fun s => Q s * P s)%pred ->
        preserves' f R (fun s => F s * Q s)%pred (fun s => F' s * Q s)%pred P.
    Proof.
      unfold preserves'; intros.
      eapply pimpl_apply;
        [ | eapply H; eauto ].
      cancel.
      pred_apply; cancel.
    Qed.

    Hint Extern 0 (okToUnify (CacheM.rep _) (CacheM.rep _)) => constructor : okToUnify.

    Require Import Morphisms.

    Polymorphic Instance lin_point_pred_piff : forall A AEQ V,
        Proper (piff ==> piff) (@lin_point_pred A AEQ V).
    Proof.
      firstorder.
    Qed.

    Polymorphic Instance lin_point_pred_special :
      Proper (piff ==> piff) (@lin_latest_pred addr (@weq addrlen) (@const Set addr wr_set)).
    Proof.
      firstorder.
    Qed.

    Theorem lin_point_pred_respects_impl : forall A AEQ V (p q: @pred A AEQ V),
        p =p=> q ->
               lin_point_pred p =p=> lin_point_pred q.
    Proof.
      intros.
      rewrite H.
      auto.
    Qed.

    Goal forall A AEQ V F (p q: @pred A AEQ V),
        p =p=> q ->
               F * lin_point_pred p =p=> F * lin_point_pred q.
    Proof.
      intros.
      rewrite H.
      auto.
    Qed.

    Theorem rewrite_middle : forall A AEQ V (p q q' r: @pred A AEQ V),
        q' =p=> q ->
                p * q' * r =p=> p * q * r.
    Proof.
      intros.
      rewrite H.
      auto.
    Qed.

    Polymorphic Theorem get_item_ok : forall i,
        stateS TID: tid |-
        {{ Fs Fs' F LF F' vs vd,
         | PRE d m s0 s:
             hlistmem s |= Fs s * rep vs * CacheM.rep vd /\
             Inv m s d /\
             get GLock s = Owned tid /\
             preserves' (fun s:S => hlistmem s) (star (othersR R tid)) Fs Fs'
                        (fun s => rep (get Items s) * CacheM.rep (get GDisk s))%pred /\
             (forall P, preserves' (get GDisk) (star (othersR R tid))
                              F F'
                              (fun s => lin_latest_pred (cache_locked tid s P))) /\
             vd |= F s * lin_point_pred (rep_items vs) * lin_latest_pred (cache_locked tid s LF) /\
             R tid s0 s
         | POST d' m' s0' s' r:
             exists vd',
               hlistmem s' |= Fs' s' * rep vs * CacheM.rep vd' /\
               Inv m' s' d' /\
               get GLock s' = Owned tid /\
               vd' |= F' s' * lin_point_pred (rep_items vs) * lin_latest_pred (cache_locked tid s' LF) /\
               r = selN vs i item0 /\
               R tid s0' s'
        }} get_item i.
    Proof.
      intros.
      step pre simplify with try solve [ finish ].

      unfold pred_in in *; pred_apply; cancel.
      assert (vs = get Items s) by admit.
      rewrite H11.
      instantiate (1 := fun s => (Fs s * rep (get Items s))%pred).
      cancel.

      unfold rep_items in H5.
      unfold pred_in in *; pred_apply.
      eapply pimpl_trans.
      apply rewrite_middle.
      Check lin_point_pred_respects_impl.
      assert (i / items_per_valu < RALen) by admit.
      pose proof (rep_blocks_split (nest_list vs items_per_valu) H11).
      destruct H12.
      eapply (lin_point_pred_respects_impl H12).

      unfold block_idx.
      replace ($ (RAStart) ^+ $ (i / items_per_valu)) with (@natToWord addrlen (RAStart + i / items_per_valu)).
      cancel.
      (* need to move block_idx i |-> _ out of lin_point_pred, saying
only block_idx i |-> _, ?; except that this needs to happen before the
existential variable for |->? is created on the right hand side *)

      admit. (* need to move one item out of rep_items, which pretty
      much requires a new "punctured rep" predicate *)

      apply preserves'_star_general; eassumption.

      instantiate (2 := (fun s => F s * lin_point_pred (rep_items (get Items s)))%pred).
    Abort.

  End RecArray.

End RecArray.