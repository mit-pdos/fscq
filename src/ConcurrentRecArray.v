Require Import EventCSL.
Require Import EventCSLauto.
Require Import Automation.
Require Import Locking.
Require Import Star.
Import List.
Import List.ListNotations.
Require Import ConcurrentDisk.
Require Import Linearizable2.
Require Import Rec.
Require Import Arith.
Require Import GenericArray.
Import ConcurrentDisk.

Import EqNotations.

Module Locks := ConcurrentDisk.Locks.

Module Type RecArrayParams.

Parameter RAStart : nat.
Parameter RALen: nat.
Parameter itemtype : Rec.type.
Parameter items_per_valu : nat.
Axiom items_per_valu_ok : Rec.len itemtype * items_per_valu = valulen.
Axiom ra_params_bounded : RAStart + RALen < pow2 addrlen.

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

  Definition block_valu (b : block) : valu := wreclen_to_valu (Rec.to_word b).
  Definition valu_block (v : valu) : block := Rec.of_word (valu_to_wreclen v).

  Lemma valu_wreclen_id : forall w, valu_to_wreclen (wreclen_to_valu w) = w.
  Proof.
    unfold valu_to_wreclen, wreclen_to_valu; intros.
    now eq_rect_simpl.
  Qed.

  Lemma block_valu_id : forall b, Rec.well_formed b -> valu_block (block_valu b) = b.
  Proof.
    unfold valu_block, block_valu; intros.
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

  Lemma valu_block_id : forall v,
    block_valu (valu_block v) = v.
  Proof.
    unfold valu_block, block_valu; intros.
    rewrite Rec.to_of_id.
    apply wreclen_valu_id.
  Qed.

  Lemma items_per_valu_not_0 : items_per_valu <> 0.
  Proof.
    intro.
    pose proof items_per_valu_ok.
    rewrite H in H0.
    rewrite <- mult_n_O in H0.
    inversion H0.
  Qed.

  (* array_item_pairs *)
  Definition rep_blocks (vs : list block) : @pred addr _ (const valu) :=
    ([[ length vs = RALen ]] *
     [[ Forall Rec.well_formed vs ]] *
     array ($ RAStart) (map block_valu vs) $1)%pred.

  Definition rep_blocks_except (vs: list block) i : @pred addr _ (const valu) :=
    ([[ length vs = RALen ]] *
     [[ Forall Rec.well_formed vs ]] *
     let blocks := map block_valu vs in
     array ($ RAStart) (firstn i blocks) $1 *
     array ($ RAStart ^+ $1) (skipn (i+1) blocks) $1)%pred.

  Polymorphic Theorem rep_blocks_split : forall vs i,
      i < RALen ->
      rep_blocks vs <=p=> rep_blocks_except vs i * ($ (RAStart) ^+ $(i)) |-> block_valu (selN vs i block0).
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

  Definition rep_blocks' vs_nested (vd: Disk) :=
    length vs_nested = RALen /\
    forall (a:addr), ($ RAStart <= a)%word ->
         (a < $ (RAStart + RALen))%word ->
         vd a = Some (block_valu (sel vs_nested a block0)).

  Definition rep_items' (vs: list item) :=
    rep_blocks' (nest_list vs items_per_valu).

  Module Type RecArrayVars (SemVars:SemanticsVars).
    Import SemVars.
    Parameter stateVars : variables Scontents [list item; list item].

    Axiom stateVars_no_confusion : NoDup (hmap var_index stateVars).
  End RecArrayVars.

  Module RecArrayTransitions (SemVars:SemanticsVars)
         (DVars:DiskVars SemVars)
         (RAVars: RecArrayVars SemVars).

    Module DiskTransitions := DiskTransitionSystem SemVars DVars.
    Import DiskTransitions.

    Import SemVars RAVars.

    Definition Items0 := ltac:(hget 0 stateVars).
    Definition Items := ltac:(hget 1 stateVars).

    Definition recarrayR (tid:ID) : Relation Scontents :=
      fun s s' => True.

    Definition recarrayI : Invariant Mcontents Scontents :=
      fun m s d =>
        rep_items' (get Items0 s) (get GDisk0 s) /\
        (* this is awkward *)
        rep_items' (get Items s) (hide_readers (view Latest (get GDisk s))).

  End RecArrayTransitions.

  Module Type RecArraySemantics
         (SemVars:SemanticsVars)
         (Sem:Semantics SemVars)
         (DVars:DiskVars SemVars)
         (DSem: DiskSemantics SemVars Sem DVars)
         (RAVars:RecArrayVars SemVars).

    Import HlistNotations.

    Import Sem DSem.
    Module RATransitions := RecArrayTransitions SemVars DVars RAVars.
    Import RATransitions.

    Axiom recarray_relation_holds : forall tid,
        rimpl (R tid) (recarrayR tid).

    Axiom recarray_relation_preserved : forall tid s s',
        modified [( Items )] s s' ->
        recarrayR tid s s' ->
        R tid s s'.

    Axiom recarray_invariant_holds : forall m s d,
        Inv m s d ->
        recarrayI m s d.

    Axiom recarray_invariant_preserved : forall m s d m' s' d',
        Inv m s d ->
        (* m = m' *)
        modified [( )] m m' ->
        modified [( Items )] s s' ->
        recarrayI m' s' d' ->
        diskI m' s' d' ->
        Inv m' s' d'.

  End RecArraySemantics.

  Module RecArray
         (SemVars:SemanticsVars)
         (Sem:Semantics SemVars)
         (DVars:DiskVars SemVars)
         (DSem: DiskSemantics SemVars Sem DVars)
         (RAVars:RecArrayVars SemVars)
         (RASem: RecArraySemantics SemVars Sem DVars DSem RAVars).
    Import Sem.
    Module LockedDiskM := LockedDisk SemVars Sem DVars DSem.
    Import LockedDiskM.
    Import DSem.Transitions.
    Import RASem.
    Import RATransitions.

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

    Definition locked_get_item {T} i rx : prog Mcontents Scontents T :=
      let idx := $ (block_idx i) in
      let off := off_idx i in
           v <- locked_read idx;
               let b := valu_block v in
               rx (get_block_offset b off).

    Hint Resolve items_per_valu_not_0.

    Lemma ra_end_goodSize : goodSize addrlen (RAStart + RALen).
    Proof.
      apply ra_params_bounded.
    Qed.

    Lemma wlt_lt'' : forall sz a b,
        goodSize sz b ->
        a < b ->
        ((@natToWord sz a) < ($ b))%word.
    Proof.
      intros.
      apply lt_wlt.
      eapply le_lt_trans.
      apply wordToNat_natToWord_le.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Lemma wle_le'' : forall sz a b,
        goodSize sz b ->
        a <= b ->
        ((@natToWord sz a) <= ($ b))%word.
    Proof.
      intros.
      apply le_wle.
      eapply le_trans.
      apply wordToNat_natToWord_le.
      rewrite wordToNat_natToWord_idempotent'; auto.
    Qed.

    Require Import Omega.

    Hint Resolve ra_end_goodSize.

    Hint Extern 5 (_ <= _) => omega.

    Lemma block_idx_valid : forall i,
        i < RALen * items_per_valu ->
        let bidx := @natToWord addrlen (block_idx i) in
        ($ RAStart <= bidx /\
         bidx < $ (RAStart + RALen))%word.
    Proof.
      unfold block_idx; cbn; intros.
      assert (i / items_per_valu < RALen).
      apply Nat.div_lt_upper_bound; auto.
      rewrite mult_comm; auto.
      split.
      - apply wle_le''; auto.
        eapply goodSize_trans with (n2 := RAStart + RALen); auto.
      - apply wlt_lt''; auto.
    Qed.

    Polymorphic Theorem locked_get_item_ok : forall i,
        stateS TID: tid |-
        {{ (_:unit),
         | PRE d m s0 s:
             Inv m s d /\
             Locks.get (get GLocks s) ($ (block_idx i)) = Owned tid /\
             i < RALen * items_per_valu /\
             R tid s0 s
         | POST d' m' s0' s' r:
               Inv m' s' d' /\
               locks_increasing tid s s' /\
               r = selN (get Items s') i item0 /\
               R tid s0' s'
        }} locked_get_item i.
    Proof.
      intros.
      step pre simplify with try solve [ finish ].
      intuition.
      unfold recarrayI, rep_items', rep_blocks' in *; intuition.
      specialize (H11 ($ (block_idx i))).
      let H := fresh in
      pose proof (@block_idx_valid i) as H; cbn in H.
      intuition idtac.
      (* need a way for all specs to say we're not reading our locked
      block, but we can't actually put that in the invariant

       interesting point: concretely, what breaks down if the
       invariant says nobody is reading anything? the LockedDisk read
       spec certainly won't be provable, but what axiom isn't true? *)
    Abort.

  End RecArray.

End RecArray.