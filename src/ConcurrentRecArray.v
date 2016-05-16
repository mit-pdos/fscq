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
Require Import Omega.
Import ConcurrentDisk.

Import EqNotations.

Require Locks.
Require Import OrderedTypeEx.
Module Locks := Locks.Make(Nat_as_OT).
Import Locks.

Module Type RecArrayParams.

Parameter RAStart : nat.
Parameter RALen: nat.
Parameter itemtype : Rec.type.
Parameter items_per_valu : nat.
Axiom items_per_valu_ok : Rec.len itemtype * items_per_valu = valulen.
Axiom ra_params_bounded : RAStart + RALen < pow2 addrlen.
Axiom ra_non_trivial: 0 < RALen.

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

  Corollary items_per_valu_gt_0 : 0 < items_per_valu.
  Proof.
    pose proof items_per_valu_not_0.
    omega.
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

  Theorem rep_blocks_split : forall vs i,
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

    Require Import Rounding.

    Import Nat.
    Import Peano.
    (* restore S for successor *)
    Import Datatypes.

    Lemma mul_pos_incr : forall n k,
        0 < n ->
        n * k <= n ->
        k = 0 \/ k = 1.
    Proof.
      intros.
      destruct k; try omega.
      destruct k; try omega.
      rewrite mult_comm in *; cbn in *.
      pose proof (le_0_n (k * n)).
      omega.
    Qed.

    Lemma div_by_larger : forall n m,
        n <= m ->
        n / m = 0 \/ n = m.
    Proof.
      intros.
      destruct (le_lt_eq_dec _ _ H); auto using div_small.
    Qed.

    Lemma divup_lt_divisor : forall n m,
        0 < n ->
        0 < m ->
        n <= m ->
        divup n m = 1.
    Proof.
      intros.
      rewrite divup_eq_divup'.
      unfold divup'.
      case_eq (n mod m); intros.
      apply mod_divides in H2; try omega; deex.
      apply mul_pos_incr in H1; intuition subst; try omega.
      rewrite mult_1_r.
      rewrite div_same by omega; auto.
      destruct (div_by_larger H1); try omega.
      subst.
      rewrite mod_same in *; omega.
    Qed.

    Theorem divup_plus_divisor : forall n k,
        0 < k ->
        divup (k + n) k = 1 + divup n k.
    Proof.
      intros.
      rewrite ?divup_eq_divup'; unfold divup'.
      assert ((k + n) mod k = n mod k).
      rewrite plus_comm.
      replace k with (1 * k) at 1 by omega.
      rewrite mod_add by omega; auto.
      rewrite H0.
      replace (k + n) with (n + 1 * k) by omega.
      rewrite div_add by omega.
      destruct (n mod k); omega.
    Qed.

    Theorem length_nest_list_f_general : forall k0 A (l: list A) k accum,
        0 < k0 ->
        k < k0 ->
        length accum + k = k0 ->
        length (nest_list_f l k0 k accum) = divup (length (accum ++ l)) k0.
    Proof.
      induction l; cbn; intros.
      - rewrite app_nil_r in *.
        rewrite divup_lt_divisor; auto; try omega.
      - destruct k;
        rewrite ?app_length, ?plus_0_r in *; cbn in *.

        erewrite IHl; cbn; eauto; try omega.
        replace (length accum).
        rewrite divup_plus_divisor by omega.
        omega.

        rewrite IHl; auto; rewrite ?app_length;
        cbn; try omega.
        f_equal; omega.
    Qed.

    Corollary length_nest_list_f_exact : forall k0 A (l: list A) k accum m,
        0 < k0 ->
        k < k0 ->
        length accum + k = k0 ->
        (* this guarantees length will be exactly length (accum ++ l) / k0 = m *)
        length (accum ++ l) = m * k0 ->
        length (nest_list_f l k0 k accum) = m.
    Proof.
      intros.
      rewrite length_nest_list_f_general by auto.
      rewrite H2.
      rewrite divup_mul by omega; auto.
    Qed.

    Theorem length_nest_list : forall A (l: list A) k,
        0 < length l ->
        0 < k ->
        length (nest_list l k) = divup (length l) k.
    Proof.
      unfold nest_list; intros.
      destruct l, k; cbn in *; try omega.
      erewrite length_nest_list_f_general; eauto; omega.
    Qed.

    Theorem length_nest_list_exact : forall A (l: list A) k m,
        0 < length l ->
        0 < k ->
        length l = m * k ->
        length (nest_list l k) = m.
    Proof.
      unfold nest_list; intros.
      destruct l, k; cbn in *; try omega.
      erewrite length_nest_list_f_exact; eauto; omega.
    Qed.

  End Nesting.


  (* array_item *)
  Definition rep_items (vs : list item) :=
    rep_blocks (nest_list vs items_per_valu).

  Definition rep_blocks' vs_nested (vd: Disk) :=
    forall off, off < RALen ->
           vd ($ (RAStart + off)) = Some (block_valu (selN vs_nested off block0)).

  Definition rep_items' (vs: list item) vd :=
    rep_blocks' (nest_list vs items_per_valu) vd /\
    length vs = RALen * items_per_valu /\
    Forall Rec.well_formed vs.

  Theorem items_length_gt_0 : 0 < RALen * items_per_valu.
  Proof.
    pose proof ra_non_trivial.
    pose proof items_per_valu_gt_0.
    apply Nat.mul_pos_pos; auto.
  Qed.

  Hint Resolve items_length_gt_0.

  Lemma in_concat : forall A (l: list (list A)) sublist a,
      In a sublist ->
      In sublist l ->
      In a (concat l).
  Proof.
    induction l; cbn; auto; intros.
    intuition subst.
    apply in_or_app; eauto.
    apply in_or_app; eauto.
  Qed.

  Theorem in_nest_list : forall A (l: list A) sublist k a,
      In a sublist ->
      In sublist (nest_list l k) ->
      In a l.
  Proof.
    intros.
    rewrite <- nest_list_concat with (k := k).
    eapply in_concat; eauto.
  Qed.

  Theorem nested_blocks_well_formed : forall vs vd,
      rep_items' vs vd ->
      Forall (@Rec.well_formed blocktype) (nest_list vs items_per_valu).
  Proof.
    unfold rep_items'; intuition; cbn.
    rewrite Forall_forall in *; intros.
    pose proof (nest_list_length vs).
    specialize (H3 items_per_valu RALen).
    assert (0 < length vs).
    rewrite H; auto.
    pose proof items_per_valu_gt_0.
    intuition.
    rewrite Forall_forall in H6.
    eauto.

    rewrite Forall_forall; intros.
    apply H2.
    eapply in_nest_list; eauto.
  Qed.

  Module Type RecArrayVars (SemVars:SemanticsVars).
    Import SemVars.
    Parameter memVars : variables Mcontents [Locks.M].
    Parameter stateVars : variables Scontents [list item; list item; Locks.S].

    Axiom stateVars_no_confusion : NoDup (hmap var_index stateVars).
  End RecArrayVars.

  Module RecArrayTransitions (SemVars:SemanticsVars)
         (DVars:DiskVars SemVars)
         (RAVars: RecArrayVars SemVars).

    Module DiskTransitions := DiskTransitionSystem SemVars DVars.
    Import DiskTransitions.

    Import SemVars RAVars.

    Definition MLocks := ltac:(hget 0 memVars).
    Definition Items0 := ltac:(hget 0 stateVars).
    Definition Items := ltac:(hget 1 stateVars).
    Definition GLocks := ltac:(hget 2 stateVars).

    Definition lists_lin_mem (V:Type) (l_lin l_latest: list V) : @linear_mem nat _ (const V) :=
      fun n => match nth_error l_lin n, nth_error l_latest n with
             | Some v, Some v' => Some (v, v')
             | _, _ => None
             end.

    Definition item_mem (s:S Scontents) :=
      lists_lin_mem (get Items0 s) (get Items s).

    Definition recarrayR (tid:ID) : Relation Scontents :=
      fun s s' => linear_rel tid (Locks.get (get GLocks s))
                           (Locks.get (get GLocks s'))
                           (item_mem s) (item_mem s').

    Definition recarrayI : Invariant Mcontents Scontents :=
      fun m s d =>
        let mlocks := get MLocks m in
        let glocks := get GLocks s in
        (forall i, ghost_lock_invariant (Locks.mem mlocks i) (Locks.get glocks i)) /\
        linearized_consistent (item_mem s) (Locks.get glocks) /\
        rep_items' (get Items0 s) (get GDisk0 s).

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
        modified [( Items; GLocks )] s s' ->
        recarrayR tid s s' ->
        R tid s s'.

    Axiom recarray_invariant_holds : forall m s d,
        Inv m s d ->
        recarrayI m s d.

    Axiom recarray_invariant_preserved : forall m s d m' s' d',
        Inv m s d ->
        (* m = m' *)
        modified [( MLocks )] m m' ->
        modified [( Items; GLocks )] s s' ->
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

    Definition lock {T} i rx : prog Mcontents Scontents T :=
      tid <- GetTID;
      wait_for MLocks (Locks.is_open i) ($ i);;
               l <- Get MLocks;
      let l' := Locks.set_locked l i in
      Assgn MLocks l';;
            GhostUpdate (fun s =>
                           let l := get GLocks s in
                           let l' := Locks.add_lock l i tid in
                           set GLocks l' s);;
            rx tt.

    Definition block_off i := i / items_per_valu.

    Definition block_idx i := RAStart + block_off i.

    Definition off_idx i :=
      i mod items_per_valu.

    Definition get_block_offset (b: block) (off: nat) : item :=
      selN b off item0.

    Definition locked_get_item {T} i rx : prog Mcontents Scontents T :=
      let idx := $ (block_idx i) in
      let off := off_idx i in
           v <- read idx;
               let b := valu_block v in
               rx (get_block_offset b off).

    Hint Resolve items_per_valu_not_0 items_per_valu_gt_0.

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

    Hint Resolve ra_end_goodSize.

    Hint Extern 5 (_ <= _) => omega.

    Lemma valid_block_offset : forall i,
        i < RALen * items_per_valu ->
        i / items_per_valu < RALen.
    Proof.
      intros.
      apply Nat.div_lt_upper_bound; auto.
      rewrite mult_comm; auto.
    Qed.

    Lemma block_idx_valid : forall i,
        i < RALen * items_per_valu ->
        let bidx := @natToWord addrlen (block_idx i) in
        ($ RAStart <= bidx /\
         bidx < $ (RAStart + RALen))%word.
    Proof.
      unfold block_idx, block_off; cbn; intros.
      apply valid_block_offset in H.
      split.
      - apply wle_le''; auto.
        eapply goodSize_trans with (RAStart + RALen); auto.
      - apply wlt_lt''; auto.
    Qed.

    Lemma block_idx_goodSize : forall i,
        i < RALen * items_per_valu ->
        # (@natToWord addrlen (block_idx i)) = block_idx i.
    Proof.
      unfold block_idx, block_off; intros.
      apply valid_block_offset in H.
      rewrite wordToNat_natToWord_idempotent'; auto.
      eapply goodSize_trans with (RAStart + RALen); auto.
    Qed.

    Theorem subslice_hom_selN : forall A (l: list (list A)) k i def,
        i < length l ->
        Forall (fun l => length l = k) l ->
        skipn (i * k) (firstn (i * k + k) (concat l)) =
        selN l i def.
    Proof.
      intros.
      generalize dependent i.
      induction l; cbn; intros.
      inversion H.

      inversion H0; subst; intuition.
      destruct i; cbn.
      replace (length a) with (length a + 0) by omega.
      rewrite firstn_app_r; cbn.
      rewrite app_nil_r; auto.
      rewrite <- plus_assoc.
      rewrite firstn_app_r; cbn.
      rewrite skipn_app_r; cbn.
      eauto.
    Qed.

    Theorem selN_nested : forall A (l: list A) k m i def,
        0 < k ->
        i < m ->
        length l = m * k ->
        selN (nest_list l k) i def =
        skipn (i*k) (firstn (i*k+k) l).
    Proof.
      intros.
      assert (0 < length l).
      destruct m; cbn in *; try omega.
      pose proof (le_0_n (m * k)).
      omega.
      rewrite <- nest_list_concat with (k := k) (l := l) at 2.
      erewrite subslice_hom_selN; eauto.
      erewrite length_nest_list_exact; eauto; try omega.
      eapply nest_list_length; eauto.
    Qed.

    Theorem selN_subslice : forall A (l: list A) n m i def,
        n + i < m ->
        selN (skipn n (firstn m l)) i def =
        selN l (n+i) def.
    Proof.
      intros.
      rewrite skipn_selN.
      rewrite selN_firstn; auto.
    Qed.

    Lemma off_idx_bound : forall i,
        off_idx i < items_per_valu.
    Proof.
      intros.
      apply Nat.mod_upper_bound; auto.
    Qed.

    Hint Resolve off_idx_bound.

    Lemma block_off_bound : forall i,
        i < RALen * items_per_valu ->
        block_off i < RALen.
    Proof.
      unfold block_off; intros.
      eapply Nat.div_lt_upper_bound; auto.
      rewrite mult_comm; auto.
    Qed.

    Hint Resolve block_off_bound.

    (* combining the block offset and block index reconstructs the
      item index *)
    Lemma item_block_index : forall i,
        block_off i * items_per_valu + off_idx i = i.
    Proof.
      unfold block_off, off_idx; intros.
      rewrite mult_comm.
      rewrite <- Nat.div_mod; auto.
    Qed.

    Theorem locked_get_item_ok : forall i,
        stateS TID: tid |-
        {{ (_:unit),
         | PRE d m s0 s:
             Inv m s d /\
             Locks.get (get GLocks s) i = Owned tid /\
             i < RALen * items_per_valu /\
             R tid s0 s
         | POST d' m' s0' s' r:
             Inv m' s' d' /\
             star (othersR R tid) s s' /\
             r = selN (get Items s') i item0 /\
             R tid s0' s'
        }} locked_get_item i.
    Proof.
      intros.
      step pre simplify with try solve [ finish ].
      intuition.
      unfold recarrayI, rep_items', rep_blocks' in *; intuition.
      specialize (H9 (block_off i)).
      let H := fresh in
      pose proof (@block_idx_valid i) as H; cbn in H.
      intuition.

      step pre simplify with try solve [ finish ].
      unfold get_block_offset.
      unfold recarrayI, rep_items', rep_blocks' in *; intuition auto.
      specialize (H20 (block_off i)).
      pose proof (off_idx_bound i).
      fold (block_idx i) in *.
      replace DiskTransitions.GDisk0 with GDisk0 in * by reflexivity.
      erewrite H20 in * by auto.
      inv_opt.
      rewrite block_valu_id.
      erewrite selN_nested; try omega; eauto.
      rewrite selN_subslice; try omega; eauto.
      rewrite item_block_index.
      (* TODO: item i was locked from s to s2 *)
      admit.

      eapply Forall_forall.
      eapply nested_blocks_well_formed.
      admit.
      (* carry forward the locked item from s to s2 *)
      match goal with
        | [ |- In ?item _ ] =>
          replace item with (selN (nest_list (get Items s2) items_per_valu) (block_off i) block0)
      end.
      eapply in_selN.
      unfold rep_items', rep_blocks' in *; intuition auto.
      (* length_nest_list_exact assumptions should be dispatched easily *)
      erewrite length_nest_list_exact; eauto.
      admit.
      admit.
      admit. (* same locked goal *)
    Admitted.

  End RecArray.

End RecArray.