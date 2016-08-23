Require Import Arith.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Lia.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Rounding.

Import ListNotations.

Set Implicit Arguments.


Module Type BlockPtrSig.

  Parameter irec     : Type.               (* inode record type *)
  Parameter iattr    : Type.               (* part of irec that BlockPtr does not touch *)
  Parameter NDirect  : addr.               (* number of direct blocks *)

  (* Number of direct blocks should be quite small to avoid word overflow 
     Using addrlen as its bound is arbitrary *)
  Parameter NDirect_bound : NDirect <= addrlen.

  Parameter IRLen    : irec -> addr.       (* get length *)
  Parameter IRIndPtr : irec -> addr.       (* get indirect block pointer *)
  Parameter IRBlocks : irec -> list waddr. (* get direct block numbers *)
  Parameter IRAttrs  : irec -> iattr.      (* get untouched attributes *)

  (* setters *)
  Parameter upd_len  : irec -> addr -> irec.
  Parameter upd_irec : forall (r : irec) (len : addr) (ibptr : addr) (dbns : list waddr), irec.

  (* getter/setter lemmas *)
  Parameter upd_len_get_len    : forall ir n, goodSize addrlen n -> IRLen (upd_len ir n) = n.
  Parameter upd_len_get_ind    : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
  Parameter upd_len_get_blk    : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
  Parameter upd_len_get_iattr  : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.

  Parameter upd_irec_get_len   : forall ir len ibptr dbns,
     goodSize addrlen len -> IRLen (upd_irec ir len ibptr dbns) = len.
  Parameter upd_irec_get_ind   : forall ir len ibptr dbns,
     goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dbns) = ibptr.
  Parameter upd_irec_get_blk   : forall ir len ibptr dbns,
     IRBlocks (upd_irec ir len ibptr dbns) = dbns.
  Parameter upd_irec_get_iattr : forall ir len ibptr dbns,
      IRAttrs (upd_irec ir len ibptr dbns) = IRAttrs ir.

End BlockPtrSig.


(* block pointer abstraction for individule inode *)
Module BlockPtr (BPtr : BlockPtrSig).

  Import BPtr.


  (* RecArray for indirect blocks *)

  Definition indrectype := Rec.WordF addrlen.

  Module IndSig <: RASig.

    Definition xparams := addr.
    Definition RAStart := fun (x : xparams) => x.
    Definition RALen := fun (_ : xparams) => 1.
    Definition xparams_ok (_ : xparams) := True.

    Definition itemtype := indrectype.
    Definition items_per_val := valulen / (Rec.len itemtype).

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val.
      rewrite valulen_is; compute; auto.
    Qed.

  End IndSig.

  Module IndRec  := LogRecArray IndSig.
  Hint Extern 0 (okToUnify (IndRec.rep _ _) (IndRec.rep _ _)) => constructor : okToUnify.

  Notation "'NIndirect'" := IndSig.items_per_val.
  Notation "'NBlocks'"   := (NDirect + NIndirect)%nat.

  (* Various bounds *)
  Lemma NIndirect_is : NIndirect = 512.
  Proof.
    unfold IndSig.items_per_val.
    rewrite valulen_is; compute; auto.
  Qed.

  Lemma NBlocks_roundtrip : # (natToWord addrlen NBlocks) = NBlocks.
  Proof.
    unfold IndSig.items_per_val.
    erewrite wordToNat_natToWord_bound with (bound:=$ valulen).
    reflexivity.
    eapply le_trans.
    eapply plus_le_compat_r.
    apply NDirect_bound.
    apply Nat.sub_0_le.
    rewrite valulen_is.
    compute; reflexivity.
  Qed.

  Lemma NDirect_roundtrip : # (natToWord addrlen NDirect) = NDirect.
  Proof.
    intros.
    eapply wordToNat_natToWord_bound with (bound := natToWord addrlen NBlocks).
    rewrite NBlocks_roundtrip; omega.
  Qed.

  Lemma NIndirect_roundtrip : # (natToWord addrlen NIndirect) = NIndirect.
  Proof.
    intros.
    eapply wordToNat_natToWord_bound with (bound := natToWord addrlen NBlocks).
    rewrite NBlocks_roundtrip; omega.
  Qed.

  Lemma le_ndirect_goodSize : forall n,
    n <= NDirect -> goodSize addrlen n.
  Proof.
    intros; eapply goodSize_word_bound; eauto.
    rewrite NDirect_roundtrip; auto.
  Qed.

  Lemma le_nindirect_goodSize : forall n,
    n <= NIndirect -> goodSize addrlen n.
  Proof.
    intros; eapply goodSize_word_bound; eauto.
    rewrite NIndirect_roundtrip; auto.
  Qed.

  Lemma le_nblocks_goodSize : forall n,
    n <= NBlocks -> goodSize addrlen n.
  Proof.
    intros; eapply goodSize_word_bound; eauto.
    rewrite NBlocks_roundtrip; auto.
  Qed.

  Local Hint Resolve le_ndirect_goodSize le_nindirect_goodSize le_nblocks_goodSize.

  (************** rep invariant *)

   Definition indrep_n_helper bxp ibn iblocks :=
    (if (addr_eq_dec ibn 0)
      then [[ iblocks = repeat $0 NIndirect ]]
      else [[ BALLOC.bn_valid bxp ibn ]] * IndRec.rep ibn iblocks
    )%pred.

  (* indlvl = 0 if ibn is the address of an indirect block,
     indlvl = 1 for doubly indirect, etc. *)

  Fixpoint indrep_n_tree indlvl bxp ibn l :=
    (match indlvl with
    | 0 => indrep_n_helper bxp ibn l
    | S indlvl' => let divisor := NIndirect ^ indlvl in
                    exists iblocks l_part, [[ l = concat l_part ]] *
                    indrep_n_helper bxp ibn iblocks *
                    listmatch (fun ibn' l' => indrep_n_tree indlvl' bxp (# ibn') l') iblocks l_part
    end)%pred.

  Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (indrep_n_tree _ _ _ _ _) (indrep_n_tree _ _ _ _ _)) => constructor : okToUnify.

  Definition indrep bxp ir (indlist : list waddr) nblocks :=
    ( [[ nblocks = 0 ]] \/ (
      [[ nblocks > 0 ]] * indrep_n_tree 0 bxp (IRIndPtr ir) indlist))%pred.

  Definition rep bxp (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp ir indlist (length l - NDirect) *
      [[ l = firstn (length l) ((IRBlocks ir) ++ indlist) ]] )%pred.

  Definition rep_direct (ir : irec) (l : list waddr) : @pred _ addr_eq_dec valuset :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l <= NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      [[ l = firstn (length l) (IRBlocks ir) ]] )%pred.

  Definition rep_indirect bxp (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l > NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep_n_tree 0 bxp (IRIndPtr ir) indlist *
      [[ l = (IRBlocks ir) ++ firstn (length l - NDirect) indlist ]] )%pred.

  (* Necessary to make subst work when there's a recursive term like:
     l = firstn (length l) ... *)
  Set Regular Subst Tactic.

  Lemma indrep_n_helper_0 : forall bxp l,
    indrep_n_helper bxp 0 l <=p=> [[ l = repeat $0 NIndirect ]] * emp.
  Proof.
    unfold indrep_n_helper; intros; split; cancel.
  Qed.

  Lemma rep_piff_direct : forall bxp ir l,
    length l <= NDirect ->
    rep bxp ir l <=p=> rep_direct ir l.
  Proof.
    unfold rep, indrep, rep_direct; intros; split; cancel; try omega.
    rewrite firstn_app_l in H5 by omega; auto.
    substl l at 1; rewrite firstn_app_l by omega; auto.
    Unshelve.
    eauto.
  Qed.

  Lemma rep_piff_indirect : forall bxp ir l,
    length l > NDirect ->
    rep bxp ir l <=p=> rep_indirect bxp ir l.
  Proof.
    unfold rep, indrep, rep_indirect; intros; split; cancel; try omega.
    rewrite <- firstn_app_r; setoid_rewrite H3.
    replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    substl l at 1; rewrite <- firstn_app_r. setoid_rewrite H3.
    replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    Unshelve. exact nil.
  Qed.

  Lemma rep_selN_direct_ok : forall F bxp ir l m off,
    (F * rep bxp ir l)%pred m ->
    off < NDirect ->
    off < length l ->
    selN (IRBlocks ir) off $0 = selN l off $0.
  Proof.
    unfold rep, indrep; intros; destruct_lift H.
    substl.
    rewrite selN_firstn by auto.
    rewrite selN_app1 by omega; auto.
  Qed.

  Local Hint Resolve IndRec.Defs.items_per_val_not_0.
  Local Hint Resolve IndRec.Defs.items_per_val_gt_0'.

  Lemma off_mod_len_l : forall T off (l : list T), length l = NIndirect -> off mod NIndirect < length l.
  Proof.
    intros. rewrite H; apply Nat.mod_upper_bound; auto.
  Qed.

  Lemma mult_neq_0 : forall m n, m <> 0 -> n <> 0 -> m * n <> 0.
  Proof.
    intros. intuition.
    apply mult_is_O in H1.
    destruct H1; auto.
  Qed.

  Fact divmod_n_zeros : forall n, fst (Nat.divmod n 0 0 0) = n.
  Proof.
    intros.
    pose proof Nat.div_1_r n.
    unfold Nat.div in H. auto.
  Qed.

  Fact div_mul_le : forall a b : addr, a / b * b <= a.
  Proof.
    intros.
    destruct (Nat.eq_dec b 0) as [H|H]; subst; try omega.
    pose proof Nat.div_mod a b H.
    rewrite mult_comm; omega.
  Qed.

  Hint Rewrite divmod_n_zeros using auto.
  Local Hint Resolve Nat.pow_nonzero.
  Local Hint Resolve off_mod_len_l.
  Local Hint Resolve mult_neq_0.

  Lemma sub_round_eq_mod : forall a b, b <> 0 -> a - a / b * b = a mod b.
  Proof.
    intros.
    rewrite Nat.mod_eq, mult_comm; auto.
  Qed.

  Lemma sub_mod_eq_round : forall a b, b <> 0 -> a - (a mod b) = a / b * b.
  Proof.
    intros.
    rewrite <- sub_round_eq_mod at 1 by auto.
    rewrite sub_sub_assoc; auto.
    apply div_mul_le.
  Qed.

  Lemma mul_ge_l : forall m n,
    0 < m -> n <= n * m.
  Proof.
    intros.
    rewrite mult_comm.
    destruct (mult_O_le n m); solve [ omega | auto].
  Qed.

  Lemma mul_ge_r : forall m n,
    0 < m -> n <= m * n.
  Proof.
    intros. rewrite mult_comm. apply mul_ge_l; auto.
  Qed.

  Local Hint Resolve mul_ge_l mul_ge_r.

  Lemma divup_bound_helper : forall m n a k k', m < divup n a -> n <= k * a -> k' = k -> m < k'.
  Proof.
    intros; subst.
    eapply lt_le_trans; eauto.
    apply divup_le; rewrite mult_comm; auto.
  Qed.

  Fact sub_sub_comm : forall a b c, a - b - c = a - c - b.
  Proof.
    intros.
    rewrite <- Nat.sub_add_distr. rewrite plus_comm.
    rewrite Nat.sub_add_distr. auto.
  Qed.

  Fact sub_S_1 : forall n, n > 0 -> S (n - 1) = n.
  Proof.
    intros. omega.
  Qed.

  Fact sub_le_eq_0 : forall a b, a <= b -> a - b = 0.
  Proof.
    intros. omega.
  Qed.

  Fact mod_le_r : forall a b, a mod b <= b.
  Proof.
    intros. case_eq b; intros. auto.
    apply Nat.lt_le_incl, Nat.mod_upper_bound. omega.
  Qed.

  Hint Resolve mod_le_r.

  Fact divup_eq_div : forall a b, a mod b = 0 -> divup a b = a / b.
  Proof.
    intros.
    rewrite divup_eq_divup'. unfold divup'.
    destruct (a mod b); omega.
  Qed.

  Fact divup_eq_div_plus_1 : forall a b, a mod b <> 0 -> divup a b = 1 + a / b.
  Proof.
    intros.
    rewrite divup_eq_divup'. unfold divup'. destruct (_ mod _); intuition.
  Qed.

  Theorem divup_sub_1_eq : forall a b, a mod b <> 0 -> divup a b - 1 = a / b.
  Proof.
    intros.
    rewrite divup_eq_div_plus_1 by auto.
    apply minus_plus.
  Qed.

  Lemma div_sub_small : forall a b n, n <> 0 -> b <= a mod n -> (a - b) / n = a / n.
  Proof.
    intros.
    rewrite Nat.div_mod with (x := a) (y := n) by auto.
    rewrite mult_comm.
    rewrite <- Nat.add_sub_assoc by auto.
    repeat rewrite Nat.div_add_l by auto.
    pose proof Nat.mod_upper_bound a n H.
    rewrite Nat.div_small with (a := a mod n) by auto.
    rewrite Nat.div_small with (a := _ - _) by omega.
    auto.
  Qed.

  Lemma mod_sub : forall a b n, a >= b -> (a - b) mod n = (a - (b mod n)) mod n.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0); subst; auto.
    erewrite <- Nat.mod_add by auto.
    rewrite <- Nat.add_sub_swap by auto.
    rewrite <- Nat.add_sub_assoc by (apply divup_n_mul_n_le; auto).
    rewrite divup_eq_divup'. unfold divup'.
    destruct (b mod n) eqn:HH.
    rewrite mul_div, Nat.sub_diag by omega. rewrite plus_0_r, Nat.sub_0_r. auto.
    Search (_ + _ / _).
    rewrite Nat.div_mod with (x := b) (y := n) at 2 by auto.
    rewrite plus_comm with (n := (_ / _)).
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.sub_add_distr.
    rewrite mult_1_l, mult_comm.
    rewrite Nat.add_sub.
    rewrite Nat.add_sub_assoc.
    pose proof Nat.mod_add (a - b mod n) 1 n n0.
    rewrite plus_comm, mult_1_l in H0.
    rewrite plus_comm. rewrite <- Nat.add_sub_assoc. congruence.
    eapply le_trans. apply Nat.mod_le; auto. auto.
    apply mod_le_r.
  Qed.

  Lemma mod_congruent : forall a b n, a >= b -> a mod n = b mod n <-> (a - b) mod n = 0.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0); subst. intuition.
    split; intros HH.
    rewrite mod_sub by auto. rewrite <- HH. rewrite sub_mod_eq_round by auto.
    rewrite Nat.mod_mul; auto.
    rewrite Nat.mod_divides in HH; destruct HH as [n' HH]; auto.
    assert (b mod n <= b) by (apply Nat.mod_le; auto).
    eapply Nat.add_cancel_r in HH.
    rewrite Nat.sub_add in HH by auto.
    subst.
    rewrite plus_comm, mult_comm, Nat.mod_add by auto.
    auto.
  Qed.

  Lemma div_plus_bound : forall a b n x y, a < x * n -> b < y * n -> (a + b) / n < x + y.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0). subst; omega.
    destruct (Nat.eq_dec x 0). subst; omega.
    destruct (Nat.eq_dec y 0). subst; omega.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm, Nat.mul_add_distr_r. omega.
  Qed.

  Lemma div_sub_close : forall a b n, n <> 0 -> b <= a -> a - b < n -> a / n - b / n <= 1.
  Proof.
    intros.
    remember (a - b) as e. replace a with (b + e) by omega.
    rewrite Nat.div_mod with (x := b) (y := n) at 1 by auto.
    rewrite <- plus_assoc. rewrite mult_comm. rewrite Nat.div_add_l by auto.
    rewrite minus_plus.
    apply lt_n_Sm_le.
    apply div_plus_bound with (x := 1) (y := 1); rewrite mult_1_l.
    apply Nat.mod_bound_pos; omega. omega.
  Qed.

  Lemma div_eq_S_div_sub : forall a n, n <> 0 -> n <= a -> a / n = S (a / n - 1).
  Proof.
    intros.
    rewrite sub_S_1. auto.
    apply Nat.div_str_pos. omega.
  Qed.

  Lemma div_sub_mod_large : forall a b n, b <= a -> a mod n < b mod n -> (a - b) / n = a / n - b / n - 1.
  Proof.
    intros.
    destruct (addr_eq_dec n 0). subst. auto.
    assert (a mod n < n) by (apply Nat.mod_bound_pos; omega).
    assert (b mod n < n) by (apply Nat.mod_bound_pos; omega).
    destruct (le_lt_dec n a); [> |repeat rewrite Nat.div_small by omega; auto].
    destruct (le_lt_dec n (a - b)).
    + rewrite Nat.div_mod with (x := b) (y := n) at 1 by auto.
      rewrite Nat.div_mod with (x := a) (y := n) at 1 by auto.
      rewrite Nat.sub_add_distr.
      rewrite plus_comm.
      rewrite <- Nat.add_sub_assoc by (apply Nat.mul_le_mono_l, Nat.div_le_mono; auto).
      rewrite div_eq_S_div_sub with (a := a) at 1 by auto.
      rewrite <- mult_n_Sm.
      rewrite plus_comm with (m := n).
      rewrite <- Nat.add_sub_assoc with (n := n).
      rewrite <- Nat.mul_sub_distr_l.
      rewrite plus_comm. rewrite plus_comm with (n := n).
      rewrite mult_comm.
      rewrite <- Nat.add_assoc.
      rewrite <- Nat.add_sub_assoc by omega.
      rewrite Nat.div_add_l by auto.
      rewrite Nat.div_small with (a := _ + _ - _) by omega.
      rewrite plus_0_r. omega.
      apply Nat.mul_le_mono_l.
      replace a with (b + (a - b)) by omega.
      rewrite Nat.div_mod with (x := b) (y := n) at 2 by auto.
      rewrite <- plus_assoc. rewrite mult_comm. rewrite Nat.div_add_l by auto.
      rewrite <- Nat.add_sub_assoc by (apply Nat.div_str_pos_iff; omega). omega.
    + rewrite Nat.div_small by auto.
      symmetry. apply Nat.sub_0_le.
      apply div_sub_close; auto.
  Qed.

  Lemma div_sub_mod_small : forall a b n, b <= a -> b mod n <= a mod n ->
    (a - b) / n = a / n - b / n.
  Proof.
    intros.
    destruct (addr_eq_dec n 0). subst; auto.
    rewrite Nat.div_mod with (x := b) (y := n) at 1 by auto.
    rewrite Nat.div_mod with (x := a) (y := n) at 1 by auto.
    rewrite Nat.sub_add_distr.
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by (apply Nat.mul_le_mono_l, Nat.div_le_mono; auto).
    rewrite plus_comm.
    rewrite <- Nat.mul_sub_distr_l.
    rewrite <- Nat.add_sub_assoc by auto.
    rewrite mult_comm, Nat.div_add_l by auto.
    rewrite Nat.div_small with (a := _ - _). auto.
    assert (a mod n < n) by (apply Nat.mod_bound_pos; omega). omega.
  Qed.

  Lemma mod_reversed_ge : forall a b n, b mod n < a -> a <= b -> n <= b.
  Proof.
    intros.
    destruct (le_lt_dec n b); auto.
    rewrite Nat.mod_small in * by omega. omega.
  Qed.

  Lemma div_lt_div_mod_reverse : forall a b n, b <= a -> a mod n < b mod n -> b / n < a / n.
  Proof.
    intros.
    destruct (addr_eq_dec n 0). subst; simpl in *. auto.
    apply Nat.div_le_mono with (c := n) in H as H'; auto.
    destruct (le_lt_eq_dec _ _ H') as [HH|HH]. auto.
    rewrite Nat.div_mod with (x := b) (y := n) in H by auto.
    rewrite Nat.div_mod with (x := a) (y := n) in H by auto.
    rewrite HH in H.
    apply Nat.add_le_mono_l in H. omega.
  Qed.

  Fact div_sub_far : forall a b n, n <> 0 -> b <= a -> a - b >= n -> a / n - b / n >= 1.
  Proof.
    intros.
    remember (a - b) as e. replace a with (b + e) by omega.
    rewrite Nat.div_mod with (x := b) (y := n) at 1 by auto.
    rewrite <- plus_assoc. rewrite mult_comm. rewrite Nat.div_add_l by auto.
    rewrite minus_plus.
    apply Nat.div_str_pos_iff; auto. omega.
  Qed.

  Lemma indrep_div_helper_1 : forall a b n,
    n <> 0 ->
    b <= a ->
    a mod n < b mod n ->
    n <= a ->
    1 + (a - b) / n = a / n - (b - a mod n) / n.
  Proof.
    intros.
    assert ((a - b) mod n <> 0) by (rewrite <- mod_congruent; omega).
    rewrite div_sub_small with (a := b) by omega.
    rewrite div_sub_mod_large by omega.
    destruct (le_lt_dec (a / n) (b / n)); [> | omega].
    assert (b / n < a / n).
    apply div_lt_div_mod_reverse; auto. omega.
  Qed.

  Lemma indrep_div_helper_2 : forall a b n,
    n <> 0 ->
    b <= a ->
    b mod n < a mod n ->
    a mod n < b ->
    n <= a ->
    1 + (a - b) / n = a / n - (b - a mod n) / n.
  Proof.
    intros.
    assert ((a - b) mod n <> 0) by (rewrite <- mod_congruent; omega).
    rewrite div_sub_mod_large with (a := b) by (try rewrite Nat.mod_mod; omega).
    rewrite mod_div_0, Nat.sub_0_r.
    assert (n <= b) by (eapply mod_reversed_ge; eauto; omega).
    rewrite div_sub_mod_small by omega.
    rewrite plus_comm.
    assert (0 < b / n) by (apply Nat.div_str_pos_iff; omega).
    assert (0 < a / n) by (apply Nat.div_str_pos_iff; omega).
    assert (b / n <= a / n) by (apply Nat.div_le_mono; omega).
    omega.
  Qed.

  Lemma roundup_sub_eq : forall a b n,
    n <> 0 ->
    b <= a ->
    n <= a ->
    a mod n < b ->
    roundup (a - b) n = a / n * n - (b - (a mod n)) / n * n.
  Proof.
    intros.
    unfold roundup.
    rewrite <- Nat.mul_sub_distr_r. f_equal.
    destruct (lt_eq_lt_dec (a mod n) (b mod n)) as [ [H'|H']|H'].
    + assert (a mod n <> b mod n) as HH by omega.
      assert ((a - b) mod n <> 0) by (rewrite mod_congruent in HH; auto).
      rewrite divup_eq_div_plus_1 by auto.
      apply indrep_div_helper_1; auto.
    + rewrite H'. rewrite sub_mod_eq_round by auto. rewrite Nat.div_mul by auto.
      apply mod_congruent in H' as H''; auto.
      rewrite divup_eq_div by auto.
      rewrite Nat.div_mod with (x := b) (y := n) at 1 by auto.
      rewrite <- H'.
      rewrite plus_comm, Nat.sub_add_distr.
      rewrite sub_mod_eq_round by auto.
      rewrite mult_comm, <- Nat.mul_sub_distr_l.
      rewrite mult_comm, Nat.div_mul by auto. auto.
    + assert (a mod n <> b mod n) as HH by omega.
      assert ((a - b) mod n <> 0) by (rewrite mod_congruent in HH; auto).
      rewrite divup_eq_div_plus_1 by auto.
      apply indrep_div_helper_2; omega.
  Qed.

  Lemma roundup_eq : forall a n, n <> 0 -> a mod n <> 0 -> roundup a n = a + (n - a mod n).
  Proof.
    intros.
    unfold roundup.
    rewrite divup_eq_divup'. unfold divup'.
    destruct (a mod n) as [|n'] eqn:HH; intuition.
    substl (S n').
    rewrite Nat.div_mod with (x := a) (y := n) at 2 by auto.
    rewrite <- plus_assoc.
    rewrite <- le_plus_minus by (apply mod_le_r).
    rewrite Nat.mul_add_distr_r. rewrite mult_comm. omega.
  Qed.

  Lemma sub_eq_roundup_sub : forall a b n,
    b <= a ->
    n <> 0 ->
    a mod n < b ->
    roundup (a - b) n - (b - a mod n) mod n = a - b.
  Proof.
    intros.
    apply Nat.add_sub_eq_l.
    destruct (lt_eq_lt_dec (a mod n) (b mod n)) as [ [H'|H']|H'].
    + assert ((a - b) mod n <> 0) by (rewrite <- mod_congruent; auto).
      rewrite roundup_eq by auto.
      rewrite plus_comm. f_equal.
      rewrite Nat.div_mod with (x := b) (y := n) by auto.
      rewrite <- Nat.add_sub_assoc by omega.
      rewrite plus_comm, mult_comm.
      rewrite Nat.mod_add by auto.
      assert (b mod n < n) by (apply Nat.mod_bound_pos; omega).
      assert (a mod n < n) by (apply Nat.mod_bound_pos; omega).
      rewrite Nat.mod_small by omega.
      destruct (le_lt_dec n a); [> | repeat rewrite Nat.mod_small in * by omega; omega].
      rewrite Nat.div_mod with (x := a) (y := n) at 2 by auto.
      rewrite div_eq_S_div_sub by auto.
      rewrite <- mult_n_Sm.
      rewrite <- plus_assoc, plus_comm.
      rewrite Nat.sub_add_distr.
      rewrite mult_comm.
      rewrite <- Nat.add_sub_assoc.
      rewrite <- Nat.mul_sub_distr_r.
      rewrite plus_comm.
      rewrite <- Nat.add_sub_assoc, plus_comm by omega.
      rewrite Nat.mod_add by auto.
      rewrite Nat.mod_small with (a := _ - _) by omega. omega.
      apply mult_le_compat_r.
      assert (b / n < a / n) by (apply div_lt_div_mod_reverse; omega).
      omega.
    + rewrite H'. rewrite sub_mod_eq_round by auto. rewrite Nat.mod_mul by auto.
      unfold roundup. rewrite divup_eq_div by (apply mod_congruent; auto).
      rewrite mul_div by (try apply mod_congruent; omega). auto.
    + assert ((a - b) mod n <> 0) by (rewrite <- mod_congruent; auto).
      rewrite roundup_eq by auto.
      rewrite plus_comm. f_equal.
      rewrite Nat.div_mod with (x := a) (y := n) at 2 by auto.
      rewrite Nat.div_mod with (x := b) (y := n) at 2 by auto.
      rewrite Nat.sub_add_distr.
      rewrite plus_comm.
      rewrite <- Nat.add_sub_assoc.
      rewrite <- Nat.mul_sub_distr_l.
      rewrite plus_comm, mult_comm.
      rewrite <- Nat.add_sub_assoc by omega.
      rewrite plus_comm.
      rewrite Nat.mod_add by auto.
      assert (b mod n < n) by (apply Nat.mod_bound_pos; omega).
      assert (a mod n < n) by (apply Nat.mod_bound_pos; omega).
      rewrite Nat.mod_small with (a := _ mod _ - _) by omega.
      destruct (le_lt_dec n b); [> | repeat rewrite Nat.mod_small in * by omega; omega].
      rewrite Nat.div_mod with (x := b) (y := n) at 1 by auto.
      rewrite div_eq_S_div_sub by auto.
      rewrite <- mult_n_Sm.
      rewrite <- plus_assoc.
      rewrite <- Nat.add_sub_assoc by omega.
      rewrite plus_comm, mult_comm.
      rewrite Nat.mod_add by auto.
      rewrite Nat.mod_small by omega.
      omega.
      apply mult_le_compat_l.
      apply Nat.div_le_mono; auto.
  Qed.

  Theorem in_removeN_enumerate : forall T a b n (l : list T),
    In (a, b) (removeN (enumerate l) n) -> a < n \/ n < a < length l.
  Proof.
    intros.
    unfold enumerate in H; rewrite removeN_combine in H.
    apply in_combine_l in H. unfold removeN in H.
    rewrite in_app_iff in *.
    rewrite firstn_seq, skipn_seq in H. simpl in H.
    repeat rewrite in_seq in H.
    edestruct Nat.min_dec as [H' | H']; rewrite H' in H.
    destruct H; intuition; omega.
    rewrite Nat.min_r_iff in H'.
    left; omega.
  Qed.

  Theorem in_enumerate : forall T a b (l : list T), In (a, b) (enumerate l) -> a < length l.
  Proof.
    unfold enumerate. intros.
    apply in_combine_l, in_seq in H. omega.
  Qed.

  Ltac in_enumerate := match goal with
    | [H : In _ (removeN (enumerate _) _) |- _ ] => apply in_removeN_enumerate in H
    | [H : In _ (enumerate _) |- _ ] => apply in_enumerate in H
    | [H : In ?a (removeN (enumerate _) _) |- _ ] => destruct a; in_enumerate
    | [H : In ?a (enumerate _) |- _ ] => destruct a; in_enumerate
  end.

  Ltac mult_nonzero := 
    repeat (match goal with
    | [ |- mult _ _ <> 0 ] => apply mult_neq_0
    | [ |- mult _ _ > 0 ] => apply lt_mul_mono
    | [ |- _ ^ _ <> 0 ] => apply Nat.pow_nonzero
    | [ |- _ > 0 ] => unfold gt
    | [ |- 0 < _ ] => apply neq_0_lt
    | [ |- 0 <> _ ] => apply not_eq_sym
    | [ |- _] => solve [auto]
    end).

  Ltac divide_mult := match goal with
    | [ |- Nat.divide 1 ?n ] => apply Nat.divide_1_l
    | [ |- Nat.divide ?n 0 ] => apply Nat.divide_0_r
    | [ |- Nat.divide ?a ?a ] => apply Nat.divide_refl
    | [ |- Nat.divide ?a (?b * ?c) ] => solve [apply Nat.divide_mul_l; divide_mult |
                                               apply Nat.divide_mul_r; divide_mult ]
    | [ |- Nat.divide ?n (roundup _ ?n) ] => unfold roundup; apply Nat.divide_mul_r
  end.

  Local Hint Extern 1 (Nat.divide ?a ?b) => divide_mult.

  Lemma indrep_n_helper_length : forall bxp ibn l m,
    indrep_n_helper bxp ibn l m -> length l = NIndirect.
  Proof.
    unfold indrep_n_helper, IndRec.rep, IndRec.items_valid.
    intros; destruct addr_eq_dec; destruct_lift H; unfold lift_empty in *;
    intuition; subst; autorewrite with lists; auto.
    unfold IndRec.Defs.item in *; simpl in *. omega.
  Qed.

  Lemma indrep_n_helper_length_piff : forall bxp ibn l,
    indrep_n_helper bxp ibn l <=p=> indrep_n_helper bxp ibn l * [[ length l = NIndirect ]].
  Proof.
    intros.
    split; [> intros m H; apply indrep_n_helper_length in H as HH; pred_apply | ]; cancel.
  Qed.

  Lemma indrep_n_length_pimpl : forall indlvl bxp ibn l,
    indrep_n_tree indlvl bxp ibn l <=p=>
    [[ length l = NIndirect ^ (S indlvl) ]] * indrep_n_tree indlvl bxp ibn l.
  Proof.
    induction indlvl; simpl; intros.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    erewrite indrep_n_helper_length; eauto; omega.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_lift_r in H; destruct_lift H.
    erewrite concat_hom_length; eauto.
    f_equal; omega.
    intros x y.
    split; [> rewrite IHindlvl |]; cancel.
  Qed.

  Lemma indrep_n_tree_length: forall indlvl F ir l1 l2 bxp m, (F *
    indrep_n_helper bxp ir l1 *
    listmatch
     (fun ibn' l' => indrep_n_tree indlvl bxp # (ibn') l') l1 l2)%pred m->
     length (concat l2) = NIndirect * (NIndirect ^ (S indlvl)).
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff in H.
    rewrite listmatch_length_pimpl in H.
    erewrite listmatch_lift_r in H.
    destruct_lift H.
    erewrite concat_hom_length; eauto.
    f_equal; omega.
    intros.
    rewrite indrep_n_length_pimpl. split; cancel.
  Qed.

  Lemma indrep_index_bound_helper : forall Fm off indlvl bxp bn iblocks l_part m,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks) *
          listmatch (fun ibn' (l' : list waddr) =>
            indrep_n_tree indlvl bxp # (ibn') l') iblocks l_part)%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < NIndirect.
  Proof.
    intros.
    apply Nat.div_lt_upper_bound; mult_nonzero.
    erewrite indrep_n_tree_length in * by eauto.
    rewrite mult_comm; simpl in *. auto.
  Qed.

  Lemma indrep_index_length_helper_l : forall Fm off indlvl bxp bn iblocks l_part m,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks) *
          listmatch (fun ibn' (l' : list waddr) =>
            indrep_n_tree indlvl bxp # (ibn') l') iblocks l_part)%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < length (iblocks).
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff in *. destruct_lifts.
    substl (length iblocks). eapply indrep_index_bound_helper; eauto.
  Qed.

  Lemma indrep_index_length_helper_l' : forall Fm Fm' off indlvl bxp bn iblocks l_part m,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks) *
          listmatch (fun ibn' l' => indrep_n_tree indlvl bxp # (ibn') l')
          iblocks l_part * Fm')%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < length (iblocks).
  Proof.
    intros. eapply indrep_index_length_helper_l; eauto.
    eapply pimpl_apply; [> | exact H0]; cancel.
    rewrite sep_star_comm, <- sep_star_assoc. apply pimpl_refl.
  Qed.

  Lemma indrep_index_length_helper_r : forall Fm off indlvl bxp bn iblocks l_part m,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks) *
          listmatch (fun ibn' (l' : list waddr) =>
            indrep_n_tree indlvl bxp # (ibn') l') iblocks l_part)%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < length l_part.
  Proof.
    intros.
    rewrite listmatch_length_pimpl in *.
    destruct_lifts.
    substl (length l_part).
    eapply indrep_index_length_helper_l; eauto.
  Qed.

  Lemma indrep_index_length_helper_r' : forall Fm Fm' off indlvl bxp bn iblocks l_part m,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks) *
          listmatch (fun ibn' (l' : list waddr) =>
            indrep_n_tree indlvl bxp # (ibn') l') iblocks l_part * Fm')%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < length l_part.
  Proof.
    intros. eapply indrep_index_length_helper_r; eauto.
    eapply pimpl_apply; [> | exact H0]; cancel.
    rewrite sep_star_comm, <- sep_star_assoc. apply pimpl_refl.
  Qed.

  Lemma indrep_n_indlist_forall_length : forall F indlvl bxp ir l1 l2 m,
    ((F ✶ indrep_n_helper bxp ir l1)
        ✶ listmatch
            (fun ibn' l' =>indrep_n_tree indlvl bxp # (ibn') l') l1 l2)%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff, listmatch_lift_r in H.
    destruct_lifts; eauto.
    intros x; intros.
    rewrite indrep_n_length_pimpl. split; cancel.
  Qed.

  Local Hint Resolve indrep_n_indlist_forall_length.

  Theorem indrep_n_tree_0 : forall indlvl bxp l,
    indrep_n_tree indlvl bxp 0 l <=p=> [[ l = repeat $0 (NIndirect ^ S indlvl)]].
  Proof.
    induction indlvl; simpl; intros.
    rewrite mult_1_r, indrep_n_helper_0; split; cancel.
    split.
    intros m' H'.
    destruct_lift H'.
    rewrite indrep_n_helper_0 in H.
    rewrite listmatch_length_pimpl in H; autorewrite with lists in *.
    rewrite listmatch_lift_r with (F := fun x y => emp) in H.
    rewrite listmatch_emp in H by cancel.
    pred_apply; cancel.
    erewrite concat_hom_repeat; eauto.
    repeat f_equal. rewrite repeat_length in *. omega.
    intros; simpl.
    destruct_lifts. erewrite repeat_spec with (y := x); eauto.
    rewrite IHindlvl. split; cancel.
    cancel.
    instantiate (iblocks := repeat $0 NIndirect).
    rewrite indrep_n_helper_0.
    rewrite listmatch_lift_r with (F := fun x y => emp) (P := fun y => length y = NIndirect ^ S indlvl).
    rewrite listmatch_emp_piff by auto.
    autorewrite with lists.
    cancel.
    apply Forall_repeat.
    rewrite repeat_length. eauto.
    rewrite repeat_length. eauto.
    intro x; intros.
    erewrite repeat_spec with (y := x); eauto.
    rewrite IHindlvl. split; cancel. subst. autorewrite with lists. auto.
    erewrite repeat_spec with(y := y); eauto.
    erewrite concat_hom_repeat; autorewrite with lists.
    rewrite plus_0_r. eauto.
    apply Forall_repeat. auto.
  Qed.

  (************* n-indirect program *)

  Fixpoint indget (indlvl : nat) lxp (bn : addr) off ms :=
    If (addr_eq_dec bn 0) {
      Ret ^(ms, $ 0)
    } else {
      let divisor := NIndirect ^ indlvl in
      let^ (ms, v) <- IndRec.get lxp bn (off / divisor) ms;
      match indlvl with
      | 0 => Ret ^(ms, v)
      | S indlvl' => indget indlvl' lxp (# v) (off mod divisor) ms
      end
    }.

  Lemma divup_gt_0 : forall a b, 0 < a -> 0 < b -> divup a b > 0.
  Proof.
    intros.
    apply Nat.div_str_pos; omega.
  Qed.

  Local Hint Resolve divup_gt_0.

  Ltac indrep_n_tree_bound := solve [
        eapply indrep_index_length_helper_l; eauto  |
        eapply indrep_index_length_helper_l'; eauto |
        eapply indrep_index_length_helper_r; eauto  |
        eapply indrep_index_length_helper_r'; eauto |
        eapply indrep_index_bound_helper; eauto].

  Ltac indrep_n_extract := match goal with
    | [|- context [listmatch _ ?l] ] =>
      match goal with [l : list _ |- context [listmatch _ (removeN ?l ?n)] ] =>
        rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try omega; try erewrite snd_pair by eauto
      end
    | [|- context [selN ?l ?n] ] => rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try omega; try erewrite snd_pair by eauto
  end.

  (* TODO move this *)
  Theorem indrep_n_helper_valid : forall bxp bn l,
    bn <> 0 -> indrep_n_helper bxp bn l <=p=> [[ BALLOC.bn_valid bxp bn ]] * IndRec.rep bn l.
  Proof.
    intros. unfold indrep_n_helper. destruct bn; try omega. simpl.
    split; cancel.
  Qed.

  Theorem indget_ok : forall indlvl lxp bxp bn off ms,
    {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp bn l ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} indget indlvl lxp bn off ms.
  Proof.
    induction indlvl; simpl.
    + repeat safestep; autorewrite with core; eauto.
      rewrite indrep_n_helper_0 in *. destruct_lifts.
      rewrite repeat_selN; auto. rewrite repeat_length in *. auto.
      rewrite indrep_n_helper_valid by omega. cancel.
    + repeat safestep; autorewrite with core; try eassumption.
      - erewrite indrep_n_tree_length in * by eauto.
        rewrite indrep_n_helper_0, listmatch_length_pimpl in *. destruct_lifts.
        erewrite concat_hom_repeat. rewrite repeat_selN. eauto.
        rewrite repeat_length in *.
        match goal with [H : _ |- _] => rewrite <- H end. eassumption.
        rewrite listmatch_lift_r in H; destruct_lifts; eauto.
        intros. match goal with [H : _ |- _] => apply repeat_spec in H end.
        subst. rewrite indrep_n_tree_0. instantiate (1 := fun _ _ => emp).
        split; cancel.
      - indrep_n_tree_bound.
      - rewrite indrep_n_helper_valid by omega.
        cancel.
      - indrep_n_extract.
        rewrite sep_star_comm. repeat rewrite <- sep_star_assoc.
        rewrite sep_star_comm. repeat rewrite <- sep_star_assoc.
        apply pimpl_refl.
        all : indrep_n_tree_bound.
      - match goal with [H : context [indrep_n_helper] |-_] => assert (HH := H) end.
        eapply lt_le_trans. apply Nat.mod_bound_pos; mult_nonzero; omega.
        apply Nat.eq_le_incl.
        rewrite listmatch_extract in HH; autorewrite with lists in *.
        rewrite indrep_n_length_pimpl in HH.
        destruct_lift HH. eauto.
        solve [indrep_n_tree_bound].
      - apply selN_selN_hom.
        eapply indrep_n_indlist_forall_length; eauto.
        rewrite listmatch_length_pimpl, indrep_n_helper_length_piff in *; autorewrite with lists in *.
        destruct_lifts.
        rewrite mult_comm.
        apply div_lt_mul_lt; solve [indrep_n_tree_bound | mult_nonzero].
      Unshelve.
      exact $0.
  Qed.

  Fixpoint indread (indlvl : nat) lxp (ir : addr) ms :=
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 (NIndirect ^ S indlvl))
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      match indlvl with
        | 0 => Ret ^(ms, indbns)
        | S indlvl' =>
          let N := (NIndirect ^ (S indlvl')) in
          r <- ForN i < NIndirect
            Hashmap hm
            Ghost [ F Fm iblocks l_part l bxp crash m0 m ]
            Loopvar [ ms r ]
            Invariant
              LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
              [[[ m ::: Fm * indrep_n_helper bxp ir iblocks *
                        listmatch (fun ibn' l' => indrep_n_tree indlvl' bxp (# ibn') l')
                          iblocks l_part ]]] *
              [[ r = firstn (i * (NIndirect ^ indlvl)) l ]]
            OnCrash crash
            Begin
              let^ (ms, v) <- indread indlvl' lxp #(selN indbns i IndRec.Defs.item0) ms;
              Ret ^(ms, r ++ v)
            Rof ^(ms, nil);
            Ret r
      end
    }.

  (* TODO move this *)
  Ltac cancel_last := repeat match goal with
    | [|- _ * ?a =p=> _ * ?a] => (apply pimpl_sep_star; apply pimpl_refl || fail)
    | [|- (_ * _) * _ =p=> _ ] => rewrite sep_star_comm
    | [|- _ * (_ * _) =p=> _ ] => repeat rewrite <- sep_star_assoc
    end.

  (* TODO move this and use it in indget *)
  Theorem indrep_n_tree_repeat:
    forall (indlvl : addr) (F : pred) (l1 : list waddr) (l2 : list (list waddr)) 
      (bxp : balloc_xparams) (m : Mem.mem),
    ((F ✶ indrep_n_helper bxp 0 l1)
     ✶ listmatch (fun (ibn' : waddr) (l' : list waddr) => indrep_n_tree indlvl bxp # (ibn') l') l1 l2)%pred m ->
    concat l2 = repeat $0 (NIndirect * NIndirect ^ S indlvl).
  Proof.
    intros. rewrite indrep_n_helper_0 in *. destruct_lifts.
    rewrite listmatch_length_pimpl in *; autorewrite with lists in *; destruct_lifts.
    erewrite concat_hom_repeat. repeat f_equal; auto.
    rewrite listmatch_lift_r in *. destruct_lifts; eauto.
    intros. instantiate (1 := fun _ _ => emp). erewrite repeat_spec with (y := x); eauto.
    rewrite indrep_n_tree_0. split; cancel.
  Qed.

  Theorem indread_ok : forall indlvl lxp bxp ir ms,
  {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} indread indlvl lxp ir ms.
  Proof.
    induction indlvl; simpl.
    + hoare.
      - rewrite indrep_n_helper_0 in *. destruct_lifts. rewrite mult_1_r. auto.
      - rewrite indrep_n_helper_valid by auto; cancel.
      - rewrite indrep_n_helper_length_piff in *.
        destruct_lifts. unfold IndRec.Defs.item in *; simpl in *.
        rewrite firstn_oob by omega. auto.
    + hoare.
      - erewrite indrep_n_tree_repeat; eauto. auto.
      - rewrite indrep_n_helper_valid by omega. cancel.
      - rewrite indrep_n_helper_length_piff. cancel.
        rewrite firstn_oob by (unfold IndRec.Defs.item in *; simpl in *; omega).
        indrep_n_extract.
        cancel_last.
        rewrite listmatch_length_pimpl in *. destruct_lifts. omega.
      - rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in *; destruct_lifts.
        rewrite concat_hom_firstn by eauto.
        match goal with [|- context [selN ?l ?n ?d] ] =>
          replace (selN l n d) with (concat [selN l n d]) by (simpl; rewrite app_nil_r; auto)
        end. rewrite <- concat_app.
        rewrite <- firstn_plusone_selN by omega.
        erewrite <- concat_hom_firstn by eauto. rewrite plus_comm. simpl. auto.
      - apply firstn_oob.
        erewrite indrep_n_tree_length by eauto. auto.
      - apply LOG.rep_hashmap_subset; eauto.
    Grab Existential Variables. all : eauto; split; solve [eauto | exact ($0)].
  Qed.
Check (updN (repeat $0 NIndirect) 3 $ 5).

  Definition indput_upd_if_necessary lxp ir v indbns to_grow ms := 
    If (addr_eq_dec v #(selN indbns to_grow $0)) {
      Ret ms
    } else {
      IndRec.write lxp ir (indbns ⟦ to_grow := ($ v)⟧) ms
    }.

  Theorem indput_upd_if_necessary_ok : forall lxp ir v indbns to_grow ms,
    {< F Fm m0 m bxp,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm * [[ BALLOC.bn_valid bxp ir ]] *
           [[[ m ::: (Fm * indrep_n_helper bxp ir indbns) ]]]
    POST:hm' RET: ms
           exists m' indbns', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[ indbns' = updN indbns to_grow ($ v) ]] *
           [[[ m' ::: (Fm * indrep_n_helper bxp ir indbns') ]]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indput_upd_if_necessary lxp ir v indbns to_grow ms.
  Proof.
    unfold indput_upd_if_necessary. unfold BALLOC.bn_valid.
    hoare.
    rewrite natToWord_wordToNat. rewrite updN_selN_eq. cancel.
    unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
    unfold Rec.well_formed. simpl. intuition.
    rewrite length_updN. rewrite indrep_n_helper_length_piff in *. destruct_lifts.
    omega.
    rewrite indrep_n_helper_valid by omega. cancel.
    rewrite indrep_n_helper_valid by omega. cancel.
    unfold BALLOC.bn_valid. intuition.
  Qed.

  Local Hint Extern 0 ({{_}} Bind (indput_upd_if_necessary _ _ _ _ _ _) _) => apply indput_upd_if_necessary_ok : prog.

  Definition indput_get_blocks {P} {Q} lxp (is_alloc : {P} + {Q}) ir ms :=
    If (is_alloc) {
      Ret ^(ms, repeat $0 NIndirect)
    } else {
      IndRec.read lxp ir 1 ms
    }.

  Theorem indput_get_blocks_ok : forall P Q lxp (is_alloc : {P} + {Q}) ir ms,
    {< F Fm m0 m bxp indbns,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm * [[ BALLOC.bn_valid bxp ir ]] *
           [[ P -> ir = 0 ]] * [[ Q -> ir <> 0 ]] *
           [[[ m ::: (Fm * indrep_n_helper bxp ir indbns) ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' * [[ r = indbns ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indput_get_blocks lxp is_alloc ir ms.
    Proof.
      unfold indput_get_blocks. unfold indrep_n_helper. intros.
      hoare. destruct_lifts. auto.
      destruct addr_eq_dec; try omega. cancel.
      apply firstn_oob.
      unfold IndRec.rep, IndRec.items_valid, IndSig.RALen in *.
      destruct addr_eq_dec; destruct_lifts.
      rewrite repeat_length. omega.
      omega.
    Qed.

  Local Hint Extern 0 ({{_}} Bind (indput_get_blocks _ _ _ _) _) => apply indput_get_blocks_ok : prog.

  Theorem IndRec_write_no_rep_ok : forall lxp xp items ms,
    {< F Fm m0 m old,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ IndRec.items_valid xp items ]] * [[ xp <> 0 ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) xp [old] ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
          [[[ m' ::: Fm * IndRec.rep xp items ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} IndRec.write lxp xp items ms.
  Proof.
    unfold IndRec.write, IndRec.rep, IndRec.items_valid.
    hoare.
    unfold IndSig.RAStart. instantiate (1 := [_]). cancel.
    rewrite IndRec.Defs.ipack_one. auto.
    unfold IndRec.Defs.item in *. simpl in *. omega.
    rewrite vsupsyn_range_synced_list; auto.
    rewrite IndRec.Defs.ipack_one. auto.
    unfold IndRec.Defs.item in *. simpl in *. omega.
  Qed.

  Local Hint Extern 0 ({{_}} Bind (IndRec.write _ _ _ _) _) => apply IndRec_write_no_rep_ok : prog.

  Fixpoint indput indlvl bxp lxp root off bn ms :=
    let N := NIndirect ^ indlvl in
    let is_alloc := (addr_eq_dec root 0) in
    let^ (ms, ir) <- If (is_alloc) {
        BALLOC.alloc lxp bxp ms
      } else {
        Ret ^(ms, Some root)
      };
    match ir with
    | None => Ret ^(ms, 0)
    | Some ir =>
      match indlvl with
      | 0 => ms <- If (is_alloc) {
                     IndRec.write lxp ir ((repeat $0 NIndirect) ⟦ off := bn ⟧) ms
                   } else {
                     IndRec.put lxp ir off bn ms
                   };
        Ret ^(ms, ir)
      | S indlvl' =>
        let to_grow := off / N in
        let^ (ms, indbns) <- indput_get_blocks lxp is_alloc ir ms;
        let ir_to_grow := #(selN indbns to_grow $0) in
        let^ (ms, v) <- indput indlvl' bxp lxp ir_to_grow (off mod N) bn ms;
        If (addr_eq_dec v 0) {
          Ret ^(ms, 0)
        } else {
          ms <- indput_upd_if_necessary lxp ir v indbns to_grow ms;
          Ret ^(ms, ir)
        }
      end
    end.

  (* TODO move this *)
  Theorem indrep_n_helper_pts_piff : forall bxp ir l,
    ir <> 0 -> indrep_n_helper bxp ir l <=p=> [[ length l = NIndirect ]] *
                [[ BALLOC.bn_valid bxp ir ]] * ir |-> (IndRec.Defs.block2val l, []).
  Proof.
    intros.
    unfold indrep_n_helper, IndRec.rep. destruct addr_eq_dec; try omega.
    unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
    rewrite mult_1_l. unfold Rec.well_formed. simpl.
    split; cancel;
    rewrite IndRec.Defs.ipack_one by (unfold IndRec.Defs.item in *; auto).
    all : cancel.
  Qed.

  (* TODO move to listutils *)
  Lemma repeat_updN : forall T n (v : T) i, updN (repeat v n) i v = repeat v n.
  Proof.
    induction n; intros; simpl. auto.
    destruct i. auto.
    f_equal. auto.
  Qed.

  Theorem indput_ok : forall indlvl lxp bxp ir off bn ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp ir l * BALLOC.rep bxp freelist) ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, ir')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           ([[ ir' = 0 ]] \/
           exists freelist' l',
           [[ ir = 0 \/ ir = ir' ]] *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp ir' l' * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist' freelist ]] * [[ l' = updN l off bn ]])
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indput indlvl bxp lxp ir off bn ms.
    Proof.
      induction indlvl; intros; simpl.
      + step.
        - hoare.
          --  unfold IndRec.items_valid, IndSig.RAStart, IndSig.RALen, IndSig.xparams_ok.
              rewrite mult_1_l. unfold Rec.well_formed. simpl. unfold BALLOC.bn_valid in *.
              rewrite length_updN, repeat_length. intuition.
          --  unfold BALLOC.bn_valid in *. intuition.
          --  or_r. cancel. unfold BALLOC.bn_valid in *; intuition.
              rewrite indrep_n_helper_0. rewrite indrep_n_helper_valid by omega.
              unfold BALLOC.bn_valid. cancel.
              apply incl_remove.
        - hoare.
        --  rewrite indrep_n_helper_valid by omega. cancel.
        --  or_r. cancel.
            rewrite indrep_n_helper_valid in * by omega. cancel.
            match goal with [H : context [?P] |- ?P] => destruct_lift H end. auto.
      + step.
        - step. safestep.
          rewrite repeat_selN, roundTrip_0. rewrite indrep_n_helper_0. rewrite indrep_n_tree_0. cancel.
          eapply indrep_index_bound_helper; eauto.
          match goal with [H : _ |- _] => 
            eapply pimpl_apply; [> | exact H]; cancel; cancel_last
          end.
          rewrite repeat_length. apply Nat.mod_bound_pos; mult_nonzero; omega.
          rewrite repeat_selN. rewrite roundTrip_0.
          unfold indput_upd_if_necessary. rewrite repeat_selN, roundTrip_0.
          hoare.
          match goal with [H : BALLOC.bn_valid _ _ |- _] =>
            let H' := fresh in (apply BALLOC.bn_valid_facts in H as H') end.
          unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed.
          simpl. rewrite length_updN, repeat_length. intuition.
          unfold BALLOC.bn_valid in *. intuition.
          or_r.
          norm. cancel. repeat split; auto.
          pred_apply. norm; intuition.
          instantiate (iblocks := updN _ _ _). cancel.
          unfold BALLOC.bn_valid in *; intuition.
          rewrite indrep_n_helper_valid by omega. cancel.
          rewrite listmatch_updN_removeN.
          indrep_n_extract. cancel.
          rewrite repeat_selN, roundTrip_0. rewrite indrep_n_tree_0.
          rewrite wordToNat_natToWord_idempotent'. cancel.
          eapply BALLOC.bn_valid_goodSize; eauto.
          (* TODO move this *)
          Theorem indrep_n_tree_valid_piff : forall indlvl bxp ir l,
            ir <> 0 -> indrep_n_tree indlvl bxp ir l <=p=> indrep_n_tree indlvl bxp ir l * [[ BALLOC.bn_valid bxp ir ]].
          Proof.
            destruct indlvl; intros; simpl.
            repeat rewrite indrep_n_helper_valid by auto. split; cancel.
            split; intros m' H'; destruct_lift H'; pred_apply; cancel.
            rewrite indrep_n_helper_valid in * by auto. destruct_lifts. auto.
          Qed.
          rewrite indrep_n_tree_valid_piff in * by auto. destruct_lifts. auto.
          all : try rewrite repeat_length; try solve [indrep_n_tree_bound |
            eapply indrep_index_bound_helper; eauto;
            match goal with [H : context [listmatch _ _ ?l] |- context [listmatch _ _ ?l] ] =>
              eapply pimpl_apply; [> |exact H]; cancel end; rewrite indrep_n_helper_0; cancel].
          unfold BALLOC.bn_valid. auto.
          erewrite Nat.div_mod with (x := off) at 1.
          rewrite plus_comm, mult_comm. rewrite updN_concat. f_equal.
          match goal with [H : context [?l] |- context [selN ?l] ] =>
            rewrite listmatch_extract with (b := l) in H
          end. rewrite repeat_selN in *. rewrite roundTrip_0, indrep_n_tree_0 in *.
          destruct_lifts.
          match goal with [H : selN _ _ _ = _ |- _] => rewrite H end. reflexivity.
          all : try rewrite repeat_length; try solve [indrep_n_tree_bound |
            eapply indrep_index_bound_helper; eauto;
            match goal with [H : context [listmatch _ _ ?l] |- context [listmatch _ _ ?l] ] =>
              eapply pimpl_apply; [> |exact H]; cancel end; rewrite indrep_n_helper_0; cancel].
          apply Nat.mod_bound_pos; mult_nonzero; omega.
          eapply indrep_n_indlist_forall_length.
          match goal with [H : context [listmatch _ _ ?l] |- context [listmatch _ _ ?l] ] =>
            eapply pimpl_apply; [> |exact H]; cancel end. rewrite indrep_n_helper_0. cancel.
          mult_nonzero.

          (* TODO move this *)
          Ltac incl_solve := match goal with
          | [|- incl ?a ?a ] => apply incl_refl
          | [|- incl (remove _ _ ?l) ?l ] => apply incl_remove
          | [|- incl ?l (_ :: ?l)] => apply incl_tl; solve [incl_solve]
          | [H : incl ?a ?b |- incl ?a ?c ] => eapply incl_tran; [> apply H|]; solve [incl_solve]
          | [H : incl ?b ?c |- incl ?a ?c ] => eapply incl_tran; [> |apply H]; solve [incl_solve]
          end.
          Local Hint Extern 1 (incl ?a ?b) => incl_solve.
          auto.
          cancel.
          or_l. cancel.
        - monad_simpl. simpl. step.
          rewrite indrep_n_helper_valid in * by auto. destruct_lifts. eauto.
          cancel_last.
          safestep.
          indrep_n_extract; solve [cancel_last | indrep_n_tree_bound].
          eapply lt_le_trans.
          apply Nat.mod_bound_pos; mult_nonzero; omega.
          apply Nat.eq_le_incl. symmetry. apply Forall_selN.
          eapply indrep_n_indlist_forall_length.
          match goal with [H : context [listmatch _ _ ?l] |- context [listmatch _ _ ?l] ] =>
            eapply pimpl_apply; [> |exact H]; cancel end. cancel_last.
          indrep_n_tree_bound.
          step. step. step. step. step.
          rewrite indrep_n_helper_valid in * by omega. destruct_lifts. auto.
          step. or_r.
          norm. cancel. repeat (split; try reflexivity). auto.
          pred_apply. norm; intuition.
          instantiate (iblocks := updN _ _ _). cancel.
          rewrite listmatch_updN_removeN. cancel.
          rewrite wordToNat_natToWord_idempotent'. cancel. apply pimpl_refl.
          eapply BALLOC.bn_valid_goodSize; eauto.
          rewrite indrep_n_tree_valid_piff in * by auto. destruct_lifts. auto.
          indrep_n_tree_bound. indrep_n_tree_bound.
          erewrite Nat.div_mod with (x := off) at 1.
          rewrite plus_comm, mult_comm. rewrite updN_concat. reflexivity.
          apply Nat.mod_bound_pos; mult_nonzero; omega.
          eapply indrep_n_indlist_forall_length.
          match goal with [H : context [listmatch _ _ ?l] |- context [listmatch _ _ ?l] ] =>
            eapply pimpl_apply; [> |exact H]; cancel end. cancel_last.
          mult_nonzero.
          auto.
          step. step.
          rewrite indrep_n_helper_valid in * by omega. destruct_lifts. auto.
          step.
          or_r.
          norm. cancel. repeat split. auto.
          pred_apply. norm; intuition.
          instantiate (iblocks := updN _ _ _). cancel.
          rewrite listmatch_updN_removeN. cancel.
          rewrite natToWord_wordToNat. cancel. apply pimpl_refl.
          indrep_n_tree_bound.
          indrep_n_tree_bound.
          erewrite Nat.div_mod with (x := off) at 1.
          rewrite plus_comm, mult_comm. rewrite updN_concat. reflexivity.
          apply Nat.mod_bound_pos; mult_nonzero; omega.
          eapply indrep_n_indlist_forall_length.
          match goal with [H : context [listmatch _ _ ?l] |- context [listmatch _ _ ?l] ] =>
            eapply pimpl_apply; [> |exact H]; cancel end. cancel_last.
          mult_nonzero.
          auto.
          cancel.
    Grab Existential Variables. all : auto; solve [exact nil | exact $0].
  Qed.

  (************* program *)

  Definition get lxp (ir : irec) off ms :=
    If (lt_dec off NDirect) {
      Ret ^(ms, selN (IRBlocks ir) off $0)
    } else {
      let^ (ms, v) <- indget 0 lxp (IRIndPtr ir) (off - NDirect) ms;
      Ret ^(ms, v)
    }.

  Definition read lxp (ir : irec) ms :=
    If (le_dec (IRLen ir) NDirect) {
      Ret ^(ms, firstn (IRLen ir) (IRBlocks ir))
    } else {
      let^ (ms, indbns) <- indread 0 lxp (IRIndPtr ir) (IRLen ir - NDirect) ms;
      Ret ^(ms, (firstn (IRLen ir) ((IRBlocks ir) ++ indbns)))
    }.

  Definition free_ind_dec ol nl :
    { ol > NDirect /\ nl <= NDirect } + { ol <= NDirect \/ nl > NDirect }.
  Proof.
    destruct (gt_dec ol NDirect).
    destruct (le_dec nl NDirect).
    left; split; assumption.
    right; right; apply not_le; assumption.
    right; left; apply not_gt; assumption.
  Defined.


  Definition shrink lxp bxp (ir : irec) nr ms :=
    let nl := ((IRLen ir) - nr) in
    If (free_ind_dec (IRLen ir) nl) {
      ms <- BALLOC.free lxp bxp (IRIndPtr ir) ms;
      Ret ^(ms, upd_len ir nl)
    } else {
      Ret ^(ms, upd_len ir nl)
    }.


  Definition grow lxp bxp (ir : irec) bn ms :=
    let len := (IRLen ir) in
    If (lt_dec len NDirect) {
      (* change direct block address *)
      Ret ^(ms, Some (upd_irec ir (S len) (IRIndPtr ir) (updN (IRBlocks ir) len bn)))
    } else {
      (* allocate indirect block if necessary *)
      let^ (ms, ibn) <- If (addr_eq_dec len NDirect) {
        let^ (ms, r) <- BALLOC.alloc lxp bxp ms;
        match r with
        | None => Ret ^(ms, None)
        | Some ibn =>
            ms <- IndRec.init lxp ibn ms;
            Ret ^(ms, Some ibn)
        end
      } else {
        Ret ^(ms, Some (IRIndPtr ir))
      };
      match ibn with
      | Some ibn =>
        (* write indirect block *)
        ms <- IndRec.put lxp ibn (len - NDirect) bn ms;
        Ret ^(ms, Some (upd_irec ir (S len) ibn (IRBlocks ir)))
      | None => Ret ^(ms, None)
      end
    }.

  Fact div_mod_le : forall a b, b <> 0 -> a mod b + a / b * b <= a.
  Proof.
    intros.
    destruct (le_lt_dec (a mod b) 0).
    rewrite mul_div; omega.
    rewrite mult_comm, plus_comm.
    rewrite <- Nat.div_mod; omega.
  Qed.

  Fact sub_mult_bound : forall n a b c, b >= c * n -> a < c -> b - a * n >= n.
  Proof.
    intros.
    remember (c - a) as e. assert (c = a + e) by omega; subst c.
    rewrite Nat.mul_add_distr_r in *.
    assert (1 <= e) by omega.
    assert (n <= e * n).
    rewrite <- mult_1_l at 1.
    apply mult_le_compat_r; auto.
    lia.
  Qed.

  Hint Rewrite length_enumerate firstn_enumerate : list.

  Opaque indget.
  Hint Extern 1 ({{_}} Bind (indget _ _ _ _ _) _) => apply indget_ok : prog.
  Hint Extern 1 ({{_}} Bind (indread _ _ _ _) _) => apply indread_ok : prog.

  Theorem get_ok : forall lxp bxp ir off ms,
    {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * rep bxp ir l ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} get lxp ir off ms.
  Proof.
    unfold get.
    step.
    step.
    eapply rep_selN_direct_ok; eauto.

    prestep; norml.
    rewrite rep_piff_indirect in H0 by omega.
    unfold rep_indirect in H0; destruct_lift H0; cancel; try omega.
    eassumption.
    step; substl.
    substl NDirect; rewrite selN_app2.
    rewrite selN_firstn by omega; auto.
    omega.
  Qed.


  Theorem read_ok : forall lxp bxp ir ms,
    {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * rep bxp ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} read lxp ir ms.
  Proof.
    unfold read.
    step; denote rep as Hx.
    step.
    rewrite rep_piff_direct in Hx; unfold rep_direct in Hx; destruct_lift Hx.
    substl; substl (length l); auto.
    unfold rep in H; destruct_lift H; omega.

    prestep; norml.
    rewrite rep_piff_indirect in Hx.
    unfold rep_indirect in Hx; destruct_lift Hx; cancel.
    step; substl.
    rewrite Nat.add_0_r, firstn_app_le by omega.
    setoid_rewrite firstn_oob at 2; try omega.
    substl (length l); substl NDirect; auto.
    unfold rep in Hx; destruct_lift Hx; omega.
  Qed.



  Lemma indrec_ptsto_pimpl : forall ibn indrec,
    IndRec.rep ibn indrec =p=> exists v, ibn |-> (v, nil).
  Proof.
    unfold IndRec.rep; cancel.
    assert (length (synced_list (IndRec.Defs.ipack indrec)) = 1).
    unfold IndRec.items_valid in H2; intuition.
    rewrite synced_list_length; subst.
    rewrite IndRec.Defs.ipack_length.
    setoid_rewrite H0.
    rewrite Rounding.divup_mul; auto.
    apply IndRec.Defs.items_per_val_not_0.

    rewrite arrayN_isolate with (i := 0) by omega.
    unfold IndSig.RAStart; rewrite Nat.add_0_r.
    rewrite skipn_oob by omega; simpl.
    instantiate (2 := ($0, nil)).
    rewrite synced_list_selN; cancel.
  Qed.

  Hint Rewrite cuttail_length : core.
  Hint Rewrite upd_len_get_len upd_len_get_ind upd_len_get_blk upd_len_get_iattr : core.
  Hint Rewrite upd_irec_get_len upd_irec_get_ind upd_irec_get_blk upd_irec_get_iattr : core.
  Local Hint Resolve upd_len_get_iattr upd_irec_get_iattr.

  Theorem shrink_ok : forall lxp bxp ir nr ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, r)  exists m' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp r (cuttail nr l) * BALLOC.rep bxp freelist') ]]] *
           [[ r = upd_len ir ((IRLen ir) - nr) ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} shrink lxp bxp ir nr ms.
  Proof.
    unfold shrink.
    prestep; norml.
    assert (length l = (IRLen ir)); denote rep as Hx.
    unfold rep in Hx; destruct_lift Hx; omega.

    (* needs to free indirect block *)
    prestep; norml.
    rewrite rep_piff_indirect in Hx by omega.
    unfold rep_indirect in Hx; destruct_lift Hx.
    denote IndRec.rep as Hx; rewrite indrec_ptsto_pimpl in Hx.
    destruct_lift Hx; cancel.

    step.
    rewrite rep_piff_direct by (rewrite cuttail_length; omega).
    unfold rep_direct; cancel; autorewrite with core; try omega.
    apply le_ndirect_goodSize; omega.

    substl l at 1; unfold cuttail.
    rewrite app_length, firstn_length_l by omega.
    rewrite firstn_app_l by omega.
    f_equal; omega.

    (* no free indirect block *)
    cancel.

    (* case 1: all in direct blocks *)
    repeat rewrite rep_piff_direct by (autorewrite with core; omega).
    unfold rep_direct; cancel; autorewrite with core; try omega.
    apply le_ndirect_goodSize; omega.

    substl l at 1; unfold cuttail.
    rewrite firstn_length_l by omega.
    rewrite firstn_firstn, Nat.min_l by omega; auto.

    (* case 1: all in indirect blocks *)
    repeat rewrite rep_piff_indirect by (autorewrite with core; omega).
    unfold rep_indirect; cancel; autorewrite with core; eauto; try omega.
    apply le_nblocks_goodSize; omega.

    substl l at 1; unfold cuttail.
    rewrite app_length, firstn_length_l by omega.
    replace (length (IRBlocks ir) + (length l - NDirect) - nr) with
            (length (IRBlocks ir) + (length l - nr - NDirect)) by omega.
    rewrite firstn_app_r; f_equal.
    rewrite firstn_firstn, Nat.min_l by omega; auto.
  Qed.


  Theorem grow_ok : forall lxp bxp ir bn ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ length l < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' \/
           exists m' freelist' ir',
           [[ r = Some ir' ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ir' (l ++ [bn]) * BALLOC.rep bxp freelist') ]]] *
           [[ IRAttrs ir' = IRAttrs ir /\ length (IRBlocks ir') = length (IRBlocks ir) ]] *
           [[ incl freelist' freelist ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow lxp bxp ir bn ms.
  Proof.
    unfold grow.
    prestep; norml.
    assert (length l = (IRLen ir)); denote rep as Hx.
    unfold rep in Hx; destruct_lift Hx; omega.
    cancel.

    (* only update direct block *)
    prestep; norml.
    rewrite rep_piff_direct in Hx by omega.
    unfold rep_direct in Hx; cancel.
    or_r; cancel.
    rewrite rep_piff_direct by (autorewrite with lists; simpl; omega).
    unfold rep_direct; autorewrite with core lists; simpl.
    cancel; try omega.
    substl l at 1; substl (length l).
    apply firstn_app_updN_eq; omega.
    apply le_nblocks_goodSize; omega.
    autorewrite with core lists; auto.

    (* update indirect blocks *)
    step.
    step.

    (* case 1 : need allocate indirect block *)
    step; try (eapply BALLOC.bn_valid_facts; eauto).
    unfold IndSig.xparams_ok; auto.
    instantiate (1 := [(dummy_cur, dummy_old)]); simpl; auto.
    simpl; unfold IndSig.RAStart; cancel.

    step.
    rewrite repeat_length; omega.
    step.
    or_r; cancel.
    rewrite rep_piff_direct by omega.
    rewrite rep_piff_indirect by (rewrite app_length; simpl; omega).
    unfold rep_direct, rep_indirect; cancel;
      repeat (autorewrite with core lists; simpl; eauto; try omega).
    eapply BALLOC.bn_valid_goodSize; eauto.
    apply le_nblocks_goodSize; omega.
    eapply BALLOC.bn_valid_goodSize; eauto.

    substl l at 1; substl (length l); substl (IRLen ir).
    rewrite firstn_oob, minus_plus, Nat.sub_diag by omega.
    erewrite firstn_S_selN, selN_updN_eq by (autorewrite with lists; omega).
    simpl; auto.
    autorewrite with core lists; auto.

    apply incl_remove.

    (* case 2 : just update the indirect block *)
    prestep; norml.
    rewrite rep_piff_indirect in Hx by omega.
    unfold rep_indirect in Hx; destruct_lift Hx; cancel; try omega.
    2: cancel.
    omega.

    step.
    or_r; cancel.
    rewrite rep_piff_indirect by (rewrite app_length; simpl; omega).
    unfold rep_indirect; cancel;
      repeat (autorewrite with core lists; simpl; eauto; try omega).
    eapply BALLOC.bn_valid_goodSize; eauto.
    apply le_nblocks_goodSize; omega.
    eapply BALLOC.bn_valid_goodSize; eauto.
    substl l at 1; substl (length l).
    replace (IRLen ir + 1 - NDirect) with (IRLen ir - NDirect + 1) by omega.
    rewrite <- app_assoc; f_equal.
    rewrite firstn_app_updN_eq; auto.
    substl (length dummy); omega.
    autorewrite with core lists; auto.

    cancel.

    Unshelve. all:eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _) _) => apply grow_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


  Theorem xform_rep : forall xp ir l,
    crash_xform (rep xp ir l) <=p=> rep xp ir l.
  Proof.
    unfold rep, indrep; intros; split.
    xform_norm.
    cancel; eauto.
    rewrite IndRec.xform_rep; cancel.

    cancel.
    xform_normr.
    rewrite crash_xform_exists_comm; cancel.
    xform_normr.
    cancel; eauto.

    cancel.
    xform_normr.
    rewrite crash_xform_exists_comm; cancel.
    xform_normr.
    cancel; eauto.
    or_r; cancel.
    rewrite IndRec.xform_rep; auto.
  Qed.

End BlockPtr.

