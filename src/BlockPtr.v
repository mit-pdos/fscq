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

   Definition indrep_n_helper bxp ibn iblocks nvalid :=
    (if (addr_eq_dec nvalid 0)
      then [[ length iblocks = NIndirect ]]
      else [[ BALLOC.bn_valid bxp ibn ]] * IndRec.rep ibn iblocks
    )%pred.

  (* indlvl = 0 if ibn is the address of an indirect block,
     indlvl = 1 for doubly indirect, etc. *)

 Fixpoint indrep_n_tree indlvl bxp ibn l nvalid :=
    (match indlvl with
    | 0 => indrep_n_helper bxp ibn l nvalid
    | S indlvl' => let divisor := NIndirect ^ indlvl in
                    exists iblocks l_part, [[ l = concat l_part ]] *
                    indrep_n_helper bxp ibn iblocks (divup nvalid divisor) *
                    listmatch (fun index_ibn' l' => let '(index, ibn') := index_ibn' in
                        indrep_n_tree indlvl' bxp (# ibn') l' (nvalid - index * divisor))
                      (enumerate iblocks) l_part
    end)%pred.

  Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (indrep_n_tree _ _ _ _ _) (indrep_n_tree _ _ _ _ _)) => constructor : okToUnify.

  Definition indrep bxp ir (indlist : list waddr) nblocks :=
    ( [[ nblocks = 0 ]] \/ (
      [[ nblocks > 0 ]] * indrep_n_tree 0 bxp (IRIndPtr ir) indlist nblocks))%pred.

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
      exists indlist, indrep_n_tree 0 bxp (IRIndPtr ir) indlist (length l - NDirect) *
      [[ l = (IRBlocks ir) ++ firstn (length l - NDirect) indlist ]] )%pred.

  (* Necessary to make subst work when there's a recursive term like:
     l = firstn (length l) ... *)
  Set Regular Subst Tactic.

  Lemma indrep_n_helper_0 : forall bxp ibn l,
    indrep_n_helper bxp ibn l 0 <=p=> [[ length l = NIndirect ]] * emp.
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

  Fact nvalid_gt_0_indrep_helper : forall bxp bn l nvalid, nvalid > 0 ->
    indrep_n_helper bxp bn l nvalid <=p=> [[BALLOC.bn_valid bxp bn]] * IndRec.rep bn l.
  Proof.
    unfold indrep_n_helper; intros; destruct addr_eq_dec; simpl; solve [omega | auto].
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

  Lemma indrep_n_helper_length : forall bxp ibn l nvalid m,
    indrep_n_helper bxp ibn l nvalid m -> length l = NIndirect.
  Proof.
    unfold indrep_n_helper, IndRec.rep, IndRec.items_valid.
    intros; destruct addr_eq_dec; destruct_lift H; unfold lift_empty in *;
    intuition; subst; autorewrite with lists; auto.
  Qed.

  Lemma indrep_n_helper_length_piff : forall bxp ibn l nvalid,
    indrep_n_helper bxp ibn l nvalid <=p=> indrep_n_helper bxp ibn l nvalid * [[ length l = NIndirect ]].
  Proof.
    intros.
    split; [> intros m H; apply indrep_n_helper_length in H as HH; pred_apply | ]; cancel.
  Qed.

  Lemma indrep_n_tree_listmatch_lift_helper : forall indlvl nvalid bxp index (ibn : waddr) y,
    (fun n_w y => indrep_n_tree indlvl bxp # (snd n_w) y (nvalid - (fst n_w) * (NIndirect * NIndirect ^ indlvl)))
      (index, ibn) y <=p=> indrep_n_tree indlvl bxp # (ibn) y (nvalid - index * (NIndirect * NIndirect ^ indlvl)).
  Proof.
    intros; simpl.
    apply piff_refl.
  Qed.

  Lemma indrep_n_length_pimpl : forall indlvl bxp ibn l nvalid,
    indrep_n_tree indlvl bxp ibn l nvalid <=p=>
    [[ length l = NIndirect ^ (S indlvl) ]] * indrep_n_tree indlvl bxp ibn l nvalid.
  Proof.
    induction indlvl; simpl; intros.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    erewrite indrep_n_helper_length; eauto; omega.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in H; destruct_lift H.
    rewrite length_enumerate in *.
    rewrite listmatch_lift_r in H; destruct_lift H.
    erewrite concat_hom_length; eauto.
    f_equal; omega.
    intros x y; destruct x.
    rewrite indrep_n_tree_listmatch_lift_helper.
    split; [> rewrite IHindlvl |]; cancel.
  Qed.

  Lemma indget_length_helper_l : forall Fm off nvalid indlvl bxp bn iblocks l_part m f,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks nvalid) *
          listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
           let '(index, ibn') := index_ibn' in
            indrep_n_tree indlvl bxp # (ibn') l' (f index))
          (enumerate iblocks) l_part)%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < length (iblocks).
  Proof.
    intros.
    apply Nat.div_lt_upper_bound; mult_nonzero.
    rewrite listmatch_length_pimpl, listmatch_lift_r in *.
    rewrite indrep_n_helper_length_piff in *.
    rewrite length_enumerate in *.
    destruct_lifts.
    match goal with
    | [ H : ?off < length (concat ?l) |- _] => erewrite concat_hom_length in H by eauto
    end.
    rewrite mult_comm.
    substl (length iblocks); eauto.
    intros x y. destruct x. intros.
    instantiate (1 := fun x y => indrep_n_tree indlvl bxp (# (snd x)) y (f (fst x))).
    rewrite indrep_n_length_pimpl; split; cancel.
  Qed.

  Lemma indget_length_helper_r : forall Fm off nvalid indlvl bxp bn iblocks l_part m f,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks nvalid) *
          listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
           let '(index, ibn') := index_ibn' in
            indrep_n_tree indlvl bxp # (ibn') l' (f index))
          (enumerate iblocks) l_part)%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < length l_part.
  Proof.
    intros.
    rewrite listmatch_length_pimpl in *.
    rewrite length_enumerate in *.
    match goal with
    | [ H : context [ lift_empty ] |- _] => destruct_lift H
    end.
    substl (length l_part).
    eapply indget_length_helper_l; eauto.
  Qed.

  Hint Resolve indget_length_helper_l indget_length_helper_r.

  Lemma mult_ge_l : forall m n,
    0 < m -> n <= n * m.
  Proof.
    intros.
    rewrite mult_comm.
    destruct (mult_O_le n m); solve [ omega | auto].
  Qed.

  Lemma divup_bound_helper : forall m n a k k', m < divup n a -> n <= k * a -> k' = k -> m < k'.
  Proof.
    intros; subst.
    eapply lt_le_trans; eauto.
    apply divup_le; rewrite mult_comm; auto.
  Qed.

  Theorem indrep_n_tree_nvalid_oob : forall indlvl bxp ibn l nvalid,
    nvalid >= (NIndirect ^ S indlvl) ->
    indrep_n_tree indlvl bxp ibn l nvalid <=p=> indrep_n_tree indlvl bxp ibn l (NIndirect ^ S indlvl).
  Proof.
    intros.
    pose proof IndRec.Defs.items_per_val_gt_0'.
    assert (NIndirect <= NIndirect ^ (S indlvl)).
    simpl; apply mult_ge_l; solve [mult_nonzero | auto].
    assert (nvalid > 0) by omega.
    generalize dependent nvalid.
    generalize dependent l.
    generalize dependent ibn.
    generalize dependent bxp.
    induction indlvl; simpl; intros.
    split; cancel; repeat rewrite nvalid_gt_0_indrep_helper by omega; cancel.
    split; intros m H'; destruct_lift H'; repeat rewrite nvalid_gt_0_indrep_helper in * by omega;
    match goal with [H : _ |- _] => destruct_lift H end; pred_apply; cancel.
    all : rewrite divup_mul in * by mult_nonzero.
    all : assert (divup nvalid (NIndirect * NIndirect ^ indlvl) > 0) by
            (apply divup_mul_ge; mult_nonzero; rewrite mult_comm;
             eapply le_trans; [> apply mult_le_compat_r | apply H]; auto).
    all : repeat rewrite nvalid_gt_0_indrep_helper in * by auto.
    all : erewrite listmatch_piff_replace; try cancel.
    all : intros x y; destruct x; intros.
    all : unfold IndRec.rep, IndRec.items_valid in *; destruct_lifts.
    all : unfold enumerate in *; apply in_combine_l, in_seq in H5.
    all : unfold IndRec.Defs.item in *; simpl in *.
    all : split; intros mm HH.
    all : apply IHindlvl in HH; try apply IHindlvl; eauto.
    all : repeat match goal with
    | [ |- ?n + ?a * ?n <= _ ] => replace n with (1 * n) at 1 by omega
    | [ |- _ - _ > _ ] => apply Nat.lt_add_lt_sub_r; simpl
    | [ |- _ - _ >= _ ] => apply Nat.le_add_le_sub_r; simpl
    | [ H : ?nvalid >= ?n * ?k |- _ < ?nvalid ] => eapply lt_le_trans; [> | apply H]
    | [ H : ?nvalid >= ?n * ?k |- _ <= ?nvalid ] => eapply le_trans; [> | apply H]
    | [ |- ?a * ?n < ?b * ?n] => apply mult_lt_compat_r
    | [ |- ?a * ?n <= ?b * ?n] => apply mult_le_compat_r
    | [ |- context [?a * ?n + ?b * ?n] ] => rewrite <- Nat.mul_add_distr_r
    | [ |- _] => solve [apply mult_ge_l; mult_nonzero | omega | mult_nonzero]
    end.
  Qed.

  Lemma indrep_n_tree_length: forall indlvl F ir l1 l2 bxp nvalid n m, (F *
    indrep_n_helper bxp ir l1 n *
    listmatch
     (fun index_ibn' l' => let '(index, ibn') := index_ibn' in
       indrep_n_tree indlvl bxp # (ibn') l' (nvalid - index * (NIndirect * NIndirect ^ indlvl)))
     (enumerate l1) l2)%pred m-> length (concat l2) = NIndirect * (NIndirect ^ (S indlvl)).
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff in H.
    rewrite listmatch_length_pimpl in H.
    erewrite listmatch_lift_r in H.
    destruct_lift H.
    rewrite length_enumerate in *.
    erewrite concat_hom_length; eauto.
    f_equal; omega.
    intros.
    destruct x.
    rewrite indrep_n_tree_listmatch_lift_helper.
    apply indrep_n_length_pimpl.
  Qed.

  Lemma indrep_n_indlist_forall_length : forall F indlvl bxp ir l1 l2 n nvalid m,
    ((F ✶ indrep_n_helper bxp ir l1 n)
        ✶ listmatch
            (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
             let '(index, ibn') := index_ibn' in
              indrep_n_tree indlvl bxp # (ibn') l' (nvalid - index * (NIndirect * NIndirect ^ indlvl)))
            (enumerate l1) l2)%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff, listmatch_lift_r in H.
    destruct_lifts; eauto.
    intros x; destruct x; intros.
    rewrite indrep_n_tree_listmatch_lift_helper.
    apply indrep_n_length_pimpl.
  Qed.

  Local Hint Resolve indrep_n_indlist_forall_length.

  Ltac divide_mult := match goal with
    | [ |- Nat.divide 1 ?n ] => apply Nat.divide_1_l
    | [ |- Nat.divide ?n 0 ] => apply Nat.divide_0_r
    | [ |- Nat.divide ?a ?a ] => apply Nat.divide_refl
    | [ |- Nat.divide ?a (?b * ?c) ] => solve [apply Nat.divide_mul_l; divide_mult |
                                               apply Nat.divide_mul_r; divide_mult ]
  end.

  Theorem listmatch_indrep_n_helper_valid : forall bxp l l_part f,
    (forall x, x < length l -> f x > 0) ->
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
               let '(index, ibn') := index_ibn' in
                indrep_n_helper bxp # (ibn') l' (f index))
              (enumerate l) l_part <=p=>
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
               let '(index, ibn') := index_ibn' in
                indrep_n_helper bxp # (ibn') l' NIndirect)
              (enumerate l) l_part.
  Proof.
    intros.
    rewrite listmatch_piff_replace.
    apply piff_refl.
    intros.
    destruct x.
    unfold indrep_n_helper.
    unfold enumerate in *.
    pose proof IndRec.Defs.items_per_val_not_0.
    assert (f n > 0). apply H.
    match goal with [H : In (_, _) (combine (seq _ _) _) |- _] =>
      eapply in_combine_l in H; apply in_seq in H; omega
    end.
    repeat destruct addr_eq_dec; auto; omega.
  Qed.

  Theorem listmatch_indrep_n_helper_invalid : forall bxp a n l l_part f,
    (forall x, x >= a -> f x = 0) ->
    n = length l ->
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
               let '(index, ibn') := index_ibn' in
                indrep_n_helper bxp # (ibn') l' (f index))
              (combine (seq a n) l) l_part <=p=>
              [[ Forall (fun x => length x = NIndirect) l_part ]] * [[ length l = length l_part]].
  Proof.
    intros.
    rewrite listmatch_lift_r.
    unfold listmatch.
    rewrite listpred_emp.
    subst; rewrite combine_length, seq_length, Nat.min_id.
    split. cancel; eauto.
    cancel.
    intros x; destruct x; intros.
    instantiate (1 := fun _ _ => emp); auto.
    intros x; destruct x; intros.
    unfold indrep_n_helper.
    rewrite H; simpl.
    split; cancel.
    eapply in_seq, in_combine_l. eauto.
  Qed.

  Theorem listmatch_indrep_n_helper_length_piff : forall bxp iblocks l_part f,
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
            let '(index, ibn') := index_ibn' in
             indrep_n_helper bxp # (ibn') l' (f index)) iblocks l_part <=p=>
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
            let '(index, ibn') := index_ibn' in
             indrep_n_helper bxp # (ibn') l' (f index)) iblocks l_part *
             [[ Forall (fun x : list waddr => length x = NIndirect) l_part ]].
  Proof.
    intros.
    rewrite listmatch_lift_r.
    2 : intros x; destruct x; intros.
    2 : rewrite indrep_n_helper_length_piff.
    2 : instantiate (2 := fun x => length x = NIndirect).
    2 : instantiate (1 := fun n_w y => indrep_n_helper bxp (# (snd n_w)) y (f (fst n_w))).
    2 : simpl; split; cancel.
    split; cancel.
  Qed.

  Theorem listmatch_indrep_n_tree_aligned : forall indlvl bxp n n1 l1 l2,
    n <= length l1 ->
    n = n1 - 1 ->
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
      let '(index, ibn') := index_ibn' in
        indrep_n_tree indlvl bxp # (ibn') l'
          (n1 * (NIndirect ^ S indlvl) - index * (NIndirect ^ S indlvl)))
      (removeN (enumerate l1) n) (removeN l2 n) <=p=>
    listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
      let '(index, ibn') := index_ibn' in
        indrep_n_tree indlvl bxp # (ibn') l'
          (n * (NIndirect ^ S indlvl) - index * (NIndirect ^ S indlvl)))
      (removeN (enumerate l1) n) (removeN l2 n).
  Proof.
    intros.
    rewrite listmatch_piff_replace. eauto.
    unfold removeN; autorewrite with lists.
    unfold enumerate. rewrite skipn_combine by (rewrite seq_length; auto).
    autorewrite with lists; simpl plus.
    rewrite <- combine_app by (rewrite seq_length; auto).
    rewrite firstn_length_l by omega.
    intros x; destruct x; intros.
    match goal with [H : In _ (combine _ _) |- _] =>
      apply in_combine_l in H; rewrite in_app_iff in H; repeat rewrite in_seq in H
    end.
    repeat rewrite <- Nat.mul_sub_distr_r.
    intuition.
    repeat rewrite indrep_n_tree_nvalid_oob with (nvalid := (_ - _) * _);
    solve [eauto |
      rewrite mult_comm; apply mult_ge_l; omega].
    repeat replace (_ - _) with 0 by omega.
    eauto.
  Qed.

  Theorem indrep_n_helper_pts_piff : forall bxp ir l nvalid,
    nvalid > 0 ->
    indrep_n_helper bxp ir l nvalid <=p=> [[ BALLOC.bn_valid bxp ir ]] * [[ IndRec.items_valid ir l]] *
    (ir |-> (IndRec.Defs.block2val l, [])).
  Proof.
    intros.
    rewrite nvalid_gt_0_indrep_helper by omega.
    unfold IndRec.Defs.item, IndRec.rep, IndSig.RAStart in *; split; cancel.
    all : unfold IndRec.items_valid, IndRec.Defs.item in *; intuition; simpl in *.
    all : rewrite IndRec.Defs.ipack_one by (simpl; omega); cancel.
  Qed.


  (************* n-indirect program *)

  Fixpoint indget (indlvl : nat) lxp (bn : addr) off ms :=
    let divisor := NIndirect ^ indlvl in
    let^ (ms, v) <- IndRec.get lxp bn (off / divisor) ms;
    match indlvl with
    | 0 => Ret ^(ms, v)
    | S indlvl' => indget indlvl' lxp (# (Rec.to_word v)) (off mod divisor) ms
    end.

  Lemma divup_gt_0 : forall a b, 0 < a -> 0 < b -> divup a b > 0.
  Proof.
    intros.
    apply Nat.div_str_pos; omega.
  Qed.

  Local Hint Resolve divup_gt_0.

  Ltac indrep_n_tree_bound := match goal with
  | [ |- ?off / ?N < length ?l] => (eapply indget_length_helper_l || eapply indget_length_helper_r);
    solve [match goal with [H : _ |- _] => apply H end]
  end.

  Theorem indget_ok : forall indlvl lxp bxp bn off ms,
    {< F Fm m0 m l nvalid,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp bn l nvalid ]]] *
           [[ off < nvalid ]] * [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} indget indlvl lxp bn off ms.
  Proof.
    induction indlvl; simpl.
    + repeat safestep; autorewrite with core; eauto.
      unfold indrep_n_helper.
      destruct addr_eq_dec; cancel; omega.
    + repeat safestep; autorewrite with core; try eassumption.
      - indrep_n_tree_bound.
      - rewrite nvalid_gt_0_indrep_helper by (apply divup_gt_0; (omega || mult_nonzero)).
        cancel.
      - unfold Rec.to_word; simpl.
        rewrite listmatch_isolate, selN_enumerate.
        (* these are hidden by notation, but otherwise prevent cancel from succeeding *)
        unfold IndRec.Defs.item; simpl; erewrite snd_pair by eauto.
        cancel.
        all : try rewrite length_enumerate.
        all : indrep_n_tree_bound.
      - rewrite <- Nat.lt_add_lt_sub_r by auto.
        eapply le_lt_trans; try eassumption.
        rewrite plus_comm, mult_comm.
        rewrite <- Nat.div_mod; auto.
      - match goal with [H : context [indrep_n_helper] |-_] => assert (HH := H) end.
        rewrite listmatch_extract, selN_enumerate in HH.
        rewrite indrep_n_length_pimpl in HH.
        destruct_lift HH.
        match goal with [H : _ |-_ ] => rewrite H end.
        apply Nat.mod_bound_pos; try solve [omega | mult_nonzero].
        all : try rewrite length_enumerate; solve [indrep_n_tree_bound].
      - apply selN_selN_hom.
        rewrite listmatch_lift_r in *.
        destruct_lifts; eauto.
        intros x y; destruct x; simpl.
        rewrite indrep_n_length_pimpl.
        rewrite indrep_n_tree_listmatch_lift_helper; split; cancel.
        rewrite mult_comm.
        apply div_lt_mul_lt; solve [indrep_n_tree_bound | mult_nonzero].
      Unshelve.
      all : try split; eauto.
      exact IndRec.Defs.item0.
  Qed.

  Fixpoint indread (indlvl : nat) lxp (ir : addr) nvalid ms :=
    let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
    match indlvl with
      | 0 => Ret ^(ms, indbns)
      | S indlvl' =>
        let N := (NIndirect ^ (S indlvl')) in
        r <- ForN i < divup nvalid N
          Hashmap hm
          Ghost [ F Fm iblocks l_part l bxp crash m0 m ]
          Loopvar [ ms r ]
          Invariant
            LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
            [[[ m ::: Fm * indrep_n_helper bxp ir iblocks (divup nvalid N) *
                      listmatch (fun index_ibn' l' =>
                        let '(index, ibn') := index_ibn' in
                          indrep_n_tree indlvl' bxp (# ibn') l' (nvalid - index * N))
                        (enumerate iblocks) l_part ]]] *
            [[ r = firstn (min (i * (NIndirect ^ indlvl)) (roundup nvalid NIndirect)) l ]]
          OnCrash crash
          Begin
            let nvalid' := (min (NIndirect ^ indlvl) (nvalid - i * NIndirect ^ indlvl)) in
            let^ (ms, v) <- indread indlvl' lxp #(selN indbns i IndRec.Defs.item0) nvalid' ms;
            Ret ^(ms, r ++ v)
          Rof ^(ms, nil);
          Ret r
    end.

  Theorem indread_ok : forall indlvl lxp bxp ir nvalid ms,
  {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp ir l nvalid ]]] *
           [[ nvalid <= length l ]] * [[ 0 < nvalid ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = firstn (roundup nvalid NIndirect) l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} indread indlvl lxp ir nvalid ms.
  Proof.
    induction indlvl; simpl.
    + hoare.
      - rewrite nvalid_gt_0_indrep_helper by auto; cancel.
      - rewrite indrep_n_helper_length_piff in *.
        match goal with [H : context [length _ = _] |- _ ] => destruct_lift H end.
        unfold IndRec.Defs.item in *; simpl in *.
        repeat rewrite firstn_oob; auto; try omega.
        substl NIndirect.
        apply roundup_ge_divisor; auto.
    + hoare.
      - rewrite nvalid_gt_0_indrep_helper by (apply divup_gt_0; (omega || mult_nonzero)); cancel.
      - rewrite indrep_n_helper_length_piff in H9.
        rewrite listmatch_length_pimpl in *; autorewrite with lists in *.
        destruct_lifts.
        unfold IndRec.Defs.item in *; simpl in *.
        rewrite firstn_oob by omega.
        assert (nvalid <= NIndirect ^ (S (S indlvl))) by (eapply le_trans; eauto;
          eapply Nat.eq_le_incl, indrep_n_tree_length; eauto); simpl in *.
        rewrite listmatch_isolate with (i := m1);
        autorewrite with lists; try (eapply divup_bound_helper; eauto; omega).
        (* this is hidden by notation, but otherwise prevents cancel from succeeding *)
        erewrite snd_pair by eauto; simpl.
        edestruct Min.min_spec as [ [HH Hmin]|[HH Hmin] ]; rewrite Hmin; cancel.
        rewrite indrep_n_tree_nvalid_oob; simpl; solve [cancel | omega].
      - match goal with [H : context[indrep_n_helper] |- _] =>
          eapply indrep_n_indlist_forall_length in H; eapply Forall_selN in H; try rewrite H
        end.
        apply Nat.le_min_l.
        rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in *; destruct_lifts.
        autorewrite with lists in *.
        eapply divup_bound_helper; [> eauto | |].
        eapply le_trans; eauto; eapply Nat.eq_le_incl, indrep_n_tree_length; eauto.
        unfold IndRec.Defs.item in *; simpl in *; congruence.
      - edestruct Min.min_spec as [ [HH Hmin]|[HH Hmin] ]; rewrite Hmin; [> mult_nonzero |].
        rewrite <- Nat.lt_add_lt_sub_r; simpl.
        apply divup_gt; auto; mult_nonzero.
      - rewrite min_roundup, roundup_mult.
        unfold IndRec.Defs.item in *; simpl in *.
        match goal with [H : context[indrep_n_helper] |- _] =>
          rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in H
        end; destruct_lifts; autorewrite with lists in *.
        edestruct Min.min_spec as [ [HH Hmin]|[HH Hmin] ]; rewrite Hmin in *; clear Hmin.
        erewrite le_plus_minus with (m := roundup nvalid NIndirect); [> | apply Nat.lt_le_incl; eauto].
        rewrite plus_comm, Min.plus_min_distr_l, firstn_sum_split.
        f_equal.
        rewrite roundup_subt_divide at 1 by solve [divide_mult | omega].
        assert (nvalid <= NIndirect ^ (S (S indlvl))) by (eapply le_trans; eauto;
          eapply Nat.eq_le_incl, indrep_n_tree_length; eauto); simpl in *.
        edestruct Min.min_spec as [ [HH' Hmin]|[HH' Hmin] ]; rewrite Hmin in *; clear Hmin.
        erewrite concat_hom_subselect_firstn; eauto.
        rewrite concat_hom_skipn; eauto.
        unfold IndRec.Defs.item in *; simpl in *.
        eapply divup_bound_helper; eauto; omega.
        rewrite concat_hom_skipn; eauto.
        erewrite concat_hom_subselect_firstn; eauto.
        unfold IndRec.Defs.item in *; simpl in *.
        eapply divup_bound_helper; eauto; omega.
        pose proof roundup_ge nvalid NIndirect IndRec.Defs.items_per_val_gt_0.
        replace (nvalid - _ * _) with 0 by omega.
        rewrite roundup_0, min_r, app_nil_r.
        rewrite min_r by lia. auto.
        apply Nat.lt_le_incl; mult_nonzero.
      - rewrite min_r; auto.
        apply roundup_mult_mono; solve [mult_nonzero | divide_mult].
      - apply LOG.rep_hashmap_subset; eauto.
    Unshelve. all : eauto; split; solve [eauto | exact ($0)].
  Qed.

  Fixpoint indshrink_aligned indlvl lxp bxp (ir : addr) nvalid nr ms :=
    let nvalid_children := nvalid / (NIndirect ^ indlvl) in
    let nr_children := nr / (NIndirect ^ indlvl) in
    match indlvl with
    | 0 => ms <- BALLOC.free lxp bxp ir ms;
           Ret ^(ms)
    | S indlvl' =>
        let N := (NIndirect ^ S indlvl') in
        let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
        let^ (ms) <- ForN i < nr_children - 1
          Hashmap hm
          Ghost [ F Fm bxp crash m0 freelist l_part iblocks ]
          Loopvar [ ms ]
          Invariant
            exists freelist' m, LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
            let bn := selN indbns (nvalid_children - 1 - i) $0 in
            [[[ m ::: Fm *
                      indrep_n_helper bxp ir iblocks nvalid_children *
                      listmatch (fun index_ibn' l' => let '(index, ibn') := index_ibn' in
                          indrep_n_tree indlvl' bxp (# ibn') l' ((nvalid_children - i) * N - index * N))
                        (enumerate iblocks) l_part *
              BALLOC.rep bxp freelist' ]]] * [[ incl freelist freelist' ]]
          OnCrash crash
          Begin
            let bn := selN indbns (nvalid_children - 1 - i) $0 in
            let^ (ms) <- indshrink_aligned indlvl' lxp bxp #bn N N ms;
            Ret ^(ms)
          Rof ^(ms);
          let bn := selN indbns (nvalid_children - nr_children) $0 in
          let^ (ms) <- indshrink_aligned indlvl' lxp bxp #bn N N ms;
        If (addr_eq_dec nr_children nvalid_children) {
          ms <- BALLOC.free lxp bxp ir ms;
          Ret ^(ms)
        } else {
          Ret ^(ms)
        }
      end.

  Theorem indshrink_aligned_ok : forall indlvl lxp bxp ir nvalid nr l ms,
    let N := NIndirect ^ indlvl in
    {< F Fm m0 m freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ (indlvl = 0 /\ nvalid = nr) \/ (indlvl > 0 /\ Nat.divide N nvalid /\ Nat.divide N nr) ]] *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp ir l nvalid * BALLOC.rep bxp freelist) ]]] *
           [[ nvalid <= length l ]] * [[0 < nr <= nvalid ]]
    POST:hm' RET:^(ms)  exists m' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp ir l (nvalid - nr) * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indshrink_aligned indlvl lxp bxp ir nvalid nr ms.
    Proof.
      induction indlvl.
      + simpl; hoare.
        rewrite nvalid_gt_0_indrep_helper in * by omega.
        destruct_lifts; auto.
        rewrite Nat.sub_diag, indrep_n_helper_0.
        rewrite indrep_n_helper_length_piff.
        rewrite indrep_n_helper_pts_piff by omega.
        cancel.
      + simpl.
        safestep.
        rewrite nvalid_gt_0_indrep_helper. cancel.
        unfold Nat.divide in *.
        repeat match goal with [H : exists _, _ |- _] => destruct H end; subst.
         match goal with [H : 0 < ?z * _, H1 : ?z * _ <= ?z0 * _ |- _] =>
          destruct (addr_eq_dec z 0); [> subst; simpl in *; omega |];
          destruct (addr_eq_dec z0 0); [> subst; simpl in *; omega |]
        end. rewrite <- Nat.mul_le_mono_pos_r in * by mult_nonzero.
        rewrite divup_mul; mult_nonzero; omega.
        erewrite indrep_n_tree_length in *.
        simpl in *.
        unfold Nat.divide in *.
        repeat match goal with [H : exists _, _ |- _] => destruct H end; subst.
         match goal with [H : 0 < ?z * _, H1 : ?z * _ <= ?z0 * _ |- _] =>
          destruct (addr_eq_dec z 0); [> subst; simpl in *; omega |];
          destruct (addr_eq_dec z0 0); [> subst; simpl in *; omega |]
        end. rewrite <- Nat.mul_le_mono_pos_r in * by mult_nonzero.
        rewrite divup_mul in * by auto.
        repeat rewrite Nat.div_mul by mult_nonzero.
        rewrite nvalid_gt_0_indrep_helper, IndRec.items_length_ok_pimpl in * by omega.
        rewrite listmatch_length_pimpl in *; autorewrite with lists in *.
        unfold IndRec.Defs.item in *; simpl in *.
        destruct_lifts.
        safestep.
        rewrite Nat.sub_0_r, nvalid_gt_0_indrep_helper by omega.
        repeat cancel.
        apply incl_refl.
        auto.
        rewrite firstn_oob by omega.
        monad_simpl; simpl.
        safestep.
        destruct indlvl; intuition.
        right; intuition; eauto.
        match goal with [ |- context[indrep_n_tree _ _ (# (selN _ ?n _))] ] =>
          rewrite listmatch_extract with (i := n); autorewrite with lists
        end; try omega.
        rewrite <- Nat.mul_sub_distr_r.
        replace (_ - _ - (_ - _ - _)) with 1 by omega. rewrite mult_1_l.
        erewrite snd_pair by eauto; cancel.
        apply Nat.eq_le_incl. symmetry.
        apply Forall_selN.
        eapply indrep_n_indlist_forall_length.
        match goal with [H : _ |- _] => eapply pimpl_apply; [> | exact H]; cancel end.
        rewrite sep_star_comm, <- sep_star_assoc.
        apply pimpl_refl.
        omega.
        mult_nonzero.
        safestep.
        rewrite listmatch_isolate with (a := enumerate _); autorewrite with lists.
        erewrite snd_pair by eauto.
        repeat rewrite Nat.sub_diag.
        rewrite <- Nat.sub_add_distr; simpl plus; cancel.
        erewrite listmatch_indrep_n_tree_aligned; auto; omega.
        all : try omega.
        eapply incl_tran; eauto.
        cancel.
        rewrite firstn_oob by omega.
        step.
        destruct indlvl; intuition.
        right; intuition; eauto.
        match goal with [ |- context[indrep_n_tree _ _ (# (selN _ ?n _))] ] =>
          rewrite listmatch_extract with (i := n); autorewrite with lists
        end; try omega.
        erewrite snd_pair by eauto.
        rewrite <- Nat.mul_sub_distr_r.
        replace (_ - _ - _) with 1 by omega; rewrite mult_1_l.
        cancel.
        apply Nat.eq_le_incl. symmetry.
        apply Forall_selN.
        eapply indrep_n_indlist_forall_length.
        match goal with [H : _ |- _] => eapply pimpl_apply; [> | exact H]; cancel end.
        rewrite sep_star_comm, <- sep_star_assoc.
        apply pimpl_refl.
        omega.
        mult_nonzero.
        hoare.
        repeat rewrite Nat.sub_diag.
        match goal with [|- context [indrep_n_tree _ _ (# (selN ?l _ _))] ] =>
          rewrite listmatch_isolate with (a := enumerate l) (i := 0)
        end; autorewrite with lists; try omega.
        simpl.
        repeat erewrite snd_pair by eauto.
        rewrite listmatch_indrep_n_tree_aligned by omega.
        rewrite divup_0, indrep_n_helper_0, indrep_n_helper_pts_piff by omega.
        cancel.
        unfold IndRec.Defs.item in *; simpl in *; omega.
        apply incl_tl. eapply incl_tran; eauto.
        match goal with [|- context [indrep_n_tree _ _ (# (selN ?l ?n _))] ] =>
          rewrite listmatch_isolate with (a := enumerate l) (i := n)
        end; autorewrite with lists; try omega.
        repeat rewrite Nat.sub_diag; simpl.
        rewrite <- Nat.mul_sub_distr_r, divup_mul by mult_nonzero.
        repeat rewrite Nat.sub_diag; simpl.
        repeat rewrite nvalid_gt_0_indrep_helper by omega.
        repeat erewrite snd_pair by eauto. cancel.
        rewrite listmatch_indrep_n_tree_aligned by omega.
        auto.
        eapply incl_tran; eauto.
        cancel. apply LOG.intact_hashmap_subset; auto.
        match goal with [H : _ |- _] => eapply pimpl_apply; [> | exact H]; cancel end.
        rewrite sep_star_comm, <- sep_star_assoc.
        apply pimpl_refl.
        cancel. apply LOG.active_intact.
        Grab Existential Variables.
        all : eauto; try split; eauto; solve [exact $0 | exact nil].
  Qed.

  Hint Extern 1 ({{_}} Bind (indshrink_aligned _ _ _ _ _ _ _) _) => apply indshrink_aligned_ok : prog.

  Fixpoint indshrink_ragged_to_aligned indlvl lxp bxp ir nvalid ms :=
    match indlvl with
    | 0 =>
      ms <- BALLOC.free lxp bxp ir ms;
      Ret ^(ms)
    | S indlvl' =>
      let N := (NIndirect ^ S indlvl') in
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      let ragged_bn := selN indbns (nvalid / N) $0 in
      let N' := (NIndirect ^ indlvl') in

      If (addr_eq_dec (nvalid mod N') 0) {
        If (addr_eq_dec (nvalid mod N) 0) {
          Ret ^(ms)
        } else {
          let^ (ms) <- indshrink_aligned indlvl' lxp bxp (# ragged_bn) (nvalid mod N) (nvalid mod N) ms;
          If (addr_eq_dec (nvalid / N) 0) {
            ms <- BALLOC.free lxp bxp ir ms;
            Ret ^(ms)
          } else {
            Ret ^(ms)
          }
        }
      } else {
        let^ (ms) <- indshrink_ragged_to_aligned indlvl' lxp bxp #ragged_bn (nvalid mod N) ms;
        let nvalid' := ((nvalid mod N) / N' * N') in
        If (addr_eq_dec nvalid' 0) {
          ms <- BALLOC.free lxp bxp ir ms;
          Ret ^(ms)
        } else {
          let^ (ms) <- indshrink_aligned indlvl' lxp bxp (# ragged_bn) nvalid' nvalid' ms;
          Ret ^(ms)
        }
      }
    end.

  Theorem indshrink_ragged_to_aliged_ok : forall indlvl lxp bxp ir nvalid l ms,
    let N := NIndirect ^ (max 1 indlvl) in
    {< F Fm m0 m freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp ir l nvalid * BALLOC.rep bxp freelist) ]]] *
           [[ nvalid mod N > 0 ]] * [[ nvalid < length l ]]
    POST:hm' RET:^(ms)  exists m' freelist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp ir l (nvalid / N * N) * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indshrink_ragged_to_aligned indlvl lxp bxp ir nvalid ms.
    Proof.
      induction indlvl; simpl.
      + rewrite mult_1_r.
        hoare; assert (nvalid > 0) by (eapply lt_le_trans; eauto; apply Nat.mod_le; auto).
        - rewrite nvalid_gt_0_indrep_helper in * by omega; destruct_lifts; auto.
        - rewrite indrep_n_helper_length_piff in *; destruct_lifts.
          rewrite Nat.div_small by omega; simpl.
          rewrite indrep_n_helper_0, indrep_n_helper_pts_piff by omega. cancel.
      + step; assert (nvalid > 0) by (destruct (addr_eq_dec nvalid 0); subst;
          [> rewrite Nat.mod_0_l in * by auto |]; omega).
          rewrite nvalid_gt_0_indrep_helper. cancel.
          apply divup_gt_0; mult_nonzero.
          assert ((divup nvalid (NIndirect * NIndirect ^ indlvl)) > 0) by (apply divup_gt_0; mult_nonzero).
          rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in *.
          destruct_lifts; autorewrite with lists in *.
          step.
          step.
          step.
          rewrite firstn_oob by omega.
          step.
          destruct indlvl; intuition.
          Fact mod_mul_0 : forall a b c, a mod b = 0 -> (a mod (c * b)) mod b = 0.
          Proof.
            intros.
            destruct (addr_eq_dec b 0); subst; auto.
            destruct (addr_eq_dec c 0); subst; simpl. apply Nat.mod_0_l; auto.
            rewrite Nat.mod_divides in * by auto.
            destruct H; eexists. subst.
            rewrite mult_comm.
            rewrite Nat.mul_mod_distr_r by auto.
            rewrite mult_comm. auto.
          Qed.
          right; intuition;
          apply Nat.mod_divide, mod_mul_0; mult_nonzero.
          rewrite listmatch_extract; autorewrite with lists.
          Fact sub_round_eq_mod : forall a b, b <> 0 -> a - a / b * b = a mod b.
          Proof.
            intros.
            rewrite Nat.mod_eq, mult_comm; auto.
          Qed.
          rewrite sub_round_eq_mod by auto.
          erewrite snd_pair by eauto. cancel.
          eapply indget_length_helper_l; eauto.
          eapply pimpl_apply; [> | exact H4]; cancel.
          rewrite sep_star_comm, <- sep_star_assoc.
          apply pimpl_refl.
          eapply indget_length_helper_l; eauto.
          eapply pimpl_apply; [> | exact H4]; cancel.
          rewrite sep_star_comm, <- sep_star_assoc.
          apply pimpl_refl.
          apply Nat.lt_le_incl.
          eapply lt_le_trans; [> apply Nat.mod_upper_bound |]; mult_nonzero.
          apply Nat.eq_le_incl. symmetry.
          apply Forall_selN.
          eapply indrep_n_indlist_forall_length.
          match goal with [H : _ |- _] => eapply pimpl_apply; [> | exact H]; cancel end.
          rewrite sep_star_comm, <- sep_star_assoc.
          apply pimpl_refl.
          eapply indget_length_helper_r; eauto.
          eapply pimpl_apply; [> | exact H4]; cancel.
          rewrite sep_star_comm, <- sep_star_assoc.
          apply pimpl_refl.
          repeat rewrite Nat.sub_diag.
          repeat step.
          rewrite nvalid_gt_0_indrep_helper in * by omega.
          destruct_lifts; auto.
          match goal with [H : _ = 0 |- _] => rewrite H in * end.
          rewrite divup_mul by mult_nonzero.
          repeat rewrite indrep_n_helper_0.
          rewrite indrep_n_helper_length_piff.
          rewrite indrep_n_helper_pts_piff by auto.
          simpl.
          cancel; eauto.
          Theorem indrep_n_tree_0 : forall indlvl bxp ir l,
            indrep_n_tree indlvl bxp ir l 0 <=p=> [[length l = NIndirect ^ S indlvl]].
          Proof.
            induction indlvl; simpl; intros.
            rewrite mult_1_r, indrep_n_helper_0; split; cancel.
            rewrite divup_0. split.
            intros m' H'.
            destruct_lift H'.
            rewrite indrep_n_helper_0 in H.
            rewrite listmatch_length_pimpl in H; autorewrite with lists in *.
            rewrite listmatch_lift_r with (F := fun x y => emp) in H.
            rewrite listmatch_emp in H by auto.
            pred_apply; cancel.
            erewrite concat_hom_length; eauto.
            f_equal. omega.
            intros; simpl.
            destruct x.
            rewrite IHindlvl. split; cancel.
            cancel.
            instantiate (iblocks := repeat $0 NIndirect).
            rewrite indrep_n_helper_0. rewrite repeat_length.
            rewrite listmatch_lift_r with (F := fun x y => emp) (P := fun y => length y = NIndirect ^ S indlvl).
            rewrite listmatch_emp_piff by auto.
            autorewrite with lists.
            cancel.
            Definition group {T} (l : list T) (k : nat) :=
              map (fun i => firstn k (skipn (i * k) l)) (seq 0 (length l / k)).
            Lemma group_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
              length (group l k) = length l / k.
            Proof.
              intros.
              unfold Nat.divide in *. destruct H.
              unfold group.
              rewrite H, Nat.div_mul by auto.
              rewrite map_length, seq_length; auto.
            Qed.
            Lemma group_forall_length : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
              Forall (fun x => length x = k) (group l k).
            Proof.
              intros.
              destruct H. unfold group; rewrite H.
              rewrite Nat.div_mul by auto.
              apply Forall_map, Forall_forall.
              intros x0 HH.
              apply in_seq in HH.
              apply firstn_length_l.
              rewrite skipn_length, H.
              rewrite <- Nat.mul_sub_distr_r, mult_comm.
              apply mult_ge_l; omega.
            Qed.
            apply group_forall_length; try substl (length l); solve [mult_nonzero | divide_mult].
            rewrite group_length; try substl (length l); try rewrite Nat.div_mul;
              solve [auto | mult_nonzero | divide_mult].
            Lemma concat_hom_group : forall T (l : list T) k, Nat.divide k (length l) -> k <> 0 ->
              concat (group l k) = l.
            Proof.
              intros.
              unfold group.
              destruct H.
              remember (length l) as n.
              generalize dependent n.
              generalize dependent l.
              generalize dependent k.
              induction x; intros.
              simpl in *; rewrite H in *.
              rewrite Nat.div_0_l by auto.
              simpl.
              symmetry; apply length_nil. auto.
              rewrite H; simpl.
              rewrite Nat.div_add, Nat.div_same by auto.
              simpl in *.
              rewrite <- seq_shift, map_map.
              simpl in *.
              rewrite <- firstn_skipn with (l := l) at 2.
              f_equal.
              rewrite <- IHx with (k := k) (n := x * k); auto.
              rewrite Nat.div_mul by auto.
              f_equal. apply map_ext.
              intros.
              f_equal.
              rewrite skipn_skipn'; auto.
              rewrite skipn_length.
              assert (x * k >= 0) by intuition.
              omega.
            Qed.
            intro x; destruct x; intros.
            rewrite IHindlvl. split; cancel.
            rewrite concat_hom_group; auto; mult_nonzero.
            unfold Nat.divide. eauto.
          Qed.
          unfold IndRec.Defs.item in *; simpl in *.
          assert (NIndirect > 0) by auto.
          rewrite listmatch_isolate with (a := enumerate _) (i := 0);
            autorewrite with lists; try omega.
          rewrite listmatch_piff_replace. erewrite snd_pair by eauto. cancel.
          intro x; destruct x; intros.
          unfold enumerate in *.
          rewrite removeN_combine in *.
          match goal with [H : In _ (combine _ _) |- _] =>
            apply in_combine_l in H; unfold removeN in H; rewrite skipn_seq in H;
            simpl in H; apply in_seq in H
          end.
          rewrite Nat.div_small_iff in * by mult_nonzero.
          replace (_ - _) with 0; auto.
          symmetry; apply Nat.sub_0_le.
          apply Nat.lt_le_incl.
          eapply lt_le_trans; eauto.
          rewrite mult_comm with (n := n).
          apply mult_ge_l; omega.
          rewrite divup_mul by mult_nonzero.
          repeat rewrite nvalid_gt_0_indrep_helper by omega.
          cancel.
          unfold IndRec.Defs.item in *; simpl in *.
          assert (NIndirect > 0) by auto.
          assert (nvalid / (NIndirect * NIndirect ^ indlvl) < NIndirect).
          Search length concat.
          Search nvalid length.
          Search (?a / ?b < ?c).
          apply Nat.div_lt_upper_bound; mult_nonzero.
          rewrite mult_comm.
          erewrite indrep_n_tree_length in H5.
          eauto.
          match goal with [H : context [listmatch _ (enumerate _)] |- _]
            => eapply pimpl_apply; [> | exact H]; cancel
          end. rewrite sep_star_comm, <- sep_star_assoc. apply pimpl_refl.
          match goal with [|- context [indrep_n_tree _ _ (# (selN ?l ?n _))] ] =>
            rewrite listmatch_isolate with (a := enumerate l) (i := n)
          end; autorewrite with lists; try omega.
          repeat rewrite Nat.sub_diag.
          cancel.
          erewrite snd_pair by eauto.
          cancel.
          Theorem listmatch_indrep_n_tree_to_aligned : forall indlvl bxp iblocks l_part nvalid,
            let N := (NIndirect * NIndirect ^ indlvl) in
            nvalid < NIndirect * N ->
            length iblocks = NIndirect ->
            listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
                      let '(index, ibn') := index_ibn' in
                      indrep_n_tree indlvl bxp # (ibn') l' (nvalid - index * N))
                        (removeN (enumerate iblocks) (nvalid / N))
                        (removeN l_part (nvalid / N)) =p=>
            listmatch (fun (index_ibn' : addr * waddr) (l' : list waddr) =>
                      let '(index, ibn') := index_ibn' in
                      indrep_n_tree indlvl bxp # (ibn') l' (nvalid / N * N - index * N))
                        (removeN (enumerate iblocks) (nvalid / N))
                        (removeN l_part (nvalid / N)).
          Proof.
            intros.
            rewrite listmatch_piff_replace. eauto.
            unfold removeN; autorewrite with lists.
            unfold enumerate. rewrite skipn_combine by (rewrite seq_length; auto).
            autorewrite with lists; simpl plus.
            rewrite <- combine_app by (rewrite seq_length; auto).
            Search (?a < ?b * ?c) Nat.div.
            rewrite mult_comm in H.
            apply Nat.div_lt_upper_bound in H; try solve [subst N; mult_nonzero].
            rewrite firstn_length_l by omega.
            intros x; destruct x; intros.
            match goal with [H : In _ (combine _ _) |- _] =>
              apply in_combine_l in H; rewrite in_app_iff in H; repeat rewrite in_seq in H
            end.
            repeat rewrite <- Nat.mul_sub_distr_r.
            intuition.
            rewrite Nat.mul_sub_distr_r.
            assert (nvalid / N * N - n * N >= N).
            rewrite <- Nat.mul_sub_distr_r.
            rewrite mult_comm.
            apply mult_ge_l; omega.
            pose proof div_mul_le nvalid N.
            repeat rewrite indrep_n_tree_nvalid_oob with (nvalid := _ - _);
            solve [eauto | subst N; simpl; omega].
            replace (nvalid / N - n) with 0 by omega.
            replace (_ - _) with 0.
            eauto.
            apply div_lt_mul_lt in H1; (subst N; mult_nonzero || omega).
          Qed.
          apply listmatch_indrep_n_tree_to_aligned; auto.
          apply div_lt_mul_lt; mult_nonzero.
          Admitted.

  Fixpoint indshrink (indlvl : nat) lxp bxp (ir : addr) nvalid nr (ms : LOG.mstate * Cache.cachestate) : prog (LOG.memstate * unit) :=
    match indlvl with
    | 0 =>  If (addr_eq_dec nr nvalid) {
              ms <- BALLOC.free lxp bxp ir ms;
              Ret ^(ms)
            } else {
              Ret ^(ms)
            }
    | S indlvl' =>
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      let divisor := (NIndirect ^ indlvl) in
      let nloops := divup nvalid divisor - (nvalid - nr) / divisor * divisor in
      (* iterate over indbns backwards so the invariant has a nice definition *)
      ms <- ForN i < nloops
        Hashmap hm
        Ghost [ F Fm l bxp crash m0 m freelist ]
        Loopvar [ ms ]
        Invariant
          exists freelist', LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[[ m ::: Fm *
            indrep_n_tree indlvl bxp ir l (nvalid - (min nr (i * NIndirect ^ indlvl))) *
            BALLOC.rep bxp freelist' ]]] * [[ incl freelist freelist' ]]
        OnCrash crash
        Begin
          let index := (NIndirect - i - 1) in
          let bn := #(selN indbns index ($ 0)) in
          let nvalid' := min (nvalid - i * NIndirect ^ indlvl') (i * NIndirect ^ indlvl) in
          let nr' := (min (NIndirect ^ indlvl) (nr - i * NIndirect ^ indlvl')) in
          ms <- indshrink indlvl' lxp bxp bn nvalid' nr' ms;
          If (addr_eq_dec nr' (NIndirect ^ indlvl)) {
            ms <- BALLOC.free lxp bxp bn (fst ms);
            Ret ^(ms)
          } else {
            Ret ms
          }
        Rof ^(ms);
        Ret ms
    end.

  Theorem indshrink_ok : forall indlvl lxp bxp ir nvalid nr ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp ir l nvalid * BALLOC.rep bxp freelist) ]]] *
           [[ nvalid <= NIndirect ^ S indlvl ]] * [[0 < nr <= nvalid ]]
    POST:hm' RET:^(ms)  exists m' freelist' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[ firstn (nvalid - nr) l' = firstn (nvalid - nr) l ]] *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp ir l' (nvalid - nr) * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indshrink indlvl lxp bxp ir nvalid nr ms.
    Proof.
      induction indlvl; simpl.
      + step; [> repeat safestep | hoare ].
        - rewrite nvalid_gt_0_indrep_helper in * by omega. destruct_lifts; auto.
        - rewrite nvalid_gt_0_indrep_helper by omega.
          rewrite IndRec.items_length_ok_pimpl; cancel.
          unfold IndRec.Defs.item in *; simpl in *.
          rewrite Nat.sub_diag, indrep_n_helper_0.
          unfold IndRec.rep, IndSig.RAStart; cancel.
          rewrite IndRec.Defs.ipack_one; simpl; solve [omega | cancel].
        - rewrite Nat.sub_diag. simpl; auto.
        - instantiate (l_part := [_]); simpl; rewrite app_nil_r.
          eauto.
        - simpl; rewrite app_nil_r; auto.
        - repeat rewrite nvalid_gt_0_indrep_helper by omega. cancel.
      + repeat safestep.
    Admitted.

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

