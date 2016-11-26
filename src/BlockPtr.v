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
Require Import Errno.

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
  Parameter IRDindPtr: irec -> addr.       (* doubly-indirect block pointer *)
  Parameter IRTindPtr: irec -> addr.       (* triply-indirect block pointer *)
  Parameter IRBlocks : irec -> list waddr. (* get direct block numbers *)
  Parameter IRAttrs  : irec -> iattr.      (* get untouched attributes *)

  (* setters *)
  Parameter upd_len  : irec -> addr -> irec.
  Parameter upd_irec : forall (r : irec) (len : addr) (ibptr : addr)
                                                      (dibptr : addr)
                                                      (tibptr : addr)
                                                      (dbns : list waddr), irec.

  (* setter equivalence *)
  Parameter upd_irec_eq_upd_len : forall ir len, goodSize addrlen len ->
    upd_len ir len = upd_irec ir len (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (IRBlocks ir).

  (* getter/setter lemmas *)
  Parameter upd_len_get_len    : forall ir n, goodSize addrlen n -> IRLen (upd_len ir n) = n.
  Parameter upd_len_get_ind    : forall ir n, IRIndPtr (upd_len ir n) = IRIndPtr ir.
  Parameter upd_len_get_dind   : forall ir n, IRDindPtr (upd_len ir n) = IRDindPtr ir.
  Parameter upd_len_get_tind   : forall ir n, IRTindPtr (upd_len ir n) = IRTindPtr ir.
  Parameter upd_len_get_blk    : forall ir n, IRBlocks (upd_len ir n) = IRBlocks ir.
  Parameter upd_len_get_iattr  : forall ir n, IRAttrs (upd_len ir n) = IRAttrs ir.

  Parameter upd_irec_get_len   : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen len -> IRLen (upd_irec ir len ibptr dibptr tibptr dbns) = len.
  Parameter upd_irec_get_ind   : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen ibptr -> IRIndPtr (upd_irec ir len ibptr dibptr tibptr dbns) = ibptr.
  Parameter upd_irec_get_dind  : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen dibptr -> IRDindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = dibptr.
  Parameter upd_irec_get_tind  : forall ir len ibptr dibptr tibptr dbns,
     goodSize addrlen tibptr -> IRTindPtr (upd_irec ir len ibptr dibptr tibptr dbns) = tibptr.
  Parameter upd_irec_get_blk   : forall ir len ibptr dibptr tibptr dbns,
     IRBlocks (upd_irec ir len ibptr dibptr tibptr dbns) = dbns.
  Parameter upd_irec_get_iattr : forall ir len ibptr dibptr tibptr dbns,
      IRAttrs (upd_irec ir len ibptr dibptr tibptr dbns) = IRAttrs ir.

  Parameter get_len_goodSize  : forall ir, goodSize addrlen (IRLen ir).
  Parameter get_ind_goodSize  : forall ir, goodSize addrlen (IRIndPtr ir).
  Parameter get_dind_goodSize : forall ir, goodSize addrlen (IRDindPtr ir).
  Parameter get_tind_goodSize : forall ir, goodSize addrlen (IRTindPtr ir).

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
  Notation "'NBlocks'"   := (NDirect + NIndirect + NIndirect ^ 2 + NIndirect ^ 3)%nat.

  (* Various bounds *)
  Lemma NIndirect_is : NIndirect = 512.
  Proof.
    unfold IndSig.items_per_val.
    rewrite valulen_is; compute; auto.
  Qed.

  Lemma NBlocks_roundtrip : # (natToWord addrlen NBlocks) = NBlocks.
  Proof.
    rewrite wordToNat_natToWord_idempotent. auto.
    repeat rewrite Nat2N.inj_add.
    simpl. repeat rewrite Nat2N.inj_mul. simpl.
    rewrite NIndirect_is.
    eapply N.le_lt_trans.
    repeat rewrite <- N.add_assoc.
    apply N.add_le_mono_r.
    unfold N.le.
    rewrite <- Nat2N.inj_compare.
    apply nat_compare_le.
    apply NDirect_bound.
    compute. reflexivity.
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

  (************** indirect blocks *)

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
                    exists iblocks, indrep_n_helper bxp ibn iblocks *
                    exists l_part, [[ l = concat l_part ]] *
                    listmatch (fun ibn' l' => indrep_n_tree indlvl' bxp (# ibn') l') iblocks l_part
    end)%pred.

  Hint Extern 0 (okToUnify (indrep_n_helper _ _ _) (indrep_n_helper _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (indrep_n_tree _ _ _ _) (indrep_n_tree _ _ _ _ )) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.

  (* Necessary to make subst work when there's a recursive term like:
     l = firstn (length l) ... *)
  Set Regular Subst Tactic.
  Local Hint Resolve IndRec.Defs.items_per_val_not_0.
  Local Hint Resolve IndRec.Defs.items_per_val_gt_0'.

  Lemma off_mod_len_l : forall T off (l : list T), length l = NIndirect -> off mod NIndirect < length l.
  Proof.
    intros. rewrite H; apply Nat.mod_upper_bound; auto.
  Qed.

  Fact divmod_n_zeros : forall n, fst (Nat.divmod n 0 0 0) = n.
  Proof.
    intros.
    pose proof Nat.div_1_r n.
    unfold Nat.div in H. auto.
  Qed.

  Hint Rewrite divmod_n_zeros using auto.
  Local Hint Resolve Nat.pow_nonzero off_mod_len_l mult_neq_0.
  Local Hint Resolve mul_ge_l mul_ge_r.

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

  Local Hint Resolve mod_le_r.
  Local Hint Resolve divup_gt_0.

  Ltac min_cases :=
    let H := fresh in let H' := fresh in
    edestruct Min.min_spec as [ [H H']|[H H'] ];
    rewrite H' in *; clear H'.

  Ltac mult_nonzero := 
    repeat (match goal with
    | [ |- mult _ _ <> 0 ] => apply mult_neq_0
    | [ |- mult _ _ > 0 ] => apply lt_mul_mono
    | [ |- _ ^ _ <> 0 ] => apply Nat.pow_nonzero
    | [ |- _ > 0 ] => unfold gt
    | [ |- 0 < _ ] => apply neq_0_lt
    | [ |- 0 <> _ ] => apply not_eq_sym
    | [ |- _] => solve [auto]
    | [ |- ?N <> 0 ] => subst N
    end).

  Ltac divide_solve := match goal with
    | [ |- Nat.divide 1 ?n ] => apply Nat.divide_1_l
    | [ |- Nat.divide ?n 0 ] => apply Nat.divide_0_r
    | [ |- Nat.divide ?a ?a ] => apply Nat.divide_refl
    | [ |- Nat.divide ?a (?b * ?c) ] => solve [apply Nat.divide_mul_l; divide_solve |
                                               apply Nat.divide_mul_r; divide_solve ]
    | [ |- Nat.divide ?a (?b + ?c) ] => apply Nat.divide_add_r; solve [divide_solve]
    | [ |- Nat.divide ?a (?b - ?c) ] => apply Nat.divide_sub_r; solve [divide_solve]
    | [ |- Nat.divide ?n (roundup _ ?n) ] => unfold roundup; solve [divide_solve]
    | [H : ?a mod ?b = 0 |- Nat.divide ?b ?a ] => apply Nat.mod_divide; mult_nonzero; solve [divide_solve]
  end.

  Local Hint Extern 1 (Nat.divide ?a ?b) => divide_solve.
  Local Hint Extern 0 (?a <= roundup ?a ?b) => apply roundup_ge; mult_nonzero.

  Ltac incl_solve := match goal with
    | [|- incl ?a ?a ] => apply incl_refl
    | [|- incl (remove _ _ ?l) ?l ] => apply incl_remove
    | [|- incl ?l (_ :: ?l)] => apply incl_tl; solve [incl_solve]
    | [H : incl ?a ?b |- incl ?a ?c ] => eapply incl_tran; [> apply H|]; solve [incl_solve]
    | [H : incl ?b ?c |- incl ?a ?c ] => eapply incl_tran; [> |apply H]; solve [incl_solve]
  end.

  Local Hint Extern 1 (incl ?a ?b) => incl_solve.

  Theorem indrep_n_helper_valid : forall bxp bn l,
    bn <> 0 -> indrep_n_helper bxp bn l <=p=> [[ BALLOC.bn_valid bxp bn ]] * IndRec.rep bn l.
  Proof.
    intros. unfold indrep_n_helper. destruct bn; try omega. simpl.
    split; cancel.
  Qed.

  Theorem indrep_n_tree_valid : forall indlvl bxp ir l,
    ir <> 0 -> indrep_n_tree indlvl bxp ir l <=p=> indrep_n_tree indlvl bxp ir l * [[ BALLOC.bn_valid bxp ir ]].
  Proof.
    destruct indlvl; intros; simpl.
    repeat rewrite indrep_n_helper_valid by auto. split; cancel.
    split; intros m' H'; destruct_lift H'; pred_apply; cancel.
    rewrite indrep_n_helper_valid in * by auto.
    destruct_lifts. auto.
  Qed.

  Lemma indrep_n_helper_0 : forall bxp l,
    indrep_n_helper bxp 0 l <=p=> [[ l = repeat $0 NIndirect ]] * emp.
  Proof.
    unfold indrep_n_helper; intros; split; cancel.
  Qed.

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

  Theorem indrep_n_helper_bxp_switch : forall bxp bxp' ir iblocks,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep_n_helper bxp ir iblocks <=p=> indrep_n_helper bxp' ir iblocks.
  Proof.
    intros. unfold indrep_n_helper, BALLOC.bn_valid. rewrite H. reflexivity.
  Qed.

  Theorem indrep_n_tree_bxp_switch : forall bxp bxp' indlvl ir l,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep_n_tree indlvl bxp ir l <=p=> indrep_n_tree indlvl bxp' ir l.
  Proof.
    induction indlvl; intros; simpl.
    apply indrep_n_helper_bxp_switch; auto.
    split; cancel; rewrite indrep_n_helper_bxp_switch.
    all : try rewrite listmatch_piff_replace; try cancel; auto.
    all : intros; simpl; rewrite IHindlvl; auto.
  Qed.

  Theorem listpred_indrep_n_tree_0 : forall indlvl bxp l,
    listpred (fun l' => indrep_n_tree indlvl bxp 0 l') l <=p=>
      [[ Forall (fun x => x = repeat $0 (NIndirect ^ S indlvl)) l ]].
  Proof.
    induction l; intros.
    - split; cancel. constructor.
    - simpl. rewrite IHl.
      rewrite indrep_n_tree_0.
      split; cancel.
      all : match goal with [H : Forall _ _ |- _] => inversion H; auto end.
  Qed.

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

  Lemma listmatch_indrep_n_tree_forall_length : forall indlvl bxp (l1 : list waddr) l2,
    listmatch (fun ibn' l' =>indrep_n_tree indlvl bxp # (ibn') l') l1 l2 <=p=>
    listmatch (fun ibn' l' =>indrep_n_tree indlvl bxp # (ibn') l') l1 l2 *
    [[Forall (fun sublist : list waddr => (length sublist = NIndirect * NIndirect ^ indlvl)%nat) l2]].
  Proof.
    intros.
    split; [> | cancel].
    rewrite listmatch_lift_r at 1. cancel. eauto.
    intros. rewrite indrep_n_length_pimpl. split; cancel.
  Qed.

  Local Hint Extern 1 (Forall (fun x => length x = _) _) => match goal with
    | [H : context [listmatch (fun x y => indrep_n_tree _ _ # x y) _ ?l]
        |- Forall (fun x => length x = _) ?l ] =>
          rewrite listmatch_indrep_n_tree_forall_length in H; destruct_lift H; solve [eassumption]
    | [|- Forall _ (upd_range ?l _ _ _)] => apply forall_upd_range; autorewrite with lists; eauto
  end.

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

  Lemma indrep_n_indlist_forall_length' : forall F F' indlvl bxp ir l1 l2 m,
    (((F ✶ indrep_n_helper bxp ir l1)
        ✶ listmatch
            (fun ibn' l' =>indrep_n_tree indlvl bxp # (ibn') l') l1 l2) * F')%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
  Proof.
    intros. eapply indrep_n_indlist_forall_length. eapply pimpl_apply; [> | exact H].
    cancel.
  Qed.

  Lemma indrep_index_bound_helper' : forall Fm Fm' off indlvl bxp bn iblocks l_part m,
    off < length (concat l_part) ->
    ((Fm * indrep_n_helper bxp bn iblocks) *
          listmatch (fun ibn' (l' : list waddr) =>
            indrep_n_tree indlvl bxp # (ibn') l') iblocks l_part *
            Fm')%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < NIndirect.
  Proof.
    intros.
    eapply indrep_index_bound_helper; eauto.
    match goal with [H : _ |- _] => eapply pimpl_apply; [> | exact H]; cancel end.
  Qed.

  Local Hint Resolve indrep_n_indlist_forall_length indrep_n_indlist_forall_length'.

  Lemma indrep_n_roundup_helper_1 : forall a b n, n <> 0 ->
    n - a mod n < b -> roundup a n - a <= b.
  Proof.
    intros.
    destruct (addr_eq_dec (a mod n) 0).
    unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero. omega.
    rewrite roundup_eq by mult_nonzero. rewrite minus_plus. omega.
  Qed.
  Local Hint Resolve indrep_n_roundup_helper_1.

  Theorem roundup_round : forall a n, roundup a n / n * n = roundup a n.
  Proof.
    intros.
    destruct (Nat.eq_dec n 0). subst. unfold roundup. auto.
    unfold roundup. rewrite Nat.div_mul by auto. auto.
  Qed.

  Theorem indclear_upd_range_helper_1 : forall T l l' l'' start (v : T) n k d,
    k <> 0 -> n <> 0 ->
    start mod (n * k) <> 0 ->
    start <= length (concat l) ->
    length l'' = n * k ->
    concat l' = upd_range l'' (start mod (n * k)) (roundup (start mod (n * k)) k - start mod (n * k)) v ->
    selN l (start / (n * k)) d = l'' ->
    Forall (fun x => length x = k) l' ->
    Forall (fun x => length x = n * k) l ->
    concat (updN l (start / (n * k)) (
      concat (upd_range l' (divup (start mod (n * k)) k) (n - divup (start mod (n * k)) k)
                (repeat v k)
    ))) = upd_range (concat l) start (n * k - start mod (n * k)) v.
  Proof.
    intros.
    erewrite concat_hom_length in * by eauto.
    erewrite upd_range_concat_hom_small.
    rewrite concat_hom_upd_range by eauto.
    substl (concat l'). f_equal. f_equal.
    substl l''.
    erewrite eq_trans with (x := divup _ _ * _); [> | reflexivity|].
    rewrite upd_range_upd_range; eauto. f_equal.
    rewrite Nat.mul_sub_distr_r.
    rewrite <- Nat.add_sub_swap. rewrite le_plus_minus_r. auto.
    all : eauto; autorewrite with core.
    all : ((apply roundup_le; auto) ||
           (apply roundup_ge; mult_nonzero) ||
           solve [mult_nonzero] ||
           unfold roundup; auto with *).
    - rewrite le_plus_minus_r. auto.
      apply roundup_ge; omega.
    - erewrite concat_hom_length by eauto.
      rewrite Nat.add_sub_assoc by auto. rewrite plus_comm.
      rewrite <- Nat.add_sub_assoc by (apply Nat.mod_le; mult_nonzero).
      rewrite sub_mod_eq_round by mult_nonzero.
      rewrite <- mult_1_l with (n := _ * _) at 1. rewrite <- Nat.mul_add_distr_r.
      apply mult_le_compat_r. simpl.
      apply Nat.div_lt_upper_bound; mult_nonzero.
      rewrite mult_comm. edestruct le_lt_eq_dec; eauto.
      subst. rewrite Nat.mod_mul in * by mult_nonzero. intuition.
    - rewrite le_plus_minus_r; auto.
    - apply Nat.lt_add_lt_sub_r. apply Nat.mod_upper_bound. auto.
  Qed.

  Theorem indrep_bound_helper_1 : forall a b n N,
    N <> 0 ->
    b <> 0 ->
    a + b <= n * N ->
    N - a mod N < b ->
    (a + (N - a mod N)) / N + (b - (N - a mod N)) / N <= n.
  Proof.
    intros.
    rewrite Nat.add_sub_assoc by auto.
    rewrite plus_comm with (n := a).
    rewrite <- Nat.add_sub_assoc by (apply Nat.mod_le; auto).
    rewrite sub_mod_eq_round by auto.
    rewrite <- mult_1_l with (n := N) at 1.
    repeat rewrite <- Nat.mul_add_distr_r.
    rewrite Nat.div_mul by auto.
    simpl. apply lt_le_S. eapply le_lt_trans.
    apply div_add_distr_le.
    eapply le_lt_trans. apply Nat.div_le_mono. auto.
    instantiate (1 := a + b - 1).
    assert (a mod N < N) by (apply Nat.mod_upper_bound; auto).
    omega.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm. omega.
  Qed.

  Theorem xform_indrep_n_helper : forall bxp ir l,
    crash_xform (indrep_n_helper bxp ir l) <=p=> indrep_n_helper bxp ir l.
  Proof.
    unfold indrep_n_helper. intros.
    destruct addr_eq_dec; xform_norm.
    - auto.
    - rewrite IndRec.xform_rep. auto.
  Qed.

  Theorem xform_indrep_n_tree : forall xp indlvl ir l,
    crash_xform (indrep_n_tree indlvl xp ir l) <=p=> indrep_n_tree indlvl xp ir l.
  Proof.
    induction indlvl; intros; simpl.
    + rewrite xform_indrep_n_helper. auto.
    + split; xform_norm.
      - rewrite xform_indrep_n_helper.
        rewrite xform_listmatch.
        rewrite listmatch_piff_replace. cancel.
        intros; simpl. eauto.
      - cancel. xform_normr.
        rewrite xform_indrep_n_helper. cancel.
        xform_normr.
        rewrite xform_listmatch.
        rewrite listmatch_piff_replace. cancel.
        intros. simpl. rewrite IHindlvl. auto.
  Qed.

  Ltac indrep_n_tree_bound := solve [
        eapply indrep_index_length_helper_l; eauto; omega  |
        eapply indrep_index_length_helper_l'; eauto; omega |
        eapply indrep_index_length_helper_r; eauto; omega  |
        eapply indrep_index_length_helper_r'; eauto; omega |
        eapply indrep_index_bound_helper; eauto; omega |
        eapply indrep_index_bound_helper'; eauto; omega].

  Ltac indrep_n_extract := match goal with
    | [|- context [listmatch _ ?l] ] =>
      match goal with [l : list _ |- context [listmatch _ (removeN ?l ?n)] ] =>
        rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try omega; try erewrite snd_pair by eauto
      end
    | [|- context [selN ?l ?n] ] => rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try omega; try erewrite snd_pair by eauto
  end.

  Ltac cancel_last := match goal with
    | [|- _ * ?a =p=> _ * ?a] =>  (apply pimpl_sep_star; [> solve [cancel] | apply pimpl_refl]) || fail 2
    | [|- (_ * _) * _ =p=> _ ] => rewrite sep_star_comm; (solve [cancel_last] || fail 2)
    | [|- _ * (_ * _) =p=> _ ] => repeat rewrite <- sep_star_assoc; (solve [cancel_last] || fail 2)
    end.

  Ltac indrep_n_tree_extract_lengths :=
    repeat match goal with [H : context [indrep_n_tree _ _ _ ?x] |- _] =>
      match goal with
      | [H' : length ?y = _ |- _] => tryif (unify x y) then fail 1 else fail
      | [|- _] => rewrite indrep_n_length_pimpl with (l := x) in H; destruct_lift H
      end
    end; try rewrite mult_1_r in *.

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

  Hint Extern 1 (BALLOC.bn_valid _ _) => match goal with
    [H : context [indrep_n_helper _ ?ir] |- BALLOC.bn_valid _ ?ir] =>
    rewrite indrep_n_helper_valid in H by omega; destruct_lift H; auto end.

  Local Hint Extern 1 (goodSize _ _) => match goal with
  | [|- goodSize _ ?a] =>
    destruct (addr_eq_dec a 0); [> substl a; apply DiskLogHash.PaddedLog.goodSize_0 |];
    rewrite indrep_n_tree_valid with (ir := a) in * by auto; destruct_lifts;
    eapply BALLOC.bn_valid_goodSize; eassumption
  end.

  Hint Rewrite le_plus_minus_r using auto.
  Local Hint Extern 1 (?a mod ?b < ?b) => apply Nat.mod_bound_pos; mult_nonzero.
  Local Hint Extern 1 (0 < ?n - ?m) => (apply Nat.lt_add_lt_sub_r; simpl; auto).

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
        erewrite indrep_n_tree_repeat by eauto.
        rewrite repeat_selN; eauto.
      - indrep_n_tree_bound.
      - rewrite indrep_n_helper_valid by omega.
        cancel.
      - indrep_n_extract.
        unfold IndRec.Defs.item; simpl. cancel.
        all : indrep_n_tree_bound.
      - match goal with [H : context [indrep_n_helper] |-_] => assert (HH := H) end.
        eapply lt_le_trans. apply Nat.mod_bound_pos; mult_nonzero; omega.
        apply Nat.eq_le_incl.
        rewrite listmatch_extract in HH; autorewrite with lists in *.
        rewrite indrep_n_length_pimpl in HH.
        destruct_lift HH. eauto.
        indrep_n_tree_bound.
      - apply selN_selN_hom.
        eapply indrep_n_indlist_forall_length; eauto.
        rewrite listmatch_length_pimpl, indrep_n_helper_length_piff in *; autorewrite with lists in *.
        destruct_lifts.
        rewrite mult_comm.
        apply div_lt_mul_lt; solve [indrep_n_tree_bound | mult_nonzero].
      Unshelve.
      exact $0.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indget _ _ _ _ _ ) _) => apply indget_ok : prog.
  Opaque indget.

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
        indrep_n_extract. cancel.
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

  Local Hint Extern 1 ({{_}} Bind (indread _ _ _ _ ) _) => apply indread_ok : prog.
  Opaque indread.

  Fixpoint indclear_all indlvl lxp bxp root ms : prog (LOG.mstate * Cache.cachestate) :=
    If (addr_eq_dec root 0) {
      Ret ms
    } else {
      let N := NIndirect ^ indlvl in
      ms <- match indlvl with
      | 0 => Ret ms
      | S indlvl' =>
        let^ (ms, indbns) <- IndRec.read lxp root 1 ms;
        let^ (ms) <- ForN i < NIndirect
          Hashmap hm
          Ghost [ F Fm l_part bxp crash m0 freelist ]
          Loopvar [ ms ]
          Invariant
            exists m freelist' indbns' l_part', LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
            [[ l_part' = repeat (repeat $0 N) i ++ skipn i l_part ]] *
            [[ indbns' = repeat $0 i ++ skipn i indbns ]] *
            [[[ m ::: Fm * listmatch (fun ibn' l' => indrep_n_tree indlvl' bxp (# ibn') l') indbns' l_part'
                         * BALLOC.rep bxp freelist' ]]] * [[ incl freelist freelist' ]]
          OnCrash crash
          Begin
            ms <- indclear_all indlvl' lxp bxp #(selN indbns i $0) ms;
            Ret ^(ms)
          Rof ^(ms);
          Ret ms
      end;
      BALLOC.free lxp bxp root ms
    }.

  Theorem indclear_all_ok : forall indlvl lxp bxp ir ms,
    let N := NIndirect ^ indlvl in
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET: ms
           exists m' freelist' l', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp 0 l' * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indclear_all indlvl lxp bxp ir ms.
    Proof.
      induction indlvl; simpl.
      + hoare.
        rewrite indrep_n_helper_pts_piff by auto.
        rewrite indrep_n_helper_0. cancel.
      + step. step.
        step.
        rewrite indrep_n_helper_valid by auto. cancel.
        rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *; simpl in *. rewrite firstn_oob by omega.
        step.
        step.
        rewrite listmatch_app_rev by (repeat rewrite repeat_length; auto).
        rewrite listmatch_extract with (i := 0) (a := skipn _ _).
        repeat rewrite skipn_selN, plus_0_r. cancel.
        rewrite skipn_length. omega.
        step.
        rewrite indrep_n_tree_0. cancel.
        unfold listmatch. simpl. rewrite indrep_n_tree_0. cancel.
        rewrite combine_app by (repeat rewrite repeat_length; auto).
        rewrite listpred_app. unfold removeN.
        repeat rewrite skipn_skipn. cancel.
        repeat rewrite app_length. repeat rewrite repeat_length.
        unfold removeN in *. repeat rewrite skipn_skipn in *. simpl in *. omega.
        step.
        rewrite indrep_n_helper_pts_piff by auto. cancel.
        step.
        rewrite skipn_oob, app_nil_r by omega. rewrite indrep_n_helper_0.
        cancel.
        apply LOG.intact_hashmap_subset. eauto.
    Grab Existential Variables.
    all : eauto; split.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_all _ _ _ _ _ ) _) => apply indclear_all_ok : prog.

  Definition indclear_aligned indlvl lxp bxp indbns start len ms :=
    let N := NIndirect ^ S indlvl in
    ForN i < len / N
      Hashmap hm
      Ghost [ F Fm l_part bxp crash m0 freelist ]
      Loopvar [ ms ]
      Invariant
        exists l_part' indbns' freelist' m,
        LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
        [[ l_part' = upd_range l_part (start / N) i (repeat $0 N) ]] *
        [[ indbns' = upd_range indbns (start / N) i $0 ]] *
        [[[ m ::: Fm * listmatch (fun ibn' l' => indrep_n_tree indlvl bxp (# ibn') l') indbns' l_part' *
                  BALLOC.rep bxp freelist' ]]] *
        [[ incl freelist freelist' ]]
      OnCrash crash
      Begin
        ms <- indclear_all indlvl lxp bxp #(selN indbns (i + start / N) IndRec.Defs.item0) ms;
        Ret ^(ms)
      Rof ^(ms).

  Theorem indclear_aligned_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm m0 m l_part freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns l_part
                         * BALLOC.rep bxp freelist) ]]] *
           [[ start / N + len / N <= length l_part ]] * [[ Nat.divide N start ]] * [[ Nat.divide N len ]]
    POST:hm' RET:^(ms)
           exists m' freelist' indbns' l_part', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns' l_part'
                          * BALLOC.rep bxp freelist') ]]] *
           [[ indbns' = upd_range indbns (start / N) (len / N) $0 ]] *
           [[ l_part' = upd_range l_part (start / N) (len / N) (repeat $0 N) ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indclear_aligned indlvl lxp bxp indbns start len ms.
    Proof.
      unfold indclear_aligned. unfold Nat.divide.
      prestep. norml.
      repeat rewrite Nat.div_mul in * by mult_nonzero.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      cancel; hoare.
      - rewrite listmatch_extract.
        repeat rewrite upd_range_selN_oob. cancel.
        all : repeat rewrite upd_range_length; omega.
      - rewrite listmatch_updN_removeN. rewrite roundTrip_0.
        repeat rewrite indrep_n_tree_0. cancel.
        repeat rewrite removeN_upd_range_l.
        rewrite plus_comm. repeat rewrite removeN_upd_range_r.
        erewrite <- removeN_upd_range_mid with (l := indbns).
        erewrite <- removeN_upd_range_mid with (l := l_part). cancel.
        all : repeat rewrite upd_range_length; omega.
      - cancel.
        apply LOG.intact_hashmap_subset. eauto.
    Grab Existential Variables. all : eauto; split.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_aligned _ _ _ _ _ _ _ ) _) => apply indclear_aligned_ok : prog.

  Definition update_block lxp bxp bn contents new ms :=
    If (list_eq_dec waddr_eq_dec new (repeat $0 NIndirect)) {
      ms <- BALLOC.free lxp bxp bn ms;
      Ret ^(ms, 0)
    } else {
      If (list_eq_dec waddr_eq_dec contents new) {
        Ret ^(ms, bn)
      } else {
        ms <- IndRec.write lxp bn new ms;
        Ret ^(ms, bn)
      }
    }.

  Theorem update_block_ok : forall lxp bxp ir indbns indbns' ms,
    {< F Fm m0 m freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm * [[ BALLOC.bn_valid bxp ir ]] *
            [[ IndRec.items_valid ir indbns' ]] *
           [[[ m ::: (Fm * indrep_n_helper bxp ir indbns) * BALLOC.rep bxp freelist ]]]
    POST:hm' RET: ^(ms, ir')
           exists m' freelist', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_helper bxp ir' indbns' * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist freelist' ]] *
           ([[ ir' = 0 ]] \/ [[ ir' = ir ]])
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} update_block lxp bxp ir indbns indbns' ms.
  Proof.
    unfold update_block.
    hoare; unfold BALLOC.bn_valid in *; intuition.
    - rewrite indrep_n_helper_pts_piff by auto. rewrite indrep_n_helper_0. cancel.
    - rewrite indrep_n_helper_valid by auto. cancel.
    - rewrite indrep_n_helper_valid by auto. cancel.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (update_block _ _ _ _ _ _) _) => apply update_block_ok : prog.

  Fixpoint indclear_from_aligned indlvl lxp bxp iblocks start len ms :=
    (* indlvl is for each block in iblocks *)
    If (addr_eq_dec len 0) {
      Ret ^(ms, iblocks)
    } else {
      let N := (NIndirect ^ S indlvl) in
      let ragged_bn := #(selN iblocks (start / N) $0) in
      If (addr_eq_dec ragged_bn 0) {
        Ret ^(ms, iblocks)
      } else {
        let^ (ms, indbns) <- IndRec.read lxp ragged_bn 1 ms;
        match indlvl with
        | 0 => 
          let indbns' := upd_range indbns 0 len $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        | S indlvl' =>
          let N' := NIndirect ^ (S indlvl') in
          let^ (ms) <- indclear_aligned indlvl' lxp bxp indbns 0 (len / N' * N') ms;
          let indbns' := upd_range indbns 0 (len / N') $0 in
          let^ (ms, indbns'') <- indclear_from_aligned indlvl' lxp bxp indbns' (len / N' * N') (len mod N') ms;
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns'' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        end
      }
    }.

  Theorem indclear_from_aligned_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm m0 m l_part freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns l_part
                         * BALLOC.rep bxp freelist) ]]] *
           [[ start + len <= length (concat l_part) ]] * [[ Nat.divide N start ]] * [[ len < N ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns' l_part'
                          * BALLOC.rep bxp freelist') ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indclear_from_aligned indlvl lxp bxp indbns start len ms.
  Proof.
    induction indlvl.
    + simpl. step; [> solve [hoare] |].
      pose proof listmatch_indrep_n_tree_forall_length 0 as H'.
      simpl in H'. rewrite H' in *. destruct_lifts. rewrite mult_1_r in *.
      prestep. norml.
      assert (start / NIndirect < length l_part).
        erewrite concat_hom_length in * by eauto.
        apply Nat.div_lt_upper_bound; auto. rewrite mult_comm. omega.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      cancel.
      - hoare.
        rewrite listmatch_extract in *.
        match goal with [H : # _ = _ |- _] => rewrite H in * end. rewrite indrep_n_helper_0 in *.
        destruct_lifts.
        erewrite upd_range_concat_hom_start_aligned by (eauto; omega).
        match goal with [H : _ = _ |- _] => rewrite H end.
        rewrite upd_range_same by omega.
        erewrite selN_eq_updN_eq; eauto. omega.
      - step.
        indrep_n_extract; try omega. rewrite indrep_n_helper_valid by eauto. cancel.
        rewrite firstn_oob. hoare.
       -- rewrite listmatch_extract in *. rewrite indrep_n_helper_valid in * by eauto.
          destruct_lifts. auto. omega.
       -- unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RALen, IndSig.RAStart.
          rewrite listmatch_extract in *. rewrite indrep_n_helper_length_piff in * by eauto.
          destruct_lifts. rewrite upd_range_length.
          intuition. all : try rewrite plus_0_r; solve [eauto | omega].
       -- indrep_n_extract; try omega. cancel.
       -- rewrite listmatch_updN_removeN. cancel. all: omega.
       -- erewrite upd_range_concat_hom_start_aligned by (eauto; omega). auto.
       -- rewrite natToWord_wordToNat. rewrite listmatch_updN_removeN by (eauto; omega). cancel.
       -- erewrite upd_range_concat_hom_start_aligned by (eauto; omega). auto.
       -- rewrite listmatch_extract in *. rewrite indrep_n_helper_length_piff in *.
          destruct_lifts. apply Nat.eq_le_incl. autorewrite with core. eauto.
          omega.
    + unfold indclear_from_aligned. fold indclear_from_aligned.
      prestep. norml.
      pose proof listmatch_indrep_n_tree_forall_length (S indlvl) as H'.
      simpl in H'. rewrite H' in *. destruct_lifts.
      cancel; [> solve [hoare] |].
      prestep. norml.
      assert (start / (NIndirect ^ S (S indlvl)) < length l_part); simpl in *.
        erewrite concat_hom_length in * by eauto.
        apply Nat.div_lt_upper_bound; auto. rewrite mult_comm. omega.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      cancel. step.
      rewrite listmatch_extract in *.
      match goal with [H : # _ = _ |- _] => rewrite H in * end. destruct_lifts.
      rewrite indrep_n_helper_0 in *. destruct_lifts.
      rewrite listmatch_repeat_l in *.
      rewrite listpred_indrep_n_tree_0 in *. destruct_lifts.
      erewrite upd_range_concat_hom_start_aligned by (eauto; omega).
      match goal with [H : selN _ _ _ = _ |- _] => rewrite H end.
      match goal with [H : Forall _ ?L |- _] =>
        erewrite concat_hom_repeat with (l := L) in * by eauto end.
      rewrite upd_range_same by omega.
      erewrite selN_eq_updN_eq; eauto. omega.
      match goal with [|- context [selN ?L ?N] ] => 
        rewrite listmatch_extract with (a := L) (i := N) in * end. destruct_lifts.
      step. rewrite indrep_n_helper_valid by eauto. cancel.
      rewrite firstn_oob.
      match goal with [H : context [listmatch _ ?l] |- context [?c = ?l] ] =>
        rewrite listmatch_length_pimpl with (a := l) in H;
        rewrite indrep_n_helper_length_piff in H; destruct_lift H end.
      step. rewrite Nat.div_mul by auto.
      rewrite Nat.div_0_l by auto. simpl in *.
      apply Nat.div_le_upper_bound; mult_nonzero. rewrite mult_comm.
      apply Nat.lt_le_incl. congruence.
      safestep. rewrite Nat.div_0_l by auto. rewrite Nat.div_mul by auto. cancel.
      rewrite mult_comm. rewrite <- Nat.div_mod by auto.
      erewrite concat_hom_length by eauto. rewrite upd_range_length.
      apply Nat.lt_le_incl. congruence.
      step.
      unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
      rewrite mult_1_l. intuition.
      match goal with [H : context [listmatch _ ?l] |- context [length ?l] ] =>
        rewrite listmatch_length_pimpl with (a := l) in H; destruct_lift H;
        substl (length l) end.
      match goal with [H : context [concat ?l] |- context [length ?l] ] =>
        apply f_equal with (f := @length _) in H; erewrite concat_hom_length in H; eauto end.
      rewrite upd_range_length in *.
      erewrite concat_hom_length in * by eauto.
      rewrite upd_range_length in *; mult_nonzero.
      rewrite Nat.mul_cancel_r in *; mult_nonzero. congruence.
      step.
      - rewrite indrep_n_helper_0. cancel.
        rewrite listmatch_updN_removeN. cancel. rewrite indrep_n_helper_0. cancel.
        omega. omega.
      - erewrite upd_range_concat_hom_start_aligned by (eauto; omega).
        repeat f_equal.
        do 2 match goal with [H : _ = _ |- _] => rewrite H end.
        rewrite concat_hom_upd_range by eauto. simpl.
        rewrite upd_range_upd_range; simpl; rewrite mult_comm; rewrite <- Nat.div_mod; auto.
      - rewrite natToWord_wordToNat. rewrite listmatch_updN_removeN. cancel.
        omega. omega.
      - match goal with [H : _ = _ |- _] => rewrite H end.
        symmetry. erewrite upd_range_concat_hom_start_aligned by (eauto; mult_nonzero; omega).
        rewrite concat_hom_upd_range; eauto.
        rewrite upd_range_upd_range; eauto.
        rewrite mult_comm with (n := len / _), <- Nat.div_mod by auto.
        simpl. repeat f_equal. eassumption.
      - cancel.
      - unfold IndRec.Defs.item in *. simpl in *.
        rewrite indrep_n_helper_length_piff in *. destruct_lifts. omega.
      - omega.
    Grab Existential Variables.
    all : eauto; exact $0.
  Qed.

  Hint Extern 1 ({{_}} Bind (indclear_from_aligned _ _ _ _ _ _ _) _) => apply indclear_from_aligned_ok : prog.

  Fixpoint indclear_to_aligned indlvl lxp bxp iblocks start ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec (start mod N) 0) {
      Ret ^(ms, iblocks)
    } else {
      let ragged_bn := #(selN iblocks (start / N) $0) in
      If (addr_eq_dec ragged_bn 0) {
        Ret ^(ms, iblocks)
      } else {
        let^ (ms, indbns) <- IndRec.read lxp ragged_bn 1 ms;
        match indlvl with
        | 0 =>
          let indbns' := upd_range indbns (start mod NIndirect) (NIndirect - (start mod NIndirect)) $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        | S indlvl' =>
          let N' := NIndirect ^ S indlvl' in
          let start' := start mod N in
          let^ (ms, indbns') <- indclear_to_aligned indlvl' lxp bxp indbns start' ms;
          let^ (ms) <- indclear_aligned indlvl' lxp bxp indbns' (roundup start' N') (N - (roundup start' N')) ms;
          let indbns'' := upd_range indbns' (divup start' N') (NIndirect - (divup start' N')) $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns'' ms;
          Ret ^(ms, updN iblocks (start / N) $ v)
        end
      }
    }.

  Theorem indclear_to_aligned_ok : forall indlvl lxp bxp indbns start ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm m0 m l_part freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns l_part
                         * BALLOC.rep bxp freelist) ]]] *
           [[ start <= length (concat l_part) ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns' l_part'
                          * BALLOC.rep bxp freelist') ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start (roundup start N - start) $0 ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indclear_to_aligned indlvl lxp bxp indbns start ms.
  Proof.
    induction indlvl.
    intros.
    + simpl in *. subst N. rewrite mult_1_r in *.
      step. hoare.
      unfold roundup. rewrite divup_eq_div by auto.
      rewrite mul_div by auto. autorewrite with core. rewrite upd_range_0. auto.
      rewrite (listmatch_indrep_n_tree_forall_length 0) in *.
      destruct_lifts. rewrite mult_1_r in *.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      prestep. norml.
      assert (start / NIndirect < length l_part).
        erewrite concat_hom_length in *; eauto.
        apply Nat.div_lt_upper_bound; auto. rewrite mult_comm.
        edestruct le_lt_eq_dec; [> | eauto |]; eauto.
        subst. rewrite Nat.mod_mul in * by auto. intuition.
      step.
      rewrite roundup_eq by auto. rewrite minus_plus by auto.
      rewrite listmatch_extract in *.
      match goal with [H : # _ = _ |- _] => rewrite H in * end. rewrite indrep_n_helper_0 in *.
      destruct_lifts. erewrite upd_range_concat_hom_small; eauto.
      erewrite selN_eq_updN_eq. auto.
      match goal with [H : _ = _ |- _] => rewrite H end. rewrite upd_range_same. eauto.
      all : autorewrite with core; auto with *.
      rewrite <- roundup_eq by auto.
      erewrite concat_hom_length in * by eauto.
      apply roundup_le. omega.
      indrep_n_extract. rewrite indrep_n_helper_valid by eassumption. cancel.
      rewrite firstn_oob.
      hoare.
      - rewrite listmatch_extract in *. rewrite indrep_n_helper_valid in * by eauto.
        destruct_lifts. auto. omega.
      - unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RALen, IndSig.RAStart.
        rewrite listmatch_extract in *. rewrite indrep_n_helper_length_piff in * by eauto.
        destruct_lifts. rewrite upd_range_length. rewrite plus_0_r. intuition; eauto. omega.
      - indrep_n_extract. cancel.
      - rewrite listmatch_updN_removeN. cancel. all: omega.
      - rewrite roundup_eq by auto. rewrite minus_plus.
        erewrite upd_range_concat_hom_small; eauto.
        all : autorewrite with core; eauto.
        rewrite <- roundup_eq by auto.
        erewrite concat_hom_length in * by eauto.
        apply roundup_le. auto.
        apply Nat.lt_add_lt_sub_r. simpl. apply Nat.mod_upper_bound; auto.
      - rewrite natToWord_wordToNat. rewrite listmatch_updN_removeN by (eauto; omega). cancel.
      - rewrite roundup_eq by auto. rewrite minus_plus.
        erewrite upd_range_concat_hom_small; eauto.
        rewrite <- roundup_eq by auto.
        erewrite concat_hom_length in * by eauto.
        apply roundup_le. auto.
        rewrite le_plus_minus_r; auto.
        apply Nat.lt_add_lt_sub_r. simpl. apply Nat.mod_upper_bound; auto.
      - rewrite listmatch_extract in *. rewrite indrep_n_helper_length_piff in *.
        destruct_lifts. autorewrite with core. apply Nat.eq_le_incl. eassumption.
        omega.
    + unfold indclear_to_aligned. fold indclear_to_aligned.
      prestep. norml.
      pose proof listmatch_indrep_n_tree_forall_length (S indlvl) as H'.
      simpl in H'. rewrite H' in *. destruct_lifts.
      cancel. hoare.
      unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero.
      autorewrite with core. auto.
      prestep. norml.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      assert (start / (NIndirect ^ S (S indlvl)) < length l_part); simpl in *.
        erewrite concat_hom_length in *; eauto.
        apply Nat.div_lt_upper_bound; auto. rewrite mult_comm.
        edestruct le_lt_eq_dec; [> | eauto |]; eauto.
        subst. rewrite Nat.mod_mul in * by auto. intuition.
      cancel. step.
      rewrite roundup_eq by auto. rewrite minus_plus by auto.
      rewrite listmatch_extract in *. destruct_lifts.
      erewrite upd_range_concat_hom_small; eauto.
      match goal with [H : # _ = _ |- _] => rewrite H in * end.
      rewrite indrep_n_helper_0 in *. destruct_lifts.
      rewrite listmatch_repeat_l in *.
      rewrite listpred_indrep_n_tree_0 in *. destruct_lifts.
      erewrite selN_eq_updN_eq. auto.
      match goal with [H : selN _ _ _ = _ |- _] => rewrite H end.
      match goal with [H : Forall _ ?L |- _] => erewrite concat_hom_repeat with (l := L) in * by eauto end.
      rewrite upd_range_same by omega. eauto.
      all : autorewrite with core; auto with *.
      erewrite concat_hom_length in * by eauto.
      rewrite <- roundup_eq by auto. apply roundup_le. congruence.
      mult_nonzero.
      rewrite listmatch_extract in *. simpl in *. destruct_lifts.
      step. rewrite indrep_n_helper_valid by eauto. cancel.
      rewrite firstn_oob.
      match goal with [H : context [listmatch _ ?l] |- context [?c = ?l] ] =>
        rewrite listmatch_length_pimpl with (a := l) in H;
        rewrite indrep_n_helper_length_piff in H; destruct_lift H end.
      step.
      erewrite concat_hom_length by eauto.
      eapply le_trans; [> | apply mult_le_compat_r]. eauto. omega.
      safestep.
      unfold roundup. rewrite <- Nat.mul_sub_distr_r. repeat rewrite Nat.div_mul by auto.
      autorewrite with core.
      match goal with [H : context [concat ?l] |- context [length ?l] ] =>
        apply f_equal with (f := @length _) in H; erewrite concat_hom_length in H; eauto end.
      rewrite upd_range_length in *; autorewrite with core; auto with *.
      erewrite concat_hom_length in * by eauto.
      rewrite Nat.mul_cancel_r in *; mult_nonzero. omega.
      apply divup_le. rewrite mult_comm. eauto.
      step.
      unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
      rewrite mult_1_l.
      match goal with [H : context [listmatch _ ?l] |- context [length (upd_range ?l _ _ _)] ] =>
        rewrite listmatch_length_pimpl with (a := l) in H; destruct_lift H end.
      match goal with [H : concat ?l = upd_range _ _ _ _ |- _] =>
        apply f_equal with (f := @length _) in H; erewrite concat_hom_length in H;
        rewrite upd_range_length in H; eauto end.
      erewrite concat_hom_length in * by eauto.
      rewrite Nat.mul_cancel_r in *; mult_nonzero.
      rewrite upd_range_length in *. intuition; omega.
      step.
      - rewrite indrep_n_helper_0. cancel.
        rewrite listmatch_updN_removeN. cancel. rewrite indrep_n_helper_0. cancel.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r.
        repeat rewrite Nat.div_mul by auto. assumption.
        all : omega.
      - rewrite roundup_eq with (a := start) by mult_nonzero.
        rewrite minus_plus.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r. repeat rewrite Nat.div_mul by mult_nonzero.
        eapply indclear_upd_range_helper_1; eauto.
        erewrite concat_hom_length by eauto. congruence.
      - rewrite natToWord_wordToNat.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r. repeat rewrite Nat.div_mul by auto.
        rewrite listmatch_updN_removeN. cancel.
        all : omega.
      - erewrite indclear_upd_range_helper_1; eauto.
        f_equal. rewrite roundup_eq by auto. omega.
        erewrite concat_hom_length by eauto. congruence.
      - cancel.
      - rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *. simpl in *. omega.
      - omega.
    Grab Existential Variables. all : eauto; exact $0.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_to_aligned _ _ _ _ _ _) _) => apply indclear_to_aligned_ok : prog.

  Definition indclear_multiple_blocks indlvl lxp bxp indbns start len ms :=
    let N := NIndirect ^ S indlvl in
    let^ (ms, indbns') <- indclear_to_aligned indlvl lxp bxp indbns start ms;
    let len' := len - (roundup start N - start) in
    let start' := start + (roundup start N - start) in
    let^ (ms) <- indclear_aligned indlvl lxp bxp indbns' start' (len' / N * N) ms;
    let indbns'' := upd_range indbns' (start' / N) (len' / N) $0 in
    let start'' := start' + (len' / N * N) in
    let len'' := len' mod N in
    indclear_from_aligned indlvl lxp bxp indbns'' start'' len'' ms.

  Theorem indclear_multiple_blocks_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm m0 m l_part freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns l_part
                         * BALLOC.rep bxp freelist) ]]] *
           [[ start <= length (concat l_part) ]] * [[ (N - start mod N) < len ]] *
           [[ start + len <= length (concat l_part) ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * listmatch (fun ibn l => indrep_n_tree indlvl bxp (#ibn) l) indbns' l_part'
                          * BALLOC.rep bxp freelist') ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indclear_multiple_blocks indlvl lxp bxp indbns start len ms.
  Proof.
    intros. subst N.
    unfold indclear_multiple_blocks.
    hoare.
    + repeat rewrite Nat.div_mul by mult_nonzero.
      eapply le_trans. apply div_add_distr_le.
      match goal with [H : concat _ = _ |- _] => apply f_equal with (f := @length _) in H end.
      rewrite upd_range_length in *.
      repeat erewrite concat_hom_length in * by eauto.
      rewrite Nat.mul_cancel_r in * by mult_nonzero.
      apply Nat.div_le_upper_bound; auto. rewrite mult_comm with (m := length _).
      destruct (addr_eq_dec (start mod (NIndirect * NIndirect ^ indlvl)) 0).
      - unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero.
        autorewrite with core. congruence.
      - rewrite roundup_eq by auto. rewrite minus_plus.
        rewrite <- plus_assoc. autorewrite with core; solve [congruence | omega].
    + autorewrite with core; auto.
    + repeat rewrite Nat.div_mul by auto. cancel.
    + erewrite concat_hom_length by auto. rewrite upd_range_length.
      rewrite mult_comm with (m := _ * _ ^ _).
      rewrite <- plus_assoc. rewrite <- Nat.div_mod by auto.
      match goal with [H : concat _ = _ |- _] => apply f_equal with (f := @length _) in H end.
      rewrite upd_range_length in *.
      repeat erewrite concat_hom_length in * by eauto.
      rewrite Nat.mul_cancel_r in * by mult_nonzero.
      destruct (addr_eq_dec (start mod (NIndirect * NIndirect ^ indlvl)) 0).
      - unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero.
        autorewrite with core. congruence.
      - rewrite roundup_eq by auto. rewrite minus_plus.
        rewrite <- plus_assoc. autorewrite with core; solve [congruence | omega].
    + autorewrite with core. auto.
    + rewrite concat_hom_upd_range in * by eauto.
      set (N := _ * _ ^ _) in *.
      rewrite le_plus_minus_r in * by auto.
      rewrite roundup_round in *.
      rewrite upd_range_upd_range in *.
      rewrite mult_comm with (m := N) in *.
      rewrite <- Nat.div_mod in * by mult_nonzero.
      repeat match goal with [H : concat ?l = _ |- context [concat ?l] ] => rewrite H end.
      erewrite <- le_plus_minus_r with (m := roundup start N) at 2.
      rewrite upd_range_upd_range. f_equal.
      destruct (addr_eq_dec (start mod N) 0).
      - unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero. omega.
      - rewrite roundup_eq by mult_nonzero. rewrite minus_plus. omega.
      - auto.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_multiple_blocks _ _ _ _ _ _ _) _) => apply indclear_multiple_blocks_ok : prog.

  Fixpoint indclear indlvl lxp bxp (root : addr) start len ms : prog (LOG.mstate * Cache.cachestate * (addr * unit)) :=
    let N := NIndirect ^ indlvl in
    If (addr_eq_dec root 0) {
      Ret ^(ms, 0)
    } else {
      If (addr_eq_dec len 0) {
        Ret ^(ms, root)
      } else {
        let^ (ms, indbns) <- IndRec.read lxp root 1 ms;
        let^ (ms, indbns') <- match indlvl with
        | 0 =>
           Ret ^(ms, upd_range indbns start len $0)
        | S indlvl' =>
          If (le_lt_dec len (N - start mod N)) {
            let^ (ms, v) <- indclear indlvl' lxp bxp #(selN indbns (start / N) $0) (start mod N) len ms;
            Ret ^(ms, updN indbns (start / N) $ v)
          } else {
            indclear_multiple_blocks indlvl' lxp bxp indbns start len ms
          }
        end;
        update_block lxp bxp root indbns indbns' ms
      }
    }.

  Theorem indclear_ok : forall indlvl lxp bxp ir start len ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp ir l * BALLOC.rep bxp freelist) ]]] *
           [[ start + len <= length l ]]
    POST:hm' RET:^(ms, ir')
           exists m' freelist' l', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp ir' l' * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist freelist' ]] * [[ l' = upd_range l start len $0 ]] *
           ([[ ir = ir' ]] \/ [[ ir' = 0 ]])
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indclear indlvl lxp bxp ir start len ms.
    Proof.
      induction indlvl.
      + simpl. hoare.
        rewrite indrep_n_helper_length_piff, indrep_n_helper_0 in *. destruct_lifts.
        rewrite upd_range_same. auto.
        rewrite indrep_n_helper_valid by auto. cancel.
        all : try (rewrite indrep_n_helper_length_piff in *;
                   repeat match goal with [H : context [lift_empty (length _ = _)] |- _ ] => destruct_lift H end;
                   unfold IndRec.Defs.item in *; simpl in *;
                   rewrite firstn_oob in * by omega).
        all : try cancel; auto.
        unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed in *.
        simpl in *. rewrite upd_range_length by omega. intuition.
      + simpl.
        step. step. rewrite indrep_n_helper_0 in *. destruct_lifts.
        rewrite listmatch_repeat_l in *. rewrite listpred_indrep_n_tree_0 in *.
        destruct_lifts. erewrite concat_hom_repeat by eauto.
        rewrite upd_range_same. auto.
        step. step.
        step. rewrite indrep_n_helper_valid by auto. cancel.
        rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *; simpl in *. rewrite firstn_oob by omega.
        step.
        - safestep.
          indrep_n_extract; solve [cancel | indrep_n_tree_bound].
          match goal with [H : context [listmatch _ _ ?l] |- context [selN ?l ?n] ] =>
            rewrite listmatch_extract with (i := n) in H; try indrep_n_tree_bound
          end.
          indrep_n_tree_extract_lengths.
          match goal with [H : length _ = _ |- _ ] => rewrite H end. omega.
          step; try (rewrite natToWord_wordToNat; rewrite updN_selN_eq).
          rewrite indrep_n_helper_valid in * by auto. unfold IndRec.rep in *. destruct_lifts. auto.
         -- prestep. norm. cancel. cancel. repeat split.
            pred_apply. norm; intuition.
            instantiate (iblocks := updN _ _ _). cancel.
            rewrite listmatch_updN_removeN. repeat rewrite indrep_n_helper_0. rewrite updN_selN_eq. cancel.
            repeat rewrite repeat_selN.
            repeat rewrite indrep_n_tree_0. cancel.
            all : autorewrite with lists; try indrep_n_tree_bound; auto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega).
            repeat f_equal.
            rewrite indrep_n_helper_0 in *. destruct_lifts.
            erewrite concat_hom_length in * by eauto.
            rewrite listmatch_repeat_l in *.
            rewrite listpred_extract in *. destruct_lifts.
            rewrite indrep_n_tree_0 in *. destruct_lifts.
            match goal with [H : _ |- _ ] => rewrite H end. rewrite upd_range_same. auto.
            apply Nat.div_lt_upper_bound; auto. rewrite mult_comm. omega.
            cancel. cancel. repeat split.
            pred_apply. norm; intuition.
            instantiate (iblocks := updN _ _ _). cancel.
            rewrite listmatch_updN_removeN. repeat rewrite indrep_n_helper_0. cancel.
            rewrite updN_selN_eq. cancel.
            all : autorewrite with lists; try indrep_n_tree_bound; auto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega).
            reflexivity.
         -- unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed in *.
              simpl in *. rewrite length_updN. intuition. omega.
         -- prestep. norm. cancel. cancel. repeat split.
            pred_apply. norm; intuition.
            instantiate (iblocks := updN _ _ _). cancel.
            rewrite listmatch_updN_removeN. repeat rewrite indrep_n_helper_0. cancel.
            all : autorewrite with lists; try indrep_n_tree_bound; auto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega).
            reflexivity.
            cancel. cancel.
            repeat split.
            pred_apply. norm; intuition.
            instantiate (iblocks := updN _ _ _). cancel.
            rewrite listmatch_updN_removeN. repeat rewrite indrep_n_helper_0. cancel.
            all : autorewrite with lists; try indrep_n_tree_bound; auto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega).
            reflexivity.
         -- cancel.
      - hoare.
        unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed.
        simpl. intuition.
        erewrite listmatch_length_pimpl in *.
        repeat match goal with [H : context [lift_empty (length _ = _)] |- _ ] =>
          destruct_lift H end.
        match goal with [H : concat _ = _|- _] => apply f_equal with (f := @length _) in H end.
        rewrite upd_range_length in *. repeat erewrite concat_hom_length in * by eauto.
        rewrite Nat.mul_cancel_r in * by mult_nonzero.
        unfold IndRec.Defs.item. simpl. omega.
    Grab Existential Variables.
    all : eauto; exact $0.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear _ _ _ _ _ _ _ ) _) => apply indclear_ok : prog.
  Opaque indclear.

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

  (* This is a wrapper for IndRec.write that will use an alternate spec *)
  Definition indrec_write_blind lxp xp items ms :=
    IndRec.write lxp xp items ms.

  (* This is an alternate spec for IndRec.write that does not require IndRec.rep
    to hold beforehand. This allows blind writes to blocks that have not been
    initialized beforehand with IndRec.init *)
  Theorem indrec_write_blind_ok : forall lxp xp items ms,
    {< F Fm m0 m old,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
          [[ IndRec.items_valid xp items ]] * [[ xp <> 0 ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) xp [old] ]]]
    POST:hm' RET:ms' exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
          [[[ m' ::: Fm * IndRec.rep xp items ]]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} indrec_write_blind lxp xp items ms.
  Proof.
    unfold indrec_write_blind, IndRec.write, IndRec.rep, IndRec.items_valid.
    hoare.
    unfold IndSig.RAStart. instantiate (1 := [_]). cancel.
    rewrite IndRec.Defs.ipack_one. auto.
    unfold IndRec.Defs.item in *. simpl in *. omega.
    rewrite vsupsyn_range_synced_list; auto.
    rewrite IndRec.Defs.ipack_one. auto.
    unfold IndRec.Defs.item in *. simpl in *. omega.
  Qed.

  Local Hint Extern 0 ({{_}} Bind (indrec_write_blind _ _ _ _) _) => apply indrec_write_blind_ok : prog.

  Definition indput_upd_if_necessary lxp ir v indbns to_grow ms := 
    If (addr_eq_dec v #(selN indbns to_grow $0)) {
      Ret ms
    } else {
      indrec_write_blind lxp ir (indbns ⟦ to_grow := ($ v)⟧) ms
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
    unfold indrec_write_blind.
    hoare.
    rewrite natToWord_wordToNat. rewrite updN_selN_eq. cancel.
    unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
    unfold Rec.well_formed. simpl. intuition.
    rewrite length_updN. rewrite indrep_n_helper_length_piff in *. destruct_lifts.
    omega.
    rewrite indrep_n_helper_valid by omega. cancel.
    rewrite indrep_n_helper_valid by omega. cancel.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indput_upd_if_necessary _ _ _ _ _ _) _) => apply indput_upd_if_necessary_ok : prog.

  Fixpoint indput indlvl lxp bxp root off bn ms :=
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
                     indrec_write_blind lxp ir ((repeat $0 NIndirect) ⟦ off := bn ⟧) ms
                   } else {
                     IndRec.put lxp ir off bn ms
                   };
        Ret ^(ms, ir)
      | S indlvl' =>
        let to_grow := off / N in
        let^ (ms, indbns) <- indput_get_blocks lxp is_alloc ir ms;
        let ir_to_grow := #(selN indbns to_grow $0) in
        let^ (ms, v) <- indput indlvl' lxp bxp ir_to_grow (off mod N) bn ms;
        If (addr_eq_dec v 0) {
          Ret ^(ms, 0)
        } else {
          ms <- indput_upd_if_necessary lxp ir v indbns to_grow ms;
          Ret ^(ms, ir)
        }
      end
    end.

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
    >} indput indlvl lxp bxp ir off bn ms.
    Proof.
      induction indlvl; intros; simpl.
      + step.
        - hoare.
         -- unfold IndRec.items_valid, IndSig.RAStart, IndSig.RALen, IndSig.xparams_ok.
            rewrite mult_1_l. unfold Rec.well_formed. simpl. unfold BALLOC.bn_valid in *.
            rewrite length_updN, repeat_length. intuition.
         -- unfold BALLOC.bn_valid in *. intuition.
         -- or_r. cancel. unfold BALLOC.bn_valid in *; intuition.
            rewrite indrep_n_helper_0. rewrite indrep_n_helper_valid by omega.
            unfold BALLOC.bn_valid. cancel.
        - hoare.
        --  rewrite indrep_n_helper_valid by omega. cancel.
        --  or_r. cancel.
            rewrite indrep_n_helper_valid in * by omega. cancel.
            match goal with [H : context [?P] |- ?P] => destruct_lift H end. auto.
      + step.
        - step. safestep.
          rewrite repeat_selN. rewrite indrep_n_helper_0, indrep_n_tree_0. cancel.
          indrep_n_tree_bound.
          rewrite repeat_length. apply Nat.mod_bound_pos; mult_nonzero; omega.
          unfold indput_upd_if_necessary. 
          repeat rewrite repeat_selN. rewrite roundTrip_0.
          (* the spec given is for updates, not blind writes *)
          hoare.
         -- unfold BALLOC.bn_valid in *.
            unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed.
            simpl. rewrite length_updN, repeat_length. intuition.
         -- unfold BALLOC.bn_valid in *. intuition.
         -- or_r.
          (* safecancel isn't safe enough, so do it manually - the long and short of it is that the
             listmatches get canceled before the indrep_n_helper, causing incorrect instantiation *)
            norm. cancel. repeat split; auto.
            pred_apply. norm; intuition. instantiate (iblocks := updN _ _ _). cancel.
            unfold BALLOC.bn_valid in *; intuition.
            rewrite indrep_n_helper_valid by omega. cancel.
            rewrite listmatch_updN_removeN.
            indrep_n_extract. cancel.
            rewrite repeat_selN, roundTrip_0. rewrite indrep_n_tree_0.
            rewrite wordToNat_natToWord_idempotent'. cancel.
            eapply BALLOC.bn_valid_goodSize; eauto.
            rewrite indrep_n_tree_valid in * by auto. destruct_lifts. auto.
            all : try rewrite repeat_length.
            all : try solve [indrep_n_tree_bound].
            unfold BALLOC.bn_valid. auto.
            erewrite Nat.div_mod with (x := off) at 1.
            rewrite plus_comm, mult_comm. rewrite updN_concat; auto.
            repeat f_equal.
            match goal with [H : context [?l] |- context [selN ?l] ] =>
              rewrite listmatch_extract with (b := l) in H
            end. rewrite repeat_selN in *. rewrite roundTrip_0, indrep_n_tree_0 in *.
            destruct_lifts. eauto.
            all : try rewrite repeat_length.
            all : try solve [indrep_n_tree_bound].
            apply Nat.mod_bound_pos; mult_nonzero; omega.
            mult_nonzero.
            auto.
         -- indrep_n_tree_bound.
         -- cancel.
         -- or_l. cancel.
        - monad_simpl. simpl.
          step.
          safestep.
          indrep_n_extract; solve [cancel | indrep_n_tree_bound].
          eapply lt_le_trans.
          apply Nat.mod_bound_pos; mult_nonzero; omega.
          apply Nat.eq_le_incl. symmetry. apply Forall_selN. eauto.
          indrep_n_tree_bound.
          match goal with [H : context [indrep_n_helper] |- _] =>
            pose proof H; rewrite indrep_n_helper_length_piff,
                            indrep_n_helper_valid in H by omega;
            destruct_lift H end.
          hoare.
          all : try solve [cancel].
          all : or_r; norm; try solve [cancel].
          all : repeat (split; try reflexivity); auto.
          all : try (pred_apply; norm; intuition).
          all : try ((instantiate (iblocks := updN _ _ _) ||
                      instantiate (iblocks0 := updN _ _ _)); cancel).
          all : try (rewrite listmatch_updN_removeN by indrep_n_tree_bound; cancel).
          all : try rewrite natToWord_wordToNat;
                try rewrite wordToNat_natToWord_idempotent'; (cancel || auto).
          all : erewrite Nat.div_mod with (x := off) at 1.
          all : try (rewrite plus_comm, mult_comm; rewrite updN_concat).
          all : auto.
          all : apply Nat.mod_bound_pos; mult_nonzero; omega.
    Grab Existential Variables. all : auto; solve [exact nil | exact $0].
  Qed.

  Local Hint Extern 0 ({{_}} Bind (indput _ _ _ _ _ _ _) _) => apply indput_ok : prog.
  Opaque indput.

  (************** rep invariant *)

  Opaque indrep_n_tree.

  Definition indrep bxp ir (indlist : list waddr) :=
    ( indrep_n_tree 0 bxp (IRIndPtr ir) (firstn NIndirect indlist) *
      indrep_n_tree 1 bxp (IRDindPtr ir) (firstn (NIndirect ^ 2) (skipn NIndirect indlist)) *
      indrep_n_tree 2 bxp (IRTindPtr ir) (skipn (NIndirect + NIndirect ^ 2) indlist)
    )%pred.

  Definition rep bxp (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp ir indlist *
      [[ l = firstn (length l) ((IRBlocks ir) ++ indlist) ]] *
      [[ list_same $0 (skipn (length l) ((IRBlocks ir) ++ indlist)) ]] )%pred.

  Definition rep_direct bxp (ir : irec) (l : list waddr) : @pred _ addr_eq_dec valuset :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l <= NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp ir indlist *
      [[ l = firstn (length l) (IRBlocks ir) ]] *
      [[ list_same $0 (skipn (length l) (IRBlocks ir)) ]] *
      [[ list_same $0 indlist ]] )%pred.

  Definition rep_indirect bxp (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l > NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp ir indlist *
      [[ l = (IRBlocks ir) ++ firstn (length l - NDirect) indlist ]] *
      [[ list_same $0 (skipn (length l - NDirect) indlist) ]] )%pred.

  Hint Resolve list_same_app_l.
  Hint Resolve list_same_app_r.
  Hint Resolve list_same_app_both.

  Lemma rep_piff_direct : forall bxp ir l,
    length l <= NDirect ->
    rep bxp ir l <=p=> rep_direct bxp ir l.
  Proof.
    intros. unfold rep, rep_direct. split; cancel.
    - rewrite firstn_app_l in * by omega; auto.
    - rewrite skipn_app_l in * by omega; eauto.
    - rewrite skipn_app_l in * by omega; eauto.
    - substl l at 1; rewrite firstn_app_l by omega; auto.
    - rewrite skipn_app_l by omega; eauto.
  Qed.

  Lemma rep_piff_indirect : forall bxp ir l,
    length l > NDirect ->
    rep bxp ir l <=p=> rep_indirect bxp ir l.
  Proof.
    unfold rep, rep_indirect; intros; split; cancel; try omega.
    - rewrite <- firstn_app_r; setoid_rewrite H3.
      replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    - rewrite skipn_app_r_ge in * by omega. congruence.
    - substl l at 1; rewrite <- firstn_app_r. setoid_rewrite H3.
      replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    - rewrite skipn_app_r_ge by omega. congruence.
  Qed.

  Lemma rep_selN_direct_ok : forall F bxp ir l m off,
    (F * rep bxp ir l)%pred m ->
    off < NDirect ->
    off < length l ->
    selN (IRBlocks ir) off $0 = selN l off $0.
  Proof.
    unfold rep. intros; destruct_lift H.
    substl.
    rewrite selN_firstn by auto.
    rewrite selN_app1 by omega; auto.
  Qed.

  Theorem indrep_length_pimpl : forall bxp ir l, indrep bxp ir l <=p=> indrep bxp ir l * [[ length l = NBlocks - NDirect ]].
  Proof.
    intros.
    unfold indrep.
    split; [> | cancel].
    intros m' H'. pred_apply. cancel.
    repeat rewrite <- plus_assoc. rewrite minus_plus.
    indrep_n_tree_extract_lengths.
    erewrite <- firstn_skipn with (l := l). rewrite app_length. f_equal; eauto.
    erewrite <- firstn_skipn with (l := skipn _ _). rewrite app_length.
    f_equal; eauto. rewrite skipn_skipn'. auto.
  Qed.

  Theorem indrep_bxp_switch : forall bxp bxp' xp ilist,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep bxp xp ilist <=p=> indrep bxp' xp ilist.
  Proof.
    intros. unfold indrep.
    repeat match goal with [|- context [indrep_n_tree ?i] ] =>
      rewrite indrep_n_tree_bxp_switch with (indlvl := i) by eassumption
    end.
    reflexivity.
  Qed.

  Theorem indrep_0 : forall bxp ir l,
    IRIndPtr ir = 0 -> IRDindPtr ir = 0 -> IRTindPtr ir = 0 ->
    indrep bxp ir l <=p=> [[l = repeat $0 (NBlocks - NDirect)]].
  Proof.
    unfold indrep. intros.
    repeat match goal with [H : _ = 0 |- _] => rewrite H end.
    repeat rewrite indrep_n_tree_0. simpl.
    repeat rewrite <- plus_assoc. rewrite minus_plus.
    rewrite mult_1_r in *.
    split; cancel; subst.
    erewrite <- firstn_skipn with (l := l).
    erewrite <- firstn_skipn with (l := skipn _ l).
    rewrite skipn_skipn'.
    repeat rewrite <- repeat_app.
    repeat (f_equal; eauto).
    all : repeat rewrite skipn_repeat;
          repeat rewrite firstn_repeat by lia; f_equal; lia.
  Qed.

  Theorem xform_indrep : forall xp ir l,
    crash_xform (indrep xp ir l) <=p=> indrep xp ir l.
  Proof.
    unfold indrep. intros.
    xform_norm.
    repeat rewrite xform_indrep_n_tree.
    reflexivity.
  Qed.

  (************* program *)

  Definition get lxp (ir : irec) off ms :=
    If (lt_dec off NDirect) {
      Ret ^(ms, selN (IRBlocks ir) off $0)
    } else {
      let off := off - NDirect in
      If (lt_dec off NIndirect) {
        indget 0 lxp (IRIndPtr ir) off ms
      } else {
        let off := off - NIndirect in
        If (lt_dec off (NIndirect ^ 2)) {
          indget 1 lxp (IRDindPtr ir) off ms
        } else {
          let off := off - NIndirect ^ 2 in
          indget 2 lxp (IRTindPtr ir) off ms
        }
      }
    }.

  Definition read lxp (ir : irec) ms :=
    If (le_dec (IRLen ir) NDirect) {
      Ret ^(ms, firstn (IRLen ir) (IRBlocks ir))
    } else {
      let^ (ms, indbns) <- indread 0 lxp (IRIndPtr ir) ms;
      let^ (ms, dindbns) <- indread 1 lxp (IRDindPtr ir) ms;
      let^ (ms, tindbns) <- indread 2 lxp (IRTindPtr ir) ms;
      Ret ^(ms, (firstn (IRLen ir) ((IRBlocks ir) ++ indbns ++ dindbns ++ tindbns)))
    }.

  Definition indshrink_helper indlvl lxp bxp bn nl ms :=
    let start := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    let len := NIndirect ^ S indlvl in
    If (lt_dec nl (start + len)) {
      indclear indlvl lxp bxp bn (nl - start) (len - (nl - start)) ms
    } else {
      Ret ^(ms, bn)
    }.

  Definition indshrink lxp bxp ir nl ms :=
    let^ (ms, indptr)  <- indshrink_helper 0 lxp bxp (IRIndPtr ir)  nl ms;
    let^ (ms, dindptr) <- indshrink_helper 1 lxp bxp (IRDindPtr ir) nl ms;
    let^ (ms, tindptr) <- indshrink_helper 2 lxp bxp (IRTindPtr ir) nl ms;
    Ret ^(ms, indptr, dindptr, tindptr).

  Definition shrink lxp bxp (ir : irec) nr ms :=
    let ol := (IRLen ir) in
    let nl := (ol - nr) in
    If (le_dec ol NDirect) {
      Ret ^(ms, upd_irec ir nl (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir)
                         (upd_range (IRBlocks ir) nl (NDirect - nl) $0))
    } else {
      let ol' := ol - NDirect in
      let nl' := nl - NDirect in
      let^ (ms, indptr, dindptr, tindptr) <- indshrink lxp bxp ir nl' ms;
      Ret ^(ms, upd_irec ir nl indptr dindptr tindptr
                         (upd_range (IRBlocks ir) nl (NDirect - nl) $0))
    }.

  Definition indgrow lxp bxp ir off bn ms :=
    If (lt_dec off NIndirect) {
      let^ (ms, v) <- indput 0 lxp bxp (IRIndPtr ir) off bn ms;
      Ret ^(ms, v, v, (IRDindPtr ir), (IRTindPtr ir))
    } else {
      let off := off - NIndirect in
      If (lt_dec off (NIndirect ^ 2)) {
        let^ (ms, v) <- indput 1 lxp bxp (IRDindPtr ir) off bn ms;
        Ret ^(ms, v, (IRIndPtr ir), v, (IRTindPtr ir))
      } else {
        let off := off - NIndirect ^ 2 in
        let^ (ms, v) <- indput 2 lxp bxp (IRTindPtr ir) off bn ms;
        Ret ^(ms, v, (IRIndPtr ir), (IRDindPtr ir), v)
      }
    }.

  Definition grow lxp bxp (ir : irec) bn ms :=
    let len := (IRLen ir) in
    If (lt_dec len NDirect) {
      (* change direct block address *)
      Ret ^(ms, OK (upd_irec ir (S len) (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) (updN (IRBlocks ir) len bn)))
    } else {
      let off := (len - NDirect) in
      If (waddr_eq_dec bn $0) {
        Ret ^(ms, OK (upd_len ir (S len)))
      } else {
        let^ (ms, v, indptr, dindptr, tindptr) <- indgrow lxp bxp ir off bn ms;
        If (addr_eq_dec v 0) {
          Ret ^(ms, Err ENOSPCBLOCK)
        } else {
          Ret ^(ms, OK (upd_irec ir (S len) indptr dindptr tindptr (IRBlocks ir)))
        }
      }
    }.

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
    rewrite rep_piff_indirect in * by omega.
    unfold rep_indirect, indrep in *. destruct_lifts.
    hoare; match goal with
    | [H : context [indrep_n_tree _ _ _ ?L] |- _ < length ?L] =>
      rewrite indrep_n_length_pimpl with (l := L) in H; destruct_lift H; omega
    | [ |- pimpl _ _] => cancel
    | [|- ?H] => idtac H
    end.
    all : substl l.
    all : repeat rewrite selN_app2 by omega.
    all : repeat rewrite selN_firstn by omega.
    all : repeat rewrite skipn_selN.
    all : repeat (congruence || omega || f_equal).
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

    unfold rep, indrep in Hx. destruct_lifts.
    hoare; match goal with
    | [H : context [indrep_n_tree _ _ _ ?L] |- _ < length ?L] =>
      rewrite indrep_n_length_pimpl with (l := L) in H; destruct_lift H; omega
    | [ |- pimpl _ _] => cancel
    | [|- ?H] => idtac H
    end.
    rewrite app_assoc with (l := firstn _ _).
    rewrite <- firstn_sum_split. rewrite firstn_skipn.
    congruence.
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

    rewrite arrayN_isolate with (i := 0) by omega.
    unfold IndSig.RAStart; rewrite Nat.add_0_r.
    rewrite skipn_oob by omega; simpl.
    instantiate (2 := ($0, nil)).
    rewrite synced_list_selN; cancel.
  Qed.

  Hint Rewrite cuttail_length : core.
  Hint Rewrite upd_len_get_len upd_len_get_ind upd_len_get_dind upd_len_get_tind upd_len_get_blk upd_len_get_iattr : core.
  Hint Rewrite upd_irec_get_len upd_irec_get_ind upd_irec_get_dind upd_irec_get_tind upd_irec_get_blk upd_irec_get_iattr : core.
  Local Hint Resolve upd_len_get_iattr upd_irec_get_iattr.

  Theorem upd_len_indrep : forall bxp ir l n,
    indrep bxp ir l <=p=> indrep bxp (upd_len ir n) l.
  Proof.
    intros.
    unfold indrep. autorewrite with core. auto.
  Qed.

  Theorem upd_len_direct_indrep : forall bxp ir l n b,
    indrep bxp ir l <=p=> indrep bxp (upd_irec ir n (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) b) l.
  Proof.
    intros.
    unfold indrep. autorewrite with core. auto.
    eapply get_ind_goodSize.
    eapply get_dind_goodSize.
    eapply get_tind_goodSize.
  Qed.

  Theorem indshrink_helper_ok : forall lxp bxp bn nl indlvl ms,
    let start := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp bn l * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, r)  exists m' freelist' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp r l' * BALLOC.rep bxp freelist') ]]] *
           [[ l' = upd_range l (nl - start) (length l - (nl - start)) $0 ]] * [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indshrink_helper indlvl lxp bxp bn nl ms.
  Proof.
    unfold indshrink_helper.
    prestep. norml.
    rewrite indrep_n_length_pimpl in *. destruct_lifts.
    hoare.
    replace (_ - (_ - _)) with 0 by omega. rewrite upd_range_0. auto.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indshrink_helper _ _ _ _ _ _ ) _) => apply indshrink_helper_ok : prog.

  Theorem indshrink_ok : forall lxp bxp ir nl ms,
    {< F Fm m0 m l0 l1 l2 freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm * [[ nl <= length (l0 ++ l1 ++ l2) ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp (IRTindPtr ir) l2 * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, indptr', dindptr', tindptr')
           exists m' freelist' l0' l1' l2',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp indptr' l0' *
                            indrep_n_tree 1 bxp dindptr' l1' *
                            indrep_n_tree 2 bxp tindptr' l2' * BALLOC.rep bxp freelist') ]]] *
           [[ l0' ++ l1' ++ l2' = upd_range (l0 ++ l1 ++ l2) nl (length (l0 ++ l1 ++ l2) - nl) $0 ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indshrink lxp bxp ir nl ms.
  Proof.
    unfold indshrink.
    hoare.
    repeat rewrite app_length in *.
    indrep_n_tree_extract_lengths.
    autorewrite with core.
    repeat rewrite upd_range_eq_app_firstn_repeat by (repeat rewrite app_length; omega).
    destruct (le_dec nl NIndirect);
    destruct (le_dec nl (NIndirect + NIndirect * NIndirect)); try omega.
    all : repeat match goal with
      | [|- context [?a - ?b] ] => replace (a - b) with 0 by omega
      | [|- context [firstn ?x ?l'] ] => rewrite firstn_oob with (n := x) (l := l') by omega
      | [|- context [firstn ?x ?l'] ] => rewrite firstn_app_le with (n := x) by omega
      | [|- context [firstn ?x ?l'] ] => rewrite firstn_app_l with (n := x) by omega
    end; repeat rewrite <- app_assoc; simpl; autorewrite with core; repeat rewrite repeat_app.
    all : repeat rewrite app_length; solve [repeat (omega || f_equal)].
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indshrink _ _ _ _ _) _) => apply indshrink_ok : prog.

  Theorem shrink_ok : forall lxp bxp ir nr ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, r)  exists m' freelist' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp r l' * BALLOC.rep bxp freelist') ]]] *
           exists ind dind tind dirl, [[ r = upd_irec ir ((IRLen ir) - nr) ind dind tind dirl ]] *
           [[ l' = firstn (IRLen ir - nr) l ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} shrink lxp bxp ir nr ms.
  Proof.
    unfold shrink.
    prestep; norml.
    denote rep as Hx. unfold rep in Hx. destruct_lifts.
    cancel.
    + (* case 1: all in direct blocks *)
      step. unfold rep.
      autorewrite with core. cancel.
      - apply upd_len_direct_indrep.
      - rewrite min_l by omega. omega.
      - rewrite upd_range_length; eauto.
      - rewrite min_l by omega.
        substl l at 1. rewrite firstn_firstn, min_l by omega.
        rewrite firstn_app_l by omega.
        rewrite firstn_app_l by ( rewrite upd_range_length; omega ).
        rewrite firstn_upd_range by omega.
        reflexivity.
      - rewrite min_l by omega.
        rewrite skipn_app_l by ( rewrite upd_range_length; omega ).
        rewrite skipn_app_l in * by omega.
        eapply list_same_app_both; eauto.
        rewrite upd_range_eq_upd_range' by omega; unfold upd_range'.
        rewrite skipn_app_r_ge by ( rewrite firstn_length; rewrite min_l by omega; auto ).
        eapply list_same_skipn.
        eapply list_same_app_both; try apply list_same_repeat.
        eapply list_same_skipn_ge.
        2: denote list_same as Hls; apply list_same_app_l in Hls; eauto.
        omega.
      - apply le_ndirect_goodSize. omega.
    + (* case 2 : indirect blocks *)
      unfold indrep in *.
      hoare.
      - repeat rewrite app_length.
        indrep_n_tree_extract_lengths. omega.
      - unfold rep, indrep. autorewrite with core; auto.
        cancel; rewrite mult_1_r in *.
        rewrite indrep_n_length_pimpl with (indlvl := 0).
        rewrite indrep_n_length_pimpl with (indlvl := 1).
        rewrite indrep_n_length_pimpl with (indlvl := 2). cancel. rewrite mult_1_r in *.
        substl (NIndirect * NIndirect). substl NIndirect.
        rewrite firstn_app. rewrite skipn_app_r. repeat rewrite skipn_app. rewrite firstn_app.
        cancel.
        all : try rewrite upd_range_length.
        all : auto.
        all : try rewrite min_l by omega; try omega.
        all : indrep_n_tree_extract_lengths.
        substl l.
        rewrite firstn_firstn, min_l by omega.
        destruct (le_dec (IRLen ir - nr) NDirect).
        {
          rewrite firstn_app_l by omega.
          rewrite firstn_app_l by ( rewrite upd_range_length; omega ).
          rewrite firstn_upd_range by omega.
          auto.
        }
        {
          rewrite not_le_minus_0 with (n := NDirect) by omega.
          rewrite upd_range_0.

          match goal with [H : _ ++ _ = _ |- _] => rewrite H end.
          repeat rewrite firstn_app_split. f_equal.
          rewrite firstn_upd_range by (repeat rewrite app_length; omega). f_equal.
          rewrite <- skipn_skipn'.
          repeat match goal with [|- ?x = _] =>
            erewrite <- firstn_skipn with (l := x) at 1; f_equal end.
        }
        match goal with [H : _ ++ _ = _ |- _] => rewrite H end.
        destruct (le_dec (IRLen ir - nr) NDirect).
        {
          rewrite skipn_app_l by ( rewrite upd_range_length; omega ).
          apply list_same_app_both.

          eapply list_same_skipn_upd_range_mid; [ | omega ].
          replace (IRLen ir - nr + (NDirect - (IRLen ir - nr))) with NDirect by omega.
          rewrite skipn_oob by omega. constructor.

          replace (IRLen ir - nr - NDirect) with 0 by omega.
          rewrite upd_range_eq_upd_range' by omega; unfold upd_range'; simpl.
          eapply list_same_app_both.
          eapply list_same_repeat.

          rewrite skipn_oob; [ constructor | ].
          omega.
        }
        {
          replace (NDirect - (IRLen ir - nr)) with 0 by omega; rewrite upd_range_0.
          denote list_same as Hls.
          rewrite skipn_app_r_ge by omega.
          rewrite skipn_app_r_ge in Hls by omega.
          replace (length (IRBlocks ir)) with (NDirect) by omega.
          eapply list_same_skipn_upd_range_tail.
        }
        apply le_nblocks_goodSize. simpl. rewrite mult_1_r. omega.
    Grab Existential Variables.
    all: eauto.
  Qed.

  Theorem indgrow_ok : forall lxp bxp ir off bn ms,
    {< F Fm m0 m l0 l1 l2 freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ off < NBlocks - NDirect ]] * [[ bn <> $0 ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp (IRTindPtr ir) l2 * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, v, indptr', dindptr', tindptr')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           ([[ v = 0 ]] \/ [[ v <> 0 ]] *
           exists freelist' l0' l1' l2',
           [[ updN (l0 ++ l1 ++ l2) off bn = l0' ++ l1' ++ l2' ]] *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp indptr' l0' *
                            indrep_n_tree 1 bxp dindptr' l1' *
                            indrep_n_tree 2 bxp tindptr' l2' * BALLOC.rep bxp freelist') ]]] *
           [[ incl freelist' freelist ]])
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} indgrow lxp bxp ir off bn ms.
  Proof.
    unfold indgrow. prestep. norml.
    indrep_n_tree_extract_lengths.
    hoare.
    all : or_r; cancel.
    all : match goal with
          | [|- _ = _ ] =>
            repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence
          | [H : ?bn = $ 0 -> False, H2 : ?a = 0 |- False ] =>
              rewrite H2 in *; rewrite indrep_n_tree_0 in *; destruct_lifts;
              apply H; eapply repeat_eq_updN; [> | eauto];
              rewrite mult_1_r; omega
          end.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indgrow _ _ _ _ _ _) _) => apply indgrow_ok : prog.

  Theorem grow_ok : forall lxp bxp ir bn ms,
    {< F Fm m0 m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ length l < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp ir l * BALLOC.rep bxp freelist) ]]]
    POST:hm' RET:^(ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' \/
           exists freelist' ir',
           [[ r = OK ir' ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
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
    unfold indrep.
    intros m' H'. pred_apply. autorewrite with core. cancel.
    all : auto.
    substl l at 1. substl (length l).
    apply firstn_app_updN_eq; omega.
    rewrite skipN_updN' by omega.
    eapply list_same_skipn_ge; try eassumption. omega.
    autorewrite with core lists; auto.

    (* update indirect blocks *)
    step.
    + (* write 0 block *)
      unfold rep in *. destruct_lifts.
      rewrite indrep_length_pimpl in *. unfold indrep in *. destruct_lifts.
      indrep_n_tree_extract_lengths.
      hoare.
      rewrite <- skipn_skipn' in *. repeat rewrite firstn_skipn in *.
      indrep_n_tree_extract_lengths.
      or_r; cancel; autorewrite with core; (cancel || auto).
      rewrite <- skipn_skipn'.
      cancel.
      all : try rewrite app_length; simpl; try omega.
      - apply le_nblocks_goodSize. simpl. rewrite mult_1_r. omega.
      - substl l at 1.
        rewrite plus_comm.
        repeat match goal with [|- context [firstn ?a (?b ++ ?c)] ] =>
          rewrite firstn_app_split with (l1 := b); rewrite firstn_oob with (l := b) by omega
        end. rewrite <- app_assoc. f_equal.
        replace (1 + length l - length (IRBlocks ir)) with ((length l - length (IRBlocks ir)) + 1) by omega.
        erewrite firstn_plusone_selN by omega. f_equal. f_equal.
        denote list_same as Hls. rewrite skipn_app_r_ge in Hls by omega.
        eapply list_same_skipn_selN; eauto; omega.
      - eapply list_same_skipn_ge; [ | eassumption ]. omega.
    + (* write nonzero block *)
      unfold rep in *. destruct_lifts.
      rewrite indrep_length_pimpl in *. unfold indrep in *. destruct_lifts.
      indrep_n_tree_extract_lengths.
      hoare.
      - rewrite mult_1_r. omega.
      - rewrite <- skipn_skipn' in *. repeat rewrite firstn_skipn in *.
        indrep_n_tree_extract_lengths.
        or_r. cancel; autorewrite with core.
        rewrite <- skipn_skipn'.
        rewrite firstn_app. rewrite skipn_app_l. rewrite skipn_oob. rewrite app_nil_l.
        rewrite firstn_app. rewrite skipn_app_l. rewrite skipn_oob. rewrite app_nil_l.
        (* using `cancel` raises a Not_found exception here; don't know why *)
        rewrite sep_star_assoc. rewrite sep_star_comm with (p1 := indrep_n_tree 1 _ _ _). cancel_last.
        all : repeat rewrite app_length; try solve [auto | simpl; omega].
       -- apply le_nblocks_goodSize. simpl. rewrite mult_1_r. omega.
       -- substl l at 1. simpl.
          match goal with [H : updN _ _ _ = _ |- _] => rewrite <- H end.
          rewrite plus_comm. erewrite firstn_S_selN.
          repeat rewrite firstn_app_le by omega.
          rewrite firstn_updN_oob by omega. rewrite selN_app2 by omega.
          erewrite eq_trans with (x := _ - _); [> | reflexivity |].
          rewrite selN_updN_eq by omega. reflexivity.
          all : try rewrite app_length, length_updN; omega.
       -- simpl.
          match goal with [H : updN _ _ _ = _ |- _] => rewrite <- H end.
          denote list_same as Hls. rewrite skipn_app_r_ge in Hls by omega.
          rewrite skipn_app_r_ge by omega.
          rewrite skipN_updN' by omega.
          eapply list_same_skipn_ge; [ | eassumption ]. omega.
    Grab Existential Variables.
    all : eauto; exact $0.
  Qed.

  Hint Extern 1 ({{_}} Bind (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _) _) => apply grow_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.

  Theorem xform_rep : forall xp ir l,
    crash_xform (rep xp ir l) <=p=> rep xp ir l.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite xform_indrep.
    cancel; eauto.

    cancel.
    xform_normr.
    rewrite crash_xform_exists_comm; cancel.
    xform_normr.
    rewrite xform_indrep.
    cancel; eauto.
  Qed.

End BlockPtr.
