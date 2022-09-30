Require Import Arith.
Require Import Setoid.
Require Import Pred PredCrash.
Require Import Word.
Require Import Prog ProgMonad.
Require Import Hoare.
Require Import BasicProg.
Require Import Omega.
Require Import Lia.
Require Import Log.
Require Import Array.
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import SepAuto.
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
Require Import DiskSet.

Import SyncedMem.
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
      rewrite valulen_is; apply Nat.eqb_eq; compute; reflexivity.
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

   Definition indrep_n_helper (Fs : @pred _ addr_eq_dec bool) bxp ibn iblocks :=
    (if (addr_eq_dec ibn 0)
      then [[ iblocks = repeat $0 NIndirect]] *
           [[ Fs <=p=> emp ]]
      else [[ BALLOCC.bn_valid bxp ibn ]] * IndRec.rep ibn iblocks *
          [[ (Fs <=p=> ibn |->?) ]]
    )%pred.

  (* indlvl = 0 if ibn is the address of an indirect block,
     indlvl = 1 for doubly indirect, etc. *)

  Fixpoint indrep_n_tree indlvl bxp Fs ibn l :=
    (match indlvl with
    | 0 => indrep_n_helper Fs bxp ibn l
    | S indlvl' =>
      exists iblocks Fs' lFs,
        [[ length lFs = length iblocks ]] *
        [[ Fs <=p=> Fs' * pred_fold_left lFs ]] *
        indrep_n_helper Fs' bxp ibn iblocks *
        exists l_part, [[ l = concat l_part ]] *
        listmatch (fun ibn'_fs l' =>
          indrep_n_tree indlvl' bxp (snd ibn'_fs) (# (fst ibn'_fs)) l') (combine iblocks lFs) l_part
    end)%pred.

  Hint Extern 0 (okToUnify (indrep_n_helper _ _ _ _) (indrep_n_helper _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (indrep_n_tree _ _ _ _ _) (indrep_n_tree _ _ _ _ _ )) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (listmatch _ ?a _) (listmatch _ ?a _)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (listmatch _ _ ?b) (listmatch _ _ ?b)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (listmatch _ (combine ?a _) _) (listmatch _ (combine ?a _) _)) => constructor : okToUnify.

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
    exact Nat.div_1_r.
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
  Local Hint Extern 1 (?a <= roundup ?a ?b) => apply roundup_ge; mult_nonzero.
  Local Hint Extern 1 (?a mod ?b < ?b) => apply Nat.mod_upper_bound; mult_nonzero.
  Local Hint Resolve roundup_le.

  Ltac incl_solve := match goal with
    | [|- incl ?a ?a ] => apply incl_refl
    | [|- incl (remove _ _ ?l) ?l ] => apply incl_remove
    | [|- incl ?l (_ :: ?l)] => apply incl_tl; solve [incl_solve]
    | [H : incl ?a ?b |- incl ?a ?c ] => eapply incl_tran; [> apply H|]; solve [incl_solve]
    | [H : incl ?b ?c |- incl ?a ?c ] => eapply incl_tran; [> |apply H]; solve [incl_solve]
  end.

  Local Hint Extern 1 (incl ?a ?b) => incl_solve.

  Ltac psubst :=
    repeat match goal with p: pred |- _ =>
      match goal with
      | H: p <=p=> _ |- _ =>
        rewrite H in *; clear H; clear p
      | H: _ <=p=> p |- _ =>
        rewrite <- H in *; clear H; clear p
      end
    end.

  Theorem indrep_n_helper_valid : forall bxp bn Fs l,
    bn <> 0 -> indrep_n_helper Fs bxp bn l <=p=> [[ BALLOCC.bn_valid bxp bn ]] * IndRec.rep bn l * [[ (Fs <=p=> bn |->?) ]].
  Proof.
    intros. unfold indrep_n_helper.
    destruct addr_eq_dec; try congruence.
    split; cancel; eauto.
  Qed.

  Theorem indrep_n_tree_valid : forall indlvl bxp Fs ir l,
    ir <> 0 -> indrep_n_tree indlvl bxp Fs ir l <=p=> indrep_n_tree indlvl bxp Fs ir l * [[ BALLOCC.bn_valid bxp ir ]].
  Proof.
    destruct indlvl; intros; simpl.
    repeat rewrite indrep_n_helper_valid by auto. split; cancel; eauto.
    split; intros m' H'; destruct_lift H'; pred_apply; cancel.
    rewrite indrep_n_helper_valid in * by auto.
    destruct_lifts. auto.
  Qed.

  Lemma indrep_n_helper_0 : forall Fs bxp l,
    indrep_n_helper Fs bxp 0 l <=p=> [[ l = repeat $0 NIndirect ]] * [[ Fs <=p=> emp ]].
  Proof.
    unfold indrep_n_helper; intros; split; cancel.
  Qed.

  Lemma indrep_n_helper_0' : forall bxp l,
    indrep_n_helper emp bxp 0 l <=p=> [[ l = repeat $0 NIndirect ]].
  Proof.
    unfold indrep_n_helper; intros; split; cancel.
  Qed.

  Lemma pred_fold_left_Forall_emp: forall AT AEQ V (l : list (@pred AT AEQ V)),
    Forall (fun x => x <=p=> emp) l ->
    pred_fold_left l <=p=> emp.
  Proof.
    unfold pred_fold_left.
    destruct l; auto; intros.
    inversion H; subst.
    clear H.
    generalize dependent p.
    induction l; cbn; intros.
    auto.
    inversion H3; subst.
    apply IHl; auto.
    rewrite H2.
    rewrite H1.
    split; cancel.
  Qed.

  Lemma pred_fold_left_cons: forall AT AEQ V (l : list (@pred AT AEQ V)) x,
    pred_fold_left (x :: l) <=p=> x * pred_fold_left l.
  Proof.
    intros.
    destruct l; cbn.
    split; cancel.
    generalize dependent p.
    generalize dependent x.
    induction l; cbn; intros.
    split; cancel.
    rewrite IHl.
    rewrite IHl.
    split; cancel.
  Qed.

  Lemma pred_fold_left_repeat_emp: forall AT AEQ V n,
    pred_fold_left (repeat (@emp AT AEQ V) n) <=p=> emp.
  Proof.
    intros.
    rewrite pred_fold_left_Forall_emp; auto.
    auto using Forall_repeat.
  Qed.

  Lemma pred_fold_left_app: forall AT AEQ V (l l' : list (@pred AT AEQ V)),
    pred_fold_left (l ++ l') <=p=> pred_fold_left l * pred_fold_left l'.
  Proof.
    induction l; intros.
    split; cancel.
    intros.
    cbn [app].
    repeat rewrite pred_fold_left_cons.
    rewrite IHl.
    split; cancel.
  Qed.

  Lemma pred_fold_left_selN_removeN: forall AT AEQ V (l : list (@pred AT AEQ V)) i,
    pred_fold_left l <=p=> (selN l i emp) * pred_fold_left (removeN l i).
  Proof.
    unfold removeN.
    intros.
    destruct (lt_dec i (length l)).
    rewrite <- firstn_skipn with (l := l) at 1.
    repeat rewrite pred_fold_left_app.
    erewrite skipn_selN_skipn by eauto.
    rewrite pred_fold_left_cons.
    split; cancel.
    rewrite selN_oob, firstn_oob, skipn_oob by omega.
    rewrite app_nil_r.
    split; cancel.
  Qed.

  Lemma pred_fold_left_updN_removeN: forall AT AEQ V l (p : @pred AT AEQ V) i,
    i < length l ->
    pred_fold_left (updN l i p) <=p=> pred_fold_left (removeN l i) * p.
  Proof.
    intros.
    rewrite pred_fold_left_selN_removeN.
    rewrite selN_updN_eq, removeN_updN by auto.
    split; cancel.
  Qed.

  Lemma in_combine_repeat_l : forall A B (a : A) n (b : list B) x,
    In x (combine (repeat a n) b) ->
    fst x = a.
  Proof.
    induction n; cbn; intuition.
    destruct b; cbn in *; intuition eauto.
    subst; auto.
  Qed.

  Lemma listmatch_combine_l_length: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V) F m
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    (F * listmatch prd (combine a b) c)%pred m -> length a = length c /\ length b = length c.
  Proof.
    intros.
    rewrite listmatch_length_pimpl in H0.
    destruct_lifts.
    rewrite combine_length in *.
    rewrite Nat.min_l in * by omega.
    omega.
  Qed.

  Lemma listmatch_combine_l_length_l: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V) F m
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    (F * listmatch prd (combine a b) c)%pred m -> length a = length c.
  Proof.
    intros.
    eapply listmatch_combine_l_length with (a := a) (b := b).
    auto.
    pred_apply' H0; cancel.
  Qed.

  Lemma listmatch_combine_l_length_r: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V) F m
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    (F * listmatch prd (combine a b) c)%pred m -> length b = length c.
  Proof.
    intros.
    eapply listmatch_combine_l_length with (a := a) (b := b).
    auto.
    pred_apply' H0; cancel.
  Qed.

  Lemma listmatch_combine_l_length_pimpl: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V)
    (a : list A) (b : list B) (c : list C),
    length a = length b ->
    listmatch prd (combine a b) c =p=> [[ length a = length c /\ length b = length c ]]
      * listmatch prd (combine a b) c.
  Proof.
    intros.
    rewrite listmatch_length_pimpl at 1.
    rewrite combine_length.
    substl (length a).
    rewrite Nat.min_id.
    cancel.
  Qed.

  Theorem indrep_n_tree_0 : forall indlvl bxp Fs l,
    indrep_n_tree indlvl bxp Fs 0 l <=p=> [[ l = repeat $0 (NIndirect ^ S indlvl)]] * [[ Fs <=p=> emp ]].
  Proof.
    induction indlvl; simpl; intros.
    rewrite mult_1_r, indrep_n_helper_0; split; cancel.
    setoid_rewrite indrep_n_helper_0.
    split.
    - norml.
      cbv [stars pred_fold_left fold_left].
      rewrite listmatch_combine_l_length_pimpl by auto.
      rewrite listmatch_lift_r.
      rewrite listmatch_lift_l.
      rewrite listmatch_emp. cancel.
      erewrite concat_hom_repeat; eauto.
      autorewrite with lists in *|-.
      repeat f_equal; eauto.
      psubst.
      denote combine as Hc.
      rewrite Forall_combine_r in Hc.
      rewrite pred_fold_left_Forall_emp by eauto.
      split; cancel.
      auto.
      instantiate (1 := fun x => (snd x) <=p=> emp).
      cbn; intros. reflexivity.
      instantiate (1 := fun _ _ => emp).
      cancel.
      cbn beta; intros.
      apply piff_refl.
      cbn beta. intros.
      erewrite in_combine_repeat_l by eauto.
      rewrite IHindlvl. split; cancel.
    - norm.
      cancel.
      eassign (repeat (@emp _ addr_eq_dec bool) NIndirect).
      rewrite listmatch_emp_piff. cancel.
      rewrite combine_repeat.
      repeat rewrite repeat_length. reflexivity.
      rewrite combine_repeat.
      intros x y; intros.
      erewrite repeat_spec with (y := x) by eauto.
      erewrite repeat_spec with (y := y) by eauto.
      cbn.
      repeat match goal with H: In _ _ |- _ => eapply repeat_spec in H end.
      subst.
      eassign (@natToWord addrlen 0).
      rewrite IHindlvl.
      split; cancel.
      autorewrite with lists.
      rewrite pred_fold_left_repeat_emp.
      intuition eauto.
      split; cancel.
      erewrite concat_hom_repeat.
      2: eapply Forall_repeat; reflexivity.
      autorewrite with lists; eauto.
  Qed.

  Lemma listmatch_indrep_n_tree_empty': forall indlvl n bxp,
    listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y)
      (combine (repeat (@natToWord addrlen 0) n) (repeat emp n)) (repeat (repeat $0 (NIndirect ^ (S indlvl))) n) <=p=> emp.
  Proof.
    intros.
    rewrite listmatch_emp_piff.
    autorewrite with lists; auto.
    split; cancel.
    intros.
    rewrite combine_repeat in *.
    eapply repeat_spec in H.
    eapply repeat_spec in H0.
    subst.
    rewrite indrep_n_tree_0.
    split; cancel.
  Qed.

  Lemma listmatch_indrep_n_tree_empty'': forall indlvl n fsl l bxp,
    length fsl = n ->
    listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y)
      (combine (repeat (@natToWord addrlen 0) n) fsl) l =p=> [[ pred_fold_left fsl <=p=> emp ]] *
        [[ l = (repeat (repeat $0 (NIndirect ^ (S indlvl))) n) ]].
  Proof.
    cbn -[Nat.div]; intros.
    rewrite listmatch_lift_l with (P := fun x => snd x <=p=> emp).
    erewrite listmatch_lift_r with (P := fun x => x = repeat $0 (NIndirect ^ (S indlvl))).
    rewrite listmatch_emp_piff.
    autorewrite with lists.
    rewrite Nat.min_l by omega.
    do 2 intro; destruct_lifts.
    - repeat eapply sep_star_lift_apply'; unfold lift_empty; intuition.
      rewrite Forall_combine_r in H1.
      rewrite pred_fold_left_Forall_emp; eauto.
      autorewrite with lists; eauto.
      reflexivity.
      eapply list_selN_ext.
      autorewrite with lists; auto.
      intros.
      rewrite Forall_forall in *.
      rewrite H2 with (x := selN l pos nil).
      rewrite repeat_selN; auto; omega.
      eapply in_selN; auto.
    - instantiate (1 := fun x y => emp).
      auto.
    - instantiate (1 := fun x y => ([[ y = repeat $0 (NIndirect ^ (S indlvl)) ]])%pred).
      split; cancel.
    - intros.
      erewrite in_combine_repeat_l in * by eauto.
      rewrite indrep_n_tree_0.
      split; cancel.
  Qed.

  Lemma listmatch_indrep_n_tree_empty: forall indlvl bxp,
    let iblocks := (repeat $0 NIndirect) in
    indrep_n_helper emp bxp 0 iblocks *
    listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y)
      (combine iblocks (repeat emp NIndirect)) (repeat (repeat $0 (NIndirect ^ (S indlvl))) NIndirect) <=p=> emp.
  Proof.
    cbn -[Nat.div]; intros.
    rewrite listmatch_indrep_n_tree_empty'.
    split; cancel.
  Qed.

  Theorem indrep_n_helper_bxp_switch : forall Fs bxp bxp' ir iblocks,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep_n_helper Fs bxp ir iblocks <=p=> indrep_n_helper Fs bxp' ir iblocks.
  Proof.
    intros. unfold indrep_n_helper, BALLOCC.bn_valid. rewrite H. reflexivity.
  Qed.

  Theorem indrep_n_tree_bxp_switch : forall bxp bxp' indlvl Fs ir l,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep_n_tree indlvl bxp Fs ir l <=p=> indrep_n_tree indlvl bxp' Fs ir l.
  Proof.
    induction indlvl; intros; simpl.
    rewrite indrep_n_helper_bxp_switch by eassumption.
    split; cancel.
    split; cancel; eauto; rewrite indrep_n_helper_bxp_switch.
    all : try rewrite listmatch_piff_replace; try cancel; auto.
    all : intros x; destruct x; intros; simpl; rewrite IHindlvl; auto.
  Qed.

  Theorem indrep_n_helper_sm_sync_invariant : forall Fs bxp ir l m F,
    (F * indrep_n_helper Fs bxp ir l)%pred m ->
    sm_sync_invariant Fs.
  Proof.
    unfold indrep_n_helper.
    intros.
    destruct addr_eq_dec.
    destruct_lifts.
    erewrite sm_sync_invariant_piff by eauto.
    apply sm_sync_invariant_emp.
    destruct_lifts.
    erewrite sm_sync_invariant_piff by eauto.
    apply sm_sync_invariant_exis_ptsto.
  Qed.

  Lemma sm_sync_invariant_pred_fold_left: forall l,
    Forall sm_sync_invariant l ->
    sm_sync_invariant (pred_fold_left l).
  Proof.
    intros.
    unfold pred_fold_left.
    destruct l; cbn.
    auto using sm_sync_invariant_emp.
    inversion H; subst.
    clear H.
    generalize dependent p.
    generalize dependent l.
    induction l; cbn; intros.
    auto.
    inversion H3; subst.
    apply IHl; auto.
  Qed.

  Theorem indrep_n_tree_sm_sync_invariant : forall bxp indlvl Fs ir l F m,
    (F * indrep_n_tree indlvl bxp Fs ir l)%pred m ->
    sm_sync_invariant Fs.
  Proof.
    induction indlvl; cbn; intros.
    eapply indrep_n_helper_sm_sync_invariant.
    pred_apply' H; cancel.
    destruct_lifts.
    erewrite sm_sync_invariant_piff by eauto.
    apply sm_sync_invariant_sep_star.
    eapply indrep_n_helper_sm_sync_invariant.
    pred_apply' H; cancel.
    apply sm_sync_invariant_pred_fold_left.
    rewrite listmatch_lift_l in H.
    destruct_lifts.
    eapply Forall_combine_r; try eassumption.
    auto.
    intros; split; intro H'; apply H'.
    intros.
    split.
    intros m' H'.
    apply sep_star_comm.
    apply sep_star_lift_apply'.
    exact H'.
    eapply IHindlvl with (m := m') (F := emp) (ir := # (fst x)).
    pred_apply; cancel.
    cancel.
  Qed.

  Theorem listpred_indrep_n_tree_0 : forall indlvl bxp Fs l,
    listpred (fun l' => indrep_n_tree indlvl bxp Fs 0 l') l <=p=>
      [[ Forall (fun x => x = repeat $0 (NIndirect ^ S indlvl) /\ (Fs <=p=> emp))%type l ]].
  Proof.
    induction l; intros.
    - split; cancel. constructor.
    - simpl. rewrite IHl.
      rewrite indrep_n_tree_0.
      split; cancel.
      all : match goal with [H : Forall _ _ |- _] => inversion H; intuition end.
  Qed.

  Lemma indrep_n_helper_length : forall F Fs bxp ibn l m,
    (F * indrep_n_helper Fs bxp ibn l)%pred m -> length l = NIndirect.
  Proof.
    unfold indrep_n_helper, IndRec.rep, IndRec.items_valid.
    intros; destruct addr_eq_dec; destruct_lift H; unfold lift_empty in *;
    intuition; subst; autorewrite with lists; auto.
    unfold IndRec.Defs.item in *; simpl in *. omega.
  Qed.

  Lemma indrep_n_helper_length_piff : forall Fs bxp ibn l,
    indrep_n_helper Fs bxp ibn l <=p=> indrep_n_helper Fs bxp ibn l * [[ length l = NIndirect ]].
  Proof.
    intros.
    split.
    - intros m H.
      pred_apply; cancel.
      eapply indrep_n_helper_length with (m := m).
      pred_apply; cancel.
    - cancel.
  Qed.

  Lemma indrep_n_length_pimpl : forall indlvl bxp ibn Fs l,
    indrep_n_tree indlvl bxp Fs ibn l <=p=>
    [[ length l = NIndirect ^ (S indlvl) ]] * indrep_n_tree indlvl bxp Fs ibn l.
  Proof.
    induction indlvl; simpl; intros.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    erewrite indrep_n_helper_length with (m := m); eauto; try omega.
    pred_apply; cancel.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    rewrite indrep_n_helper_length_piff, listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_lift_r in H; destruct_lift H.
    erewrite concat_hom_length; eauto.
    rewrite combine_length_eq in * by congruence.
    eassign (NIndirect ^ S indlvl).
    f_equal; omega.
    intros x y; destruct x.
    intros.
    rewrite IHindlvl.
    instantiate (1 := fun x y => indrep_n_tree indlvl bxp (snd x) (# (fst x)) y).
    split; cancel.
  Qed.

  Lemma listmatch_indrep_n_tree_forall_length : forall indlvl bxp (l1 : list (waddr * _)) l2,
    listmatch (fun a l' => indrep_n_tree indlvl bxp (snd a) # (fst a) l') l1 l2 <=p=>
    listmatch (fun a l' => indrep_n_tree indlvl bxp (snd a) # (fst a) l') l1 l2 *
    [[Forall (fun sublist : list waddr => (length sublist = NIndirect * NIndirect ^ indlvl)%nat) l2]].
  Proof.
    intros.
    split; [> | cancel].
    rewrite listmatch_lift_r at 1. cancel. eauto.
    intros.
    destruct x.
    rewrite indrep_n_length_pimpl. split; cancel.
  Qed.

  Local Hint Extern 1 (Forall (fun x => length x = _) _) => match goal with
    | [H : context [listmatch (fun x y => indrep_n_tree _ _ (snd x) # (fst x) y) _ ?l]
        |- Forall (fun x => length x = _) ?l ] =>
          rewrite listmatch_indrep_n_tree_forall_length with (l2 := l) in H; destruct_lift H; solve [eassumption]
    | [|- Forall _ (upd_range ?l _ _ _)] => apply forall_upd_range; autorewrite with lists; eauto
  end.

  Theorem indrep_n_helper_pts_piff : forall Fs bxp ir l,
    ir <> 0 -> indrep_n_helper Fs bxp ir l <=p=> [[ length l = NIndirect ]] *
                [[ BALLOCC.bn_valid bxp ir ]] * [[ Fs <=p=> ir |->? ]] *
                ir |-> (IndRec.Defs.block2val l, []).
  Proof.
    intros.
    unfold indrep_n_helper, IndRec.rep. destruct addr_eq_dec; try omega.
    unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
    rewrite mult_1_l. unfold Rec.well_formed. simpl.
    split; cancel;
    rewrite IndRec.Defs.ipack_one by (unfold IndRec.Defs.item in *; auto).
    all : cancel.
  Qed.

  Lemma indrep_n_tree_balloc_goodSize: forall F1 F2 bxp freelist ms indlvl Fs ir l m1 m2,
    (F1 * BALLOCC.rep bxp freelist ms)%pred m1 ->
     (F2 * indrep_n_tree indlvl bxp Fs ir l)%pred m2 ->
      goodSize addrlen ir.
  Proof.
    intros.
    destruct (addr_eq_dec ir 0); subst.
    apply DiskLogHash.PaddedLog.goodSize_0.
    rewrite indrep_n_tree_valid in * by auto.
    destruct_lifts.
    eapply BALLOCC.bn_valid_goodSize; eauto.
  Qed.

  Lemma indrep_n_tree_length: forall indlvl F ir l1 l2 lfs bxp Fs m,
    length lfs = NIndirect ->
    (F *
    indrep_n_helper Fs bxp ir l1 *
    listmatch
     (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine l1 lfs) l2)%pred m->
     length (concat l2) = NIndirect * (NIndirect ^ (S indlvl)).
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff in H0.
    rewrite listmatch_length_pimpl in H0.
    erewrite listmatch_lift_r in H0.
    destruct_lift H0.
    rewrite combine_length_eq in * by congruence.
    erewrite concat_hom_length; eauto.
    f_equal; omega.

    intros.
    destruct_lift H0.
    instantiate (1 := fun x y => indrep_n_tree indlvl bxp (snd x) (# (fst x)) y).
    rewrite indrep_n_length_pimpl. split; cancel.
  Qed.

  Lemma indrep_n_indlist_forall_length : forall F indlvl Fs bxp ir l1 fsl l2 m,
    length fsl = NIndirect ->
    ((F ✶ indrep_n_helper Fs bxp ir l1)
        ✶ listmatch
            (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine l1 fsl) l2)%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff, listmatch_lift_r in H0.
    destruct_lifts; eauto.
    intros x; intros.
    rewrite indrep_n_length_pimpl.
    split; cancel.
  Qed.

  Lemma indrep_n_indlist_forall_length' : forall F F' indlvl Fs bxp ir fsl l1 l2 m,
    length fsl = NIndirect ->
    (((F ✶ indrep_n_helper Fs bxp ir l1)
        ✶ listmatch
            (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine l1 fsl) l2) * F')%pred m ->
    Forall (fun sublist : list waddr => length sublist = NIndirect * NIndirect ^ indlvl) l2.
  Proof.
    intros. eapply indrep_n_indlist_forall_length.
    2: eassign m; pred_apply; cancel.
    auto.
  Qed.

  Lemma indrep_index_bound_helper : forall Fm Fs off indlvl bxp bn iblocks fsl l_part m,
      off < length (concat l_part) ->
      length fsl = NIndirect ->
      ((Fm * indrep_n_helper Fs bxp bn iblocks) *
       listmatch (fun x l' =>
                    indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine iblocks fsl) l_part)%pred m
      -> off / (NIndirect * NIndirect ^ indlvl) < NIndirect.
  Proof.
    intros.
    apply Nat.div_lt_upper_bound; mult_nonzero.
    erewrite indrep_n_tree_length in * by eauto.
    rewrite mult_comm; simpl in *. auto.
  Qed.

  Lemma indrep_index_bound_helper' : forall Fm Fm' off indlvl bxp Fs bn iblocks l_part fsl m,
      off < length (concat l_part) ->
      length fsl = NIndirect ->
    ((Fm * indrep_n_helper Fs bxp bn iblocks) *
          listmatch (fun x (l' : list waddr) =>
            indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine iblocks fsl) l_part *
            Fm')%pred m
    -> off / (NIndirect * NIndirect ^ indlvl) < NIndirect.
  Proof.
    intros.
    eapply indrep_index_bound_helper; eauto.
    eassign m.
    pred_apply; cancel.
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
    rewrite upd_range_upd_range by eauto. f_equal.
    rewrite Nat.mul_sub_distr_r.
    rewrite <- Nat.add_sub_swap. rewrite le_plus_minus_r. auto.
    apply roundup_le. auto.
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



  Theorem xform_indrep_n_helper : forall Fs bxp ir l,
    crash_xform (indrep_n_helper Fs bxp ir l) <=p=> indrep_n_helper Fs bxp ir l.
  Proof.
    unfold indrep_n_helper. intros.
    destruct addr_eq_dec; xform_norm.
    - auto.
    - rewrite IndRec.xform_rep. auto.
  Qed.

  Theorem xform_indrep_n_tree : forall xp indlvl Fs ir l,
    crash_xform (indrep_n_tree indlvl xp Fs ir l) <=p=> indrep_n_tree indlvl xp Fs ir l.
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
        intros. simpl. rewrite IHindlvl.
        all: auto.
  Qed.

  Hint Rewrite Nat.mul_1_r.

  Ltac indrep_n_tree_bound_step := match goal with
    | [ |- _ ] => reflexivity
    | [ |- _ ] => assumption
    | [ |- Forall _ _ ] => auto
    | [ H : context [IndRec.Defs.item] |- _ ] => unfold IndRec.Defs.item in *; simpl Rec.data in *
    | [ |- context [IndRec.Defs.item] ] => unfold IndRec.Defs.item in *; simpl Rec.data in *
    | [ |- context [length (combine ?a ?b)] ] => rewrite combine_length_eq by congruence
    | [ |- _ ] => progress autorewrite with core lists
    | [ |- ?a * ?b = ?c * ?b ] => rewrite Nat.mul_cancel_r by mult_nonzero
    | [ |- ?a * ?b = ?b * ?c ] => rewrite mult_comm with (n := b) (m := c)
    | [ |- ?b * ?a = ?b * ?c ] => rewrite mult_comm with (n := b) (m := a)
    | [ H : ?a < ?b * ?c |- ?a < ?d * ?c] => replace d with b; [ eauto | ]
    | [ H : ?a < ?x |- ?a < ?y ] => replace y with x; [ auto | ]
    | [ H : ?a <= ?x |- ?a <= ?y ] => replace y with x; [ auto | ]
    | [ H : context [indrep_n_tree _ _ _ _ ?l] |- context [length ?l] ] =>
      rewrite indrep_n_tree_length in H; destruct_lift H
    | [ H : context [indrep_n_helper _ _ _ ?l] |- context [length ?l] ] =>
      replace (length l) with NIndirect by (erewrite indrep_n_helper_length; auto; pred_apply' H; cancel)
    | [ |- ?off / ?N < ?N' ] => apply Nat.div_lt_upper_bound; [ mult_nonzero |]
    | [ |- ?off < ?N * NIndirect] => rewrite mult_comm
    | [ |- context [Nat.min ?a ?b] ] => rewrite Nat.min_r by auto
    | [ |- context [Nat.min ?a ?b] ] => rewrite Nat.min_l by auto
    | [ H : ?a + ?b <= ?c |- ?a < ?d ] => eapply lt_le_trans with (m := a + b); [omega |]
    (* try to get an argument to indrep_n_tree or indrep_n_helper *)
    | [ H : context [listmatch ?P (combine ?A ?B) ?C] |- context [length ?C] ] =>
      replace (length C) with (length A) in * by (
        erewrite listmatch_combine_l_length_l with (a := A) (b := B) (c := C) (prd := P); auto;
        pred_apply' H; cancel)
    | [ H : context [listmatch ?P (combine ?A ?B) ?c] |- context [length ?C] ] =>
      replace (length c) with (length B) in * by (
        erewrite listmatch_combine_l_length_r with (a := A) (b := B) (c := C) (prd := P); auto;
        pred_apply' H; cancel)
    | [ H : context [listmatch _ (combine ?A ?B) _] |- context [length ?B] ] =>
      replace (length B) with (length A) by auto

    | [ H : context [listmatch _ ?A ?b] |- context [length ?b] ] =>
      replace (length b) with (length A) in * by (
        erewrite listmatch_length with (a := A); auto; pred_apply' H; cancel)
    | [ H : context [listmatch _ ?A ?b], H': context [length ?b] |- _ ] =>
      replace (length b) with (length A) in * by (
        erewrite listmatch_length with (a := A); auto; pred_apply' H; cancel)

    | [ H : context [lift_empty _] |- _ ] => progress destruct_lift H
    | [ |- context [length (concat _)] ] => erewrite concat_hom_length; eauto
    | [ |- context [Nat.min _ _] ] => rewrite min_l by omega
    | [ H: context [Nat.min _ _] |- _ ] => rewrite min_l in H by omega
    | [ |- _ ] => omega
    | [ |- ?a < ?b * ?c ] => rewrite mult_comm; omega
    | [ H : context [length (concat ?l)] |- _ ] => erewrite concat_hom_length in H by eauto
    end.

  Ltac indrep_n_tree_bound :=
    match goal with
    | [l : list _ |- context [?x] ] => is_evar x; unify x l; solve [indrep_n_tree_bound]
    | _ => repeat indrep_n_tree_bound_step
  end.

  Ltac indrep_n_extract := match goal with
    | [|- context [listmatch _ ?l] ] =>
      match goal with [l : list _ |- context [listmatch _ (removeN ?l ?n)] ] =>
        rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try omega; try erewrite snd_pair by eauto
      end
    | [|- context [selN ?l ?n] ] => rewrite listmatch_isolate with (i := n) (a := l);
        autorewrite with lists in *; try omega; try erewrite snd_pair by eauto
    | [|- context [selN ?l ?n] ] => rewrite listmatch_isolate with (i := n) (a := combine l _);
        autorewrite with lists in *; try rewrite selN_combine; try omega; try erewrite snd_pair by eauto;
        cbn [fst snd] in *
    | [H: context [listmatch _ (combine ?l _)] |- context [selN ?l ?n] ] =>
        rewrite listmatch_isolate with (i := n) (a := combine l _) in H;
        autorewrite with lists in *; erewrite ?selN_combine in H; try omega; erewrite ?snd_pair by eauto;
        cbn [fst snd] in *
    | [H: context [listmatch _ _ ?l] |- context [selN ?l ?n] ] =>
        rewrite listmatch_isolate with (i := n) (b := l) in H;
        autorewrite with lists in *; erewrite ?selN_combine in H; try omega; erewrite ?snd_pair by eauto;
        cbn [fst snd] in *
  end.

  Ltac indrep_n_tree_extract_lengths :=
    repeat match goal with [H : context [indrep_n_tree _ _ _ _ ?x] |- _] =>
      match goal with
      | [H' : length ?y = _ |- _] => tryif (unify x y) then fail 1 else fail
      | [|- _] => rewrite indrep_n_length_pimpl with (l := x) in H; destruct_lift H
      end
    end; try rewrite mult_1_r in *.

  Theorem indrep_n_tree_repeat_concat:
    forall indlvl F Fs lfs l1 l2 bxp m,
    length lfs = NIndirect ->
    ((F ✶ indrep_n_helper Fs bxp 0 l1)
     ✶ listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y) (combine l1 lfs) l2)%pred m ->
    concat l2 = repeat $0 (NIndirect * NIndirect ^ S indlvl).
  Proof.
    intros. rewrite indrep_n_helper_0 in *. destruct_lifts.
    rewrite listmatch_length_pimpl in *; autorewrite with lists in *; destruct_lifts.
    rewrite min_l in * by omega.
    erewrite concat_hom_repeat. repeat f_equal; auto.
    rewrite listmatch_lift_r in *. destruct_lifts; eauto.
    intros. instantiate (1 := fun x y => ([[ snd x <=p=> emp ]])%pred).
    erewrite in_combine_repeat_l by eauto.
    rewrite indrep_n_tree_0. split; cancel.
  Qed.

  Theorem indrep_n_tree_repeat_Fs:
    forall indlvl F Fs lfs l1 l2 bxp m,
    length lfs = NIndirect ->
    ((F ✶ indrep_n_helper Fs bxp 0 l1)
     ✶ listmatch (fun x y => indrep_n_tree indlvl bxp (snd x) # (fst x) y) (combine l1 lfs) l2)%pred m ->
    Fs * pred_fold_left lfs <=p=> emp.
  Proof.
    intros. rewrite indrep_n_helper_0 in *. destruct_lifts.
    rewrite listmatch_lift_l in *.
    destruct_lifts.
    rewrite Forall_combine_r in *.
    rewrite pred_fold_left_Forall_emp; eauto.
    psubst; split; cancel.
    autorewrite with lists; auto.
    intros.
    instantiate (1 := fun x => (snd x) <=p=> emp).
    reflexivity.
    intros.
    erewrite in_combine_repeat_l by eauto.
    rewrite roundTrip_0.
    rewrite indrep_n_tree_0 at 1.
    instantiate (1 := fun x y => ([[ y = _ ]])%pred).
    split; cancel.
  Qed.


  Local Hint Extern 1 (BALLOCC.bn_valid _ _) => match goal with
    [H : context [indrep_n_helper _ _ ?ir] |- BALLOCC.bn_valid _ ?ir] =>
    rewrite indrep_n_helper_valid in H by omega; destruct_lift H; auto end.

  Local Hint Extern 1 (goodSize _ _) => match goal with
  | [H: context [indrep_n_tree _ _ _ ?i] |- goodSize _ ?i ] =>
    match goal with H' : context [BALLOCC.rep ?B ?l] |- _ =>
      eapply indrep_n_tree_balloc_goodSize with (bxp := B) (freelist := l); eapply pimpl_apply;
      [| exact H' | | exact H]; cancel
    end
  end.

  Hint Rewrite le_plus_minus_r using auto.
  Local Hint Extern 1 (?a mod ?b < ?b) => apply Nat.mod_bound_pos; mult_nonzero.
  Local Hint Extern 1 (0 < ?n - ?m) => (apply Nat.lt_add_lt_sub_r; simpl; auto).

  Local Hint Resolve repeat_selN'.
  Local Hint Extern 1 (Forall (fun x => length x = _) _) => eapply indrep_n_indlist_forall_length.

  Lemma IndRec_items_valid_repeat : forall bn x,
    bn <> 0 -> IndRec.items_valid bn (repeat x NIndirect).
  Proof.
    unfold IndRec.items_valid, IndSig.RAStart, IndSig.RALen, IndSig.xparams_ok.
    simpl. intros. autorewrite with lists. auto.
  Qed.

  Local Hint Resolve IndRec_items_valid_repeat IndRec.items_valid_updN IndRec.items_valid_upd_range.
  Local Hint Extern 1 (Rec.well_formed _) => unfold Rec.well_formed; cbn.

  Lemma indrep_n_helper_items_valid : forall Fs bxp bn l,
    bn <> 0 ->
    indrep_n_helper Fs bxp bn l <=p=> [[ IndRec.items_valid bn l]] * indrep_n_helper Fs bxp bn l.
  Proof.
    intros.
    rewrite indrep_n_helper_length_piff.
    unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RALen, IndSig.RAStart, IndRec.Defs.item.
    split; cancel.
  Qed.

  Local Hint Extern 1 (IndRec.items_valid _ _) => match goal with
    [H : context [indrep_n_helper _ _ ?bn] |- IndRec.items_valid ?bn _] =>
    rewrite indrep_n_helper_items_valid in H; destruct_lift H end.


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
    {< F Fm Fs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp bn l ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} indget indlvl lxp bn off ms.
  Proof.
    induction indlvl; simpl.
    + repeat safestep; autorewrite with core; eauto.
      rewrite indrep_n_helper_0 in *. destruct_lifts. auto.
      rewrite indrep_n_helper_valid by omega. cancel.
    + repeat safestep; autorewrite with core; try eassumption; clear IHindlvl.
    3: rewrite indrep_n_helper_valid by auto; cancel.
      - erewrite indrep_n_tree_repeat_concat with (m := list2nmem m).
        3: pred_apply; cancel.
        auto.
        indrep_n_tree_bound.
      - indrep_n_tree_bound.
      - rewrite listmatch_isolate with (i := off / (NIndirect ^ S indlvl)) by indrep_n_tree_bound.
        rewrite selN_combine by indrep_n_tree_bound.
        cbn [fst snd]; cancel.
      - match goal with [H : context [indrep_n_helper] |-_] => assert (HH := H) end.
        match goal with |- ?a mod ?n < ?b => replace b with n; auto end.
        rewrite listmatch_extract in HH; autorewrite with lists in HH.
        rewrite indrep_n_length_pimpl in HH.
        destruct_lift HH. eauto.
        indrep_n_tree_bound.
      - apply selN_selN_hom; eauto.
        indrep_n_tree_bound.
      Unshelve.
      all: eauto.
           exact ($0, emp).
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
          r <- ForEach b indbns' (rev indbns)
            Hashmap hm
            Ghost [ F Fm Fs fsl iblocks l_part l bxp crash m0 sm m ]
            Loopvar [ ms r ]
            Invariant
              exists remlen, [[ remlen = length indbns' ]] *
              LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
              [[[ m ::: Fm * indrep_n_helper Fs bxp ir iblocks *
                        listmatch (fun x l' => indrep_n_tree indlvl' bxp (snd x) (# (fst x)) l')
                          (combine iblocks fsl) l_part ]]] *
              [[ r = skipn (remlen * (NIndirect ^ indlvl)) l ]]
            OnCrash crash
            Begin
              let^ (ms, v) <- indread indlvl' lxp (# b) ms;
              Ret ^(ms, v ++ r)
            Rof ^(ms, nil);
            Ret r
      end
    }.

  Theorem indread_ok : forall indlvl lxp bxp ir ms,
  {< F Fm Fs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
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
      - erewrite indrep_n_tree_repeat_concat; eauto. auto.
        indrep_n_tree_bound.
      - rewrite indrep_n_helper_valid by omega. cancel.
      - rewrite firstn_oob by indrep_n_tree_bound.
        autorewrite with list.
        rewrite skipn_oob; auto.
        indrep_n_tree_bound.
      - rewrite firstn_oob in * by indrep_n_tree_bound; subst.
        rewrite rev_eq_iff, rev_app_distr in *; cbn [rev] in *; subst.
        rewrite listmatch_extract.
        rewrite selN_combine.
        rewrite selN_app1.
        rewrite selN_app2.
        rewrite sub_le_eq_0 by reflexivity; cbn [selN].
        cancel.
        all: rewrite indrep_n_helper_length_piff in *; destruct_lifts.
        all : autorewrite with list in *; cbn -[Nat.div] in *; try omega.
        rewrite combine_length_eq; autorewrite with list; cbn; omega.
      - rewrite firstn_oob in * by indrep_n_tree_bound; subst.
        rewrite rev_eq_iff, rev_app_distr in *; cbn [rev] in *; subst.
        rewrite listmatch_length_pimpl in *; destruct_lifts.
        rewrite indrep_n_helper_length_piff in *; destruct_lifts.
        autorewrite with list in *; cbn [length] in *.
        rewrite <- (Nat.mul_1_l (NIndirect * NIndirect ^ indlvl)) at 1.
        rewrite <- Nat.mul_add_distr_r.
        repeat erewrite concat_hom_skipn by eauto.
        erewrite skipn_selN_skipn with (off := length _).
        reflexivity.
        match goal with H: length (combine _ _) = _ |- _ => rename H into Hc end.
        rewrite combine_length_eq in Hc.
        autorewrite with list in *; cbn [length] in *; omega.
        autorewrite with list; cbn [length]. omega.
      - apply LOG.rep_hashmap_subset; eauto.
    Grab Existential Variables.
      all : eauto; split.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indread _ _ _ _ ) _) => apply indread_ok : prog.
  Opaque indread.

  Definition indread_aligned indlvl lxp (indbns : list waddr) ms :=
    ForEach bn rest (rev indbns)
      Hashmap hm
      Ghost [ F Fm l_part fsl bxp crash m0 sm m ]
      Loopvar [ ms r ]
      Invariant
        LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
        [[ length indbns = length fsl ]] *
        [[ r = concat (skipn (length rest) l_part) ]] *
        [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine (rev indbns) (rev fsl)) (rev l_part) ]]]
      OnCrash crash
      Begin
        let^ (ms, blks) <- indread indlvl lxp # bn ms;
        Ret ^(ms, blks ++ r)
      Rof ^(ms, nil).

  Hint Rewrite rev_length rev_involutive rev_app_distr : lists.

  Theorem indread_aligned_ok : forall indlvl lxp indbns ms,
    {< F Fm m0 sm m bxp fsl l_part,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) # (fst x) l) (combine indbns fsl) l_part) ]]] *
           [[ length fsl = length indbns ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = concat l_part ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_aligned indlvl lxp indbns ms.
  Proof.
    unfold indread_aligned.
    step.
    eassign l_part.
    autorewrite with lists core.
    rewrite skipn_oob; auto.
    indrep_n_tree_bound.
    rewrite <- combine_rev by auto.
    rewrite listmatch_rev. cancel.
    assert (length l_part = length fsl) by indrep_n_tree_bound.
    prestep. norml.
    denote app as Hr.
    apply f_equal with (f := @rev _) in Hr.
    autorewrite with lists in Hr; cbn [rev] in Hr; subst.
    autorewrite with lists in *.
    cbn [length] in *.
    denote listmatch as Hl.
    erewrite list_isolate with (l := fsl) (d := emp) in Hl, H by eauto.
    erewrite list_isolate with (l := l_part) (d := nil) in Hl, H by (substl (length l_part); eauto).
    autorewrite with lists in Hl, H.
    cbn [rev app] in Hl, H.
    repeat rewrite app_assoc_reverse in Hl, H.
    rewrite combine_app in Hl, H.
    cbn [app combine] in Hl, H.
    rewrite listmatch_app_rev, listmatch_cons in Hl.
    cancel.
    step.
    indrep_n_tree_bound.
    autorewrite with lists core.
    rewrite skipn_app_r_ge by indrep_n_tree_bound.
    erewrite skipn_selN_skipn by indrep_n_tree_bound.
    cbn.
    autorewrite with core lists.
    rewrite min_l by omega.
    autorewrite with core.
    rewrite firstn_rev by auto.
    autorewrite with lists core.
    replace (length l_part - length prefix) with (S (length lst')) by omega.
    auto.
    rewrite <- listmatch_app, listmatch_cons.
    cancel.
    cancel.
    auto using LOG.active_intact.
    left.
    autorewrite with core lists.
    rewrite Min.min_assoc, Nat.min_id.
    congruence.
    indrep_n_tree_bound.
    indrep_n_tree_bound.
    step.
    eauto using LOG.intact_hashmap_subset.
  Unshelve.
    all: constructor.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indread_aligned _ _ _ _ ) _) => apply indread_aligned_ok : prog.

  Fixpoint indread_to_aligned indlvl lxp ir start ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 (N - start))
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      match indlvl with
      | 0 =>
        Ret ^(ms, skipn start indbns)
      | S indlvl' =>
        let N := (NIndirect ^ S indlvl') in
        let^ (ms, r) <- indread_aligned indlvl' lxp (skipn (S (start / N)) indbns) ms;
        let ir' := selN indbns (start / N) $0 in
        let^ (ms, r') <- indread_to_aligned indlvl' lxp # ir' (start mod N) ms;
        Ret ^(ms, r' ++ r)
      end
    }.

  Theorem indread_to_aligned_ok : forall indlvl lxp ir start ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm IFs m0 sm m bxp l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp IFs ir l ]]] *
           [[ start < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = skipn start l ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_to_aligned indlvl lxp ir start ms.
  Proof.
    induction indlvl; cbn [indread_to_aligned].
    - hoare.
      rewrite indrep_n_helper_0 in *; destruct_lifts.
      autorewrite with core.
      rewrite skipn_repeat; auto.
      rewrite indrep_n_helper_valid by auto.
      cancel.
      rewrite firstn_oob by indrep_n_tree_bound.
      auto.
    - step.
      step.
      erewrite indrep_n_tree_repeat_concat with (m := list2nmem m).
      3: pred_apply; cancel.
      rewrite skipn_repeat; eauto.
      indrep_n_tree_bound.
      step.
      rewrite indrep_n_helper_valid by auto. cancel.
      rewrite firstn_oob by indrep_n_tree_bound.
      step.
      match goal with |- context [skipn ?k] =>
        rewrite listmatch_split with (n := S k)
      end.
      rewrite skipn_combine by auto.
      cancel.
      repeat match goal with |- context [match ?x with _ => _ end] => destruct x end;
        cbn [length] in *; autorewrite with core; congruence.
      step.
      indrep_n_extract. cancel.
      indrep_n_tree_bound.
      indrep_n_tree_bound.
      eapply lt_le_trans; [eapply Nat.mod_upper_bound|]; auto.
      indrep_n_extract.
      erewrite indrep_n_length_pimpl in *.
      destruct_lifts.
      match goal with H: context [selN] |- _ => rewrite H; omega end.
      indrep_n_tree_bound.
      indrep_n_tree_bound.
      step.
      erewrite <- skipn_hom_concat by eauto.
      auto.
  Unshelve.
    all: solve [eauto | exact $0].
  Qed.

  Opaque indread_to_aligned.
  Local Hint Extern 1 ({{_}} Bind (indread_to_aligned _ _ _ _ _ ) _) => apply indread_to_aligned_ok : prog.

  Fixpoint indread_from_aligned indlvl lxp ir len ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 len)
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
      match indlvl with
      | 0 =>
        Ret ^(ms, firstn len indbns)
      | S indlvl' =>
        let N := (NIndirect ^ S indlvl') in
        let^ (ms, r) <- indread_aligned indlvl' lxp (firstn (len / N) indbns) ms;
        If (addr_eq_dec (len mod N) 0) {
          Ret ^(ms, r)
        } else {
          let ir' := selN indbns (len / N) $0 in
          let^ (ms, r') <- indread_from_aligned indlvl' lxp # ir' (len mod N) ms;
          Ret ^(ms, r ++ r')
        }
      end
    }.


  Theorem indread_from_aligned_ok : forall indlvl lxp ir len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm IFs m0 sm m bxp l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl bxp IFs ir l ]]] *
           [[ len <= length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len l ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_from_aligned indlvl lxp ir len ms.
  Proof.
    induction indlvl; cbn [indread_from_aligned].
    + hoare.
      rewrite indrep_n_helper_0 in *; destruct_lifts.
      autorewrite with core.
      rewrite firstn_repeat; auto.
      rewrite repeat_length in *; omega.
      rewrite indrep_n_helper_valid by auto.
      cancel.
      f_equal.
      rewrite firstn_oob by indrep_n_tree_bound.
      auto.
    + step.
      step.
      erewrite indrep_n_tree_repeat_concat with (m := list2nmem m).
      3: pred_apply; cancel.
      rewrite firstn_repeat; eauto.
      indrep_n_tree_bound.
      indrep_n_tree_bound.
      step.
      rewrite indrep_n_helper_valid by auto. cancel.
      rewrite firstn_oob by indrep_n_tree_bound.
      step.
      match goal with |- context [firstn ?k] =>
        rewrite listmatch_split with (n := k)
      end.
      rewrite firstn_combine_comm.
      cancel.
      indrep_n_tree_bound.
      step.
      step.
      erewrite <- concat_hom_firstn by eauto.
      rewrite mul_div by mult_nonzero. auto.
      denote listmatch as Hl; pose proof Hl.
      prestep. norml.
      indrep_n_extract.
      erewrite indrep_n_length_pimpl in *.
      destruct_lifts.
      match goal with H: context [selN] |- _ => rename H into Hr end.
      cancel; hoare.
      - rewrite Hr; auto using mod_le_r.
      - erewrite <- firstn_hom_concat by eauto.
        auto.
      - indrep_n_tree_bound.
        denote le as He.
        destruct (le_lt_eq_dec _ _ He); subst.
        indrep_n_tree_bound.
        rewrite Nat.mod_mul in * by auto.
        congruence.
      - indrep_n_tree_bound.
        denote le as He.
        destruct (le_lt_eq_dec _ _ He); subst.
        indrep_n_tree_bound.
        rewrite Nat.mod_mul in * by auto.
        congruence.
  Unshelve.
    all: solve [eauto | exact $0].
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indread_from_aligned _ _ _ _ _ ) _) => apply indread_from_aligned_ok : prog.

  Definition indread_multiple_blocks indlvl lxp (indbns : list waddr) start len ms :=
    let N := NIndirect ^ S indlvl in
    (* reads up to N blocks if start mod N = 0 *)
    let^ (ms, rl) <- indread_to_aligned indlvl lxp #(selN indbns (start / N) $0) (start mod N) ms;
    let start' := start + (N - start mod N) in
    let len' := len - (N - start mod N) in
    let^ (ms, rm) <- indread_aligned indlvl lxp (firstn (len' / N) (skipn (start' / N) indbns)) ms;
    let len'' := len' mod N in
    let start'' := start' + (len' / N * N) in
    let^ (ms, rr) <- indread_from_aligned indlvl lxp #(selN indbns (start'' / N) $0) len'' ms;
    Ret ^(ms, rl ++ (rm ++ rr)).

  Theorem indread_multiple_blocks_ok : forall indlvl lxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm m0 sm m bxp l_part fsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part) ]]] *
           [[ start < length (concat l_part) ]] *
           [[ (N - start mod N) < len ]] *
           [[ start + len < length (concat l_part) ]] *
           [[ length indbns = length fsl ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len (skipn start (concat l_part)) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_multiple_blocks indlvl lxp indbns start len ms.
  Proof.
    cbv [indread_multiple_blocks].
    prestep. norml.
    denote listmatch as Hl. pose proof Hl.
    assert (length indbns = length l_part) by indrep_n_tree_bound.
    cancel.
    indrep_n_extract. cancel.
    indrep_n_tree_bound.
    indrep_n_tree_bound.
    indrep_n_extract.
    erewrite indrep_n_length_pimpl in *.
    destruct_lifts.
    match goal with H: context [selN] |- _ => rewrite H; auto end.
    indrep_n_tree_bound.
    indrep_n_tree_bound.
    step.
    match goal with |- context [firstn ?m (skipn ?k _)] =>
      rewrite listmatch_split with (n := k);
      rewrite listmatch_split with (n := m) (a := skipn _ _)
    end.
    rewrite <- firstn_combine_comm.
    rewrite <- skipn_combine by eauto.
    cancel.
    autorewrite with core. congruence.
    denote (list2nmem m) as Hm. pose proof Hm.
    indrep_n_extract.
    rewrite Nat.div_add in * by auto.
    hoare.
    - erewrite indrep_n_length_pimpl in *.
      destruct_lifts.
      match goal with H: context [selN] |- _ => rewrite H; auto end.
    - erewrite <- skipn_selN.
      rewrite <- firstn_hom_concat by eauto using forall_skipn.
      erewrite skipn_hom_concat by eauto.
      indrep_n_extract; [ | solve [indrep_n_tree_bound].. ].
      erewrite indrep_n_length_pimpl in *; destruct_lifts.
      rewrite firstn_app.
      rewrite firstn_oob with (n := len).
      autorewrite with core.
      match goal with H: context [selN] |- _ => rewrite H end.
      f_equal.
      match goal with |- context [?a mod ?b] => destruct (addr_eq_dec 0 (a mod b));
        try (substl (a mod b)) end.
      + cbn [skipn firstn].
        autorewrite with core.
        repeat f_equal.
        match goal with |- context [(?a + ?b) / ?b] =>
          replace ((a + b) / b) with ((a + 1 * b) / b) by (do 2 f_equal; omega)
        end.
        rewrite Nat.div_add, plus_comm; auto.
      + rewrite <- roundup_eq by auto.
        unfold roundup.
        rewrite Nat.div_mul by auto.
        rewrite divup_eq_div_plus_1 by auto.
        rewrite plus_comm; auto.
      + autorewrite with core.
        match goal with H: context [selN] |- _ => rewrite H end.
        omega.
    - apply Nat.div_lt_upper_bound; auto.
      eapply le_lt_trans.
      apply plus_le_compat_l, div_mul_le.
      rewrite plus_assoc_reverse.
      rewrite le_plus_minus_r by omega.
      indrep_n_tree_bound.
    - apply Nat.div_lt_upper_bound; auto.
      eapply le_lt_trans.
      apply plus_le_compat_l, div_mul_le.
      rewrite plus_assoc_reverse.
      rewrite le_plus_minus_r by omega.
      indrep_n_tree_bound.
  Unshelve.
    all: solve [eauto | apply emp | exact $0].
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indread_multiple_blocks _ _ _ _ _ _ ) _) => apply indread_multiple_blocks_ok : prog.

  Fixpoint indread_range indlvl lxp (root : addr) start len ms :=
    let N := NIndirect ^ indlvl in
    If (addr_eq_dec len 0) {
      Ret ^(ms, nil)
    } else {
      (* not necessary, but it makes the proof much easier *)
      If (addr_eq_dec (start + len) (NIndirect * N)) {
        indread_to_aligned indlvl lxp root start ms
      } else {
        If (addr_eq_dec root 0) {
          Ret ^(ms, repeat $0 len)
        } else {
          let^ (ms, indbns) <- IndRec.read lxp root 1 ms;
          match indlvl with
          | 0 =>
             Ret ^(ms, firstn len (skipn start indbns))
          | S indlvl' =>
            If (le_dec len (N - start mod N)) {
              indread_range indlvl' lxp #(selN indbns (start / N) $0) (start mod N) len ms
            } else {
              indread_multiple_blocks indlvl' lxp indbns start len ms
            }
          end
        }
      }
    }.

  Theorem indread_range_ok : forall indlvl lxp ir start len ms,
  {< F Fm Fs m0 sm m bxp l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp ir l ]]] *
           [[ start + len <= length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len (skipn start l) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_range indlvl lxp ir start len ms.
  Proof.
    induction indlvl; cbn [indread_range].
    + hoare.
      rewrite firstn_oob; indrep_n_tree_bound.
      rewrite indrep_n_helper_0 in *.
      destruct_lifts.
      rewrite skipn_repeat, firstn_repeat; auto.
      rewrite repeat_length in *; omega.
      rewrite indrep_n_helper_valid by auto. cancel.
      repeat f_equal.
      apply firstn_oob.
      indrep_n_tree_bound.
    + step; step.
      hoare.
      rewrite firstn_oob; indrep_n_tree_bound.
      step.
      step.
      erewrite indrep_n_tree_repeat_concat with (m := list2nmem m).
      3: pred_apply; cancel.
      rewrite skipn_repeat, firstn_repeat; auto.
      indrep_n_tree_bound.
      match goal with H: _ + _ <= length ?l * _ |- _ =>
        replace (length l) with NIndirect in *; indrep_n_tree_bound
      end.
      indrep_n_tree_bound.
      step.
      rewrite indrep_n_helper_valid by auto. cancel.
      rewrite firstn_oob by indrep_n_tree_bound.
      denote listmatch as Hl. pose proof Hl.
      step.
      indrep_n_extract.
      erewrite indrep_n_length_pimpl in *.
      destruct_lifts.
      hoare.
      erewrite skipn_hom_concat by eauto.
      rewrite firstn_app_l; auto.
      match goal with H: context [selN] |- _ => rename H into Hr end.
      autorewrite with core; rewrite Hr.
      omega.
      indrep_n_tree_bound.
      indrep_n_tree_bound.
      hoare.
      indrep_n_tree_bound.
      match goal with H: _ + _ <= length ?l * _ |- _ =>
        replace (length l) with NIndirect in *; indrep_n_tree_bound
      end.
  Unshelve.
    apply emp.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indread_range _ _ _ _ _ _ ) _) => apply indread_range_ok : prog.

  Fixpoint indclear_all indlvl lxp bxp root ms :=
    If (addr_eq_dec root 0) {
      Ret ms
    } else {
      let N := NIndirect ^ indlvl in
      ms <- match indlvl with
      | 0 => Ret ms
      | S indlvl' =>
        let^ (lms, indbns) <- IndRec.read lxp root 1 (BALLOCC.MSLog ms);
        let msn := BALLOCC.upd_memstate lms ms in
        let^ (msn) <- ForEach bn indbns' indbns
          Hashmap hm
          Ghost [ F Fm Fs bxp crash m0 sm freelist l_part fsl ]
          Loopvar [ msn ]
          Invariant
            exists m freelist',
            LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog msn) sm hm *
            let n := length indbns - length indbns' in
            [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl' bxp (snd x) (# (fst x)) l')
                          (combine (skipn n indbns) (skipn n fsl)) (skipn n l_part)
                         * BALLOCC.rep bxp freelist' msn ]]] *
            [[ incl freelist freelist' ]] *
            [[ (Fs * pred_fold_left (skipn n fsl) * BALLOCC.smrep freelist')%pred sm ]]
          OnCrash crash
          Begin
            msn <- indclear_all indlvl' lxp bxp # bn msn;
            Ret ^(msn)
          Rof ^(msn);
          Ret msn
      end;
      BALLOCC.free lxp bxp root ms
    }.


  Theorem indclear_all_ok : forall indlvl lxp bxp ir ms,
    let N := NIndirect ^ indlvl in
    {< F Fm Fs IFS m0 sm m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFS ir l *
              BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFS * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET: ms
           exists m' freelist' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp emp 0 l' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_all indlvl lxp bxp ir ms.
    Proof.
      induction indlvl; simpl.
      + step.
        hoare.
        repeat rewrite indrep_n_helper_0. cancel.
        rewrite indrep_n_helper_0 in *.
        denote lift_empty as Hf; destruct_lift Hf.
        psubst; auto.
        destruct (addr_eq_dec ir 0). step.
        rewrite indrep_n_helper_pts_piff in * by auto.
        denote lift_empty as Hf; destruct_lift Hf.
        psubst. denote exis as Hf; destruct_lift Hf.
        hoare.
        rewrite indrep_n_helper_0 by auto.
        cancel.
      + step.
        psubst.
        step.
        symmetry. eapply indrep_n_tree_repeat_Fs with (m := list2nmem m).
        indrep_n_tree_bound.
        pred_apply; cancel.
        eapply indrep_n_tree_repeat_Fs with (m := list2nmem m).
        indrep_n_tree_bound.
        pred_apply; cancel.
        step.
        rewrite indrep_n_helper_valid by auto. cancel.
        rewrite indrep_n_helper_length_piff in *.
        denote indrep_n_helper as Hi; destruct_lift Hi.
        unfold IndRec.Defs.item in *; simpl in *. rewrite firstn_oob by omega.
        prestep. norm. cancel.
        rewrite Nat.sub_diag; cbn [skipn].
        intuition auto.
        - pred_apply. cancel.
        - apply incl_refl.
        - psubst.
          pred_apply; cancel.
        - match goal with H: context [listmatch _ _ ?l] |- _ =>
            assert (length l = NIndirect) by indrep_n_tree_bound end.
          prestep. norml.
          assert (length prefix < NIndirect).
          rewrite indrep_n_helper_length_piff in *; destruct_lifts.
          autorewrite with lists in *; cbn [length] in *; omega.
          cancel.
          autorewrite with lists; cbn [length].
          repeat rewrite ?Nat.add_sub, ?Nat.sub_diag, ?skipn_app_r_ge by omega.
          cbn [skipn].
          erewrite skipn_selN_skipn by omega.
          cbn [combine].
          erewrite skipn_selN_skipn with (off := length prefix) by omega.
          rewrite listmatch_cons.
          cancel.
          autorewrite with lists; cbn [length].
          repeat rewrite Nat.add_sub.
          erewrite skipn_selN_skipn with (l := dummy1) by omega.
          rewrite pred_fold_left_cons.
          cancel.
          reflexivity.
          step.
          autorewrite with lists; cbn [length].
          rewrite skipn_app_r_ge by omega.
          repeat match goal with |- context [?b + S ?a - ?a] => replace (b + S a - a) with (S b) by omega end.
          repeat match goal with |- context [S ?a - ?a] => replace (S a - a) with 1 by omega end.
          rewrite indrep_n_tree_0. cancel.
          autorewrite with lists; cbn [length].
          repeat match goal with |- context [?b + S ?a - ?a] => replace (b + S a - a) with (S b) by omega end.
          cancel.
          cancel.
        - rewrite indrep_n_helper_valid in * by auto.
          denote lift_empty as Hl; destruct_lift Hl.
          psubst.
          denote piff as Hp. rewrite Hp in *.
          match goal with H: context [(_ |->?)%pred] |- _ => progress destruct_lift H end.
          prestep. norml.
          repeat rewrite skipn_oob in * by omega.
          rewrite Hp in *.
          cancel.
          rewrite skipn_oob by indrep_n_tree_bound.
          rewrite indrep_n_helper_pts_piff by auto.
          unfold listmatch; cancel.
          safestep.
          apply listmatch_indrep_n_tree_empty.
          autorewrite with lists; auto.
          rewrite pred_fold_left_repeat_emp.
          split; cancel.
          reflexivity.
          cancel.
        - cancel.
          eauto using LOG.intact_hashmap_subset.
    Grab Existential Variables.
    all: try exact addr_eq_dec.
    all : eauto using tt.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_all _ _ _ _ _ ) _) => apply indclear_all_ok : prog.

  Definition indclear_aligned indlvl lxp bxp (indbns : list waddr) start len ms :=
    let N := NIndirect ^ S indlvl in
    let indbns := firstn (len / N) (skipn (start / N) indbns) in
    ForEach bn rest indbns
      Hashmap hm
      Ghost [ F Fm Fs l_part fsl bxp crash m0 sm freelist ]
      Loopvar [ ms ]
      Invariant
        exists l_part' indbns' fsl' freelist' m,
        LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
        let n := length indbns - length rest in
        [[ l_part' = skipn n l_part ]] *
        [[ indbns' = skipn n indbns ]] *
        [[ fsl' = skipn n fsl ]] *
        [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl bxp (snd x) # (fst x) l') (combine indbns' fsl') l_part' *
                  BALLOCC.rep bxp freelist' ms ]]] *
        [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
        [[ incl freelist freelist' ]]
      OnCrash crash
      Begin
        ms <- indclear_all indlvl lxp bxp # bn ms;
        Ret ^(ms)
      Rof ^(ms).

  Theorem indclear_aligned_ok : forall indlvl lxp bxp indbns start len ms,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part fsl freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) # (fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start / N + len / N <= length l_part ]] * [[ Nat.divide N start ]] * [[ Nat.divide N len ]] *
           [[ length fsl = length indbns ]] *
           [[ (Fs * BALLOCC.smrep freelist * pred_fold_left fsl)%pred sm ]]
    POST:hm' RET:^(ms)
           exists m' freelist' indbns' fsl' l_part', 
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ indbns' = upd_range indbns (start / N) (len / N) $0 ]] *
           [[ l_part' = upd_range l_part (start / N) (len / N) (repeat $0 N) ]] *
           [[ incl freelist freelist' ]] *
           [[ length fsl' = length indbns' ]] *
           [[ (Fs * BALLOCC.smrep freelist' * pred_fold_left fsl')%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_aligned indlvl lxp bxp indbns start len ms.
    Proof.
      unfold indclear_aligned. unfold Nat.divide.
      prestep. norml.
      repeat rewrite Nat.div_mul in * by mult_nonzero.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      cancel.
      all: repeat rewrite Nat.sub_diag; auto.
      - cbn [skipn].
        rewrite <- firstn_combine_comm.
        rewrite <- skipn_combine by eauto.
        rewrite listmatch_split with (n := z0).
        rewrite listmatch_split with (n := z) (a := skipn _ _).
        repeat cancel.
      - cbn [skipn].
        erewrite <- firstn_skipn with (n := z0) (l := fsl) at 1.
        erewrite <- firstn_skipn with (n := z) (l := skipn _ fsl) at 1.
        repeat rewrite pred_fold_left_app. cancel.
      - prestep. norml.
        assert (length (firstn z (skipn z0 fsl)) = length (firstn z (skipn z0 indbns))) by
          (repeat rewrite ?firstn_length, ?skipn_length; congruence).
        assert (length (firstn z (skipn z0 l_part)) = length (firstn z (skipn z0 indbns))) by
          (rewrite firstn_length, skipn_length; indrep_n_tree_bound).
        assert (length prefix < length (firstn z (skipn z0 indbns))) by
          (substl (firstn z (skipn z0 indbns)); rewrite app_length; cbn; omega).
        match goal with H: _ ++ _ = _ |- _ => rename H into Hp; repeat rewrite <- Hp in * end.
        autorewrite with lists in *. cbn [length] in *.
        repeat rewrite Nat.add_sub in *.
        rewrite skipn_app in *.
        cancel.
        + erewrite skipn_selN_skipn with (l := firstn _ (skipn _ fsl)) at 1.
          erewrite skipn_selN_skipn with (l := firstn _ (skipn _ l_part)) at 1.
          cbn [combine].
          rewrite listmatch_cons.
          cancel.
          all: omega.
        + erewrite skipn_selN_skipn with (off := length prefix).
          rewrite pred_fold_left_cons.
          cancel. reflexivity.
          omega.
        + step.
          repeat match goal with |- context [?b + S ?a - ?a] => replace (b + S a - a) with (b + 1) by omega end.
          rewrite skipn_app_r_ge by omega.
          rewrite minus_plus. rewrite <- plus_n_Sm, <- plus_n_O.
          rewrite indrep_n_tree_0.
          cancel.
          repeat match goal with |- context [?b + S ?a - ?a] => replace (b + S a - a) with (b + 1) by omega end.
          rewrite <- plus_n_Sm, <- plus_n_O.
          cancel.
        + cancel.
      - step.
        match goal with H: context [lift_empty] |- _ => destruct_lift H end.
        rewrite combine_length_eq in * by auto.
        repeat rewrite upd_range_eq_upd_range' by omega.
        unfold upd_range'.
        repeat rewrite combine_app.
        repeat rewrite skipn_skipn.
        replace (z0 + z) with (z + z0) in * by omega.
        rewrite firstn_combine_comm, skipn_combine by auto.
        repeat rewrite <- listmatch_app; cancel.
        repeat rewrite Nat.sub_0_r.
        repeat rewrite skipn_oob by indrep_n_tree_bound.
        rewrite listmatch_indrep_n_tree_empty'.
        unfold listmatch; cancel.
        autorewrite with lists; auto.
        indrep_n_tree_bound.
        autorewrite with lists.
        match goal with H: context [lift_empty] |- _ => destruct_lift H end.
        rewrite combine_length_eq in * by auto.
        rewrite firstn_length_l, skipn_length by omega.
        omega.
        repeat rewrite pred_fold_left_app.
        cancel.
        rewrite skipn_skipn.
        rewrite skipn_oob by indrep_n_tree_bound.
        rewrite pred_fold_left_repeat_emp.
        cancel.
      - cancel.
        eauto using LOG.intact_hashmap_subset.
    Grab Existential Variables. all : eauto; split.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_aligned _ _ _ _ _ _ _ ) _) => apply indclear_aligned_ok : prog.

  Definition update_block lxp bxp bn contents new ms :=
    If (list_eq_dec waddr_eq_dec new (repeat $0 NIndirect)) {
      ms <- BALLOCC.free lxp bxp bn ms;
      Ret ^(ms, 0)
    } else {
      If (list_eq_dec waddr_eq_dec contents new) {
        Ret ^(ms, bn)
      } else {
        lms <- IndRec.write lxp bn new (BALLOCC.MSLog ms);
        Ret ^(BALLOCC.upd_memstate lms ms, bn)
      }
    }.

  Lemma indrep_n_helper_valid_sm: forall Fs bxp ir l,
    ir <> 0 ->
    indrep_n_helper Fs bxp ir l =p=> indrep_n_helper Fs bxp ir l * [[ Fs <=p=> ir |->? ]].
  Proof.
    unfold indrep_n_helper.
    intros.
    destruct addr_eq_dec; try congruence.
    cancel.
  Qed.

  Theorem update_block_ok : forall lxp bxp ir indbns indbns' ms,
    {< F Fm Fs IFs m0 sm m freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
            [[ BALLOCC.bn_valid bxp ir ]] *
            [[ IndRec.items_valid ir indbns' ]] *
           [[[ m ::: (Fm * indrep_n_helper IFs bxp ir indbns) *
              BALLOCC.rep bxp freelist ms ]]] *
            [[ (Fs * BALLOCC.smrep freelist * IFs)%pred sm ]]
    POST:hm' RET: ^(ms, ir')
           exists m' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_helper IFs' bxp ir' indbns' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * BALLOCC.smrep freelist' * IFs')%pred sm ]] *
           [[ incl freelist freelist' ]] *
           ([[ ir' = 0 ]] \/ [[ ir' = ir ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} update_block lxp bxp ir indbns indbns' ms.
  Proof.
    unfold update_block.
    prestep. norml.
    assert (ir <> 0) by (unfold BALLOCC.bn_valid in *; intuition).
    rewrite indrep_n_helper_valid_sm in * by auto.
    denote lift_empty as Hf; destruct_lift Hf.
    denote IFs as Hf; rewrite Hf in *.
    denote BALLOCC.smrep as Hs; destruct_lift Hs.
    step.
    rewrite indrep_n_helper_pts_piff by auto. cancel.
    + step.
      rewrite indrep_n_helper_0 by auto.
      cancel.
    + step.
      rewrite Hf; cancel.
    + step.
      rewrite indrep_n_helper_valid by auto; cancel.
      prestep. norm. repeat cancel.
      intuition idtac.
      rewrite indrep_n_helper_valid by auto.
      pred_apply; cancel; reflexivity.
      pred_apply; cancel.
      auto.
      auto.
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
        let^ (lms, indbns) <- IndRec.read lxp ragged_bn 1 (BALLOCC.MSLog ms);
        let ms := BALLOCC.upd_memstate lms ms in
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
    {< F Fm Fs m0 sm m l_part freelist fsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start + len <= length (concat l_part) ]] * [[ Nat.divide N start ]] * [[ len < N ]] *
           [[ length fsl = length indbns ]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part' fsl',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ length indbns' = length indbns ]] *
           [[ length fsl' = length indbns' ]] *
           [[ incl freelist freelist' ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_from_aligned indlvl lxp bxp indbns start len ms.
  Proof.
    induction indlvl.
    + simpl. step; [> solve [hoare] |].
      pose proof listmatch_indrep_n_tree_forall_length 0 as H'.
      simpl in H'. rewrite H' in *.
      denote combine as Hc. destruct_lift Hc. rewrite mult_1_r in *.
      prestep. norml.
      erewrite concat_hom_length in * by eauto.
      assert (start / NIndirect < length l_part) by indrep_n_tree_bound.
      assert (start / NIndirect < length indbns) by indrep_n_tree_bound.
      cancel.
      - hoare.
        rewrite listmatch_extract in *.
        erewrite selN_combine in * by auto.
        cbn [fst snd] in *.
        denote (# _ = _) as Ha. rewrite Ha in *.
        rewrite indrep_n_helper_0 in *.
        destruct_lifts.
        erewrite upd_range_concat_hom_start_aligned; eauto.
        denote (selN _ _ _ = repeat _ _) as Hb. rewrite Hb.
        rewrite upd_range_same by omega.
        erewrite selN_eq_updN_eq; eauto.
        indrep_n_tree_bound.
        omega.
        indrep_n_tree_bound.
      - step.
        indrep_n_extract.
        rewrite indrep_n_helper_valid by eauto. cancel.
        indrep_n_tree_bound.
        rewrite firstn_oob.
        safestep.
        1, 2: match goal with |- context [selN ?l ?ind ?d] =>
            erewrite listmatch_extract with (a := combine l _) (i := ind) (ad := (d, _)) in *
          end; rewrite ?selN_combine in * by auto; cbn [fst snd] in *;
          auto; indrep_n_tree_bound.
        * rewrite indrep_n_helper_items_valid in * by auto; destruct_lifts.
          cbv [IndRec.items_valid] in *.
          autorewrite with lists. intuition eauto.
        * indrep_n_extract. cancel. indrep_n_tree_bound.
        * rewrite pred_fold_left_selN_removeN with (i := start / NIndirect).
          cancel. reflexivity.
        * step.
        **  rewrite combine_updN, listmatch_updN_removeN. cancel. all: indrep_n_tree_bound.
        **  erewrite upd_range_concat_hom_start_aligned; eauto. indrep_n_tree_bound. omega.
        **  indrep_n_tree_bound.
        **  autorewrite with lists; omega.
        **  rewrite pred_fold_left_selN_removeN with (l := updN _ _ _).
            rewrite selN_updN_eq, removeN_updN by omega. cancel.
        **  rewrite natToWord_wordToNat. rewrite combine_updN.
            rewrite listmatch_updN_removeN by (eauto; indrep_n_tree_bound). cancel.
        **  erewrite upd_range_concat_hom_start_aligned; eauto. indrep_n_tree_bound. omega.
        **  indrep_n_tree_bound.
        **  autorewrite with lists; omega.
        **  rewrite pred_fold_left_selN_removeN with (l := updN _ _ _).
            rewrite selN_updN_eq, removeN_updN by omega. cancel.
        * cancel.
        * match goal with |- context [selN ?l ?ind ?d] =>
            rewrite listmatch_extract with (b := l) (i := ind) (bd := d) in *
          end. rewrite indrep_n_helper_length_piff in *.
          destruct_lifts.
          denote (length (selN _ _ _) = _) as Ha. rewrite Ha.
          omega.
          indrep_n_tree_bound.
    + cbn [indclear_from_aligned].
      prestep. norml.
      pose proof listmatch_indrep_n_tree_forall_length (S indlvl) as H'.
      simpl in H'. rewrite H' in *.
      denote (combine indbns fsl) as Hc; destruct_lift Hc.
      cancel; [ solve [hoare] |].
      prestep. norml.
      erewrite concat_hom_length in * by eauto.
      assert (start / (NIndirect ^ S (S indlvl)) < length l_part) by indrep_n_tree_bound.
      assert (start / (NIndirect ^ S (S indlvl)) < length indbns) by indrep_n_tree_bound.
      cancel.
      step.
      {
        rewrite listmatch_extract in *.
        erewrite selN_combine in * by auto. cbn [fst snd] in *.
        denote (# _ = _) as Ha. rewrite Ha in *.
        destruct_lifts.
        rewrite indrep_n_helper_0 in *.
        destruct_lift H.
        rewrite listmatch_indrep_n_tree_empty'' in *.
        destruct_lifts.
        erewrite upd_range_concat_hom_start_aligned; eauto.
        denote (selN _ _ _ = _) as Hs. rewrite Hs.
        rewrite concat_repeat in *.
        rewrite upd_range_same by omega.
        erewrite selN_eq_updN_eq; eauto.
        indrep_n_tree_bound.
        omega.
        omega.
        rewrite repeat_length in *; eauto.
        indrep_n_tree_bound.
      }
      match goal with [|- context [selN ?L ?N] ] => 
        rewrite listmatch_extract with (a := combine L _) (i := N) in * by indrep_n_tree_bound end.
      destruct_lifts.
      rewrite combine_length_eq in * by omega.
      step.
      {
        rewrite selN_combine by indrep_n_tree_bound; cbn [fst snd].
        rewrite indrep_n_helper_valid by eauto. cancel.
      }
      rewrite firstn_oob.
      match goal with [H : context [listmatch _ (combine ?l _)] |- context [?c = ?l] ] =>
        rewrite listmatch_length_pimpl with (a := combine l _) in H;
        rewrite indrep_n_helper_length_piff in H; destruct_lift H end.
      rewrite combine_length_eq in * by omega.
      prestep. norm. cancel.
      intuition auto.
      pred_apply; cancel.
      {
        rewrite Nat.div_mul, Nat.div_0_l by auto. simpl in *.
        apply Nat.div_le_upper_bound; mult_nonzero. rewrite mult_comm.
        apply Nat.lt_le_incl. congruence.
      }
      indrep_n_tree_bound.
      {
        denote (snd (selN _ _ _)) as Hp.
        rewrite selN_combine in Hp by indrep_n_tree_bound.
        cbn [snd] in Hp.
        pred_apply.
        rewrite pred_fold_left_selN_removeN.
        rewrite Hp.
        cancel.
      }
      safestep.
      { rewrite Nat.div_0_l, Nat.div_mul by auto. cancel. }
      {
        rewrite mult_comm, <- Nat.div_mod by auto.
        erewrite concat_hom_length by eauto.
        autorewrite with lists.
        apply Nat.lt_le_incl. congruence.
      }
      autorewrite with lists; indrep_n_tree_bound.
      cancel.
      prestep. norm. cancel.
      rewrite selN_combine with (a := indbns) in * by eauto.
      cbn [fst snd] in *.
      intuition auto.
      unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
      rewrite mult_1_l. intuition.
      rewrite upd_range_length in *.
      match goal with |- length ?x = _ => substl (length x) end.
      indrep_n_tree_bound.
      pred_apply; cancel.
      pred_apply; cancel.
      - step; clear IHindlvl.
        5: match goal with |- context [removeN _ ?i] =>
          erewrite pred_fold_left_selN_removeN with (l := updN fsl i (pred_fold_left fsl'0));
          rewrite selN_updN_eq, removeN_updN by omega
        end.
        * rewrite indrep_n_helper_0. cancel.
          rewrite combine_updN, listmatch_updN_removeN.
          norm. cancel. eassign IFs'. rewrite indrep_n_helper_0. cancel.
          intuition eauto.
          denote (IFs' <=p=> emp) as Hf. rewrite Hf. split; cancel.
          all: indrep_n_tree_bound.
        * erewrite upd_range_concat_hom_start_aligned; eauto.
          repeat f_equal.
          denote (concat _ = _) as Hc. rewrite Hc.
          denote (selN _ _ _ = _) as Hs. rewrite Hs.
          rewrite concat_hom_upd_range by eauto. cbn -[Nat.div Nat.modulo].
          autorewrite with lists. simpl.
          rewrite mult_comm, <- Nat.div_mod; auto.
          erewrite concat_hom_length; eauto.
          all: omega.
        * autorewrite with lists; auto.
        * autorewrite with lists; omega.
        * denote (indrep_n_helper _ _ 0) as Hi. rewrite indrep_n_helper_0 in Hi.
          destruct_lift Hi. denote (IFs' <=p=> emp) as Hf. rewrite Hf. cancel.
        * rewrite natToWord_wordToNat. rewrite combine_updN.
          rewrite listmatch_updN_removeN. cancel. reflexivity.
          indrep_n_tree_bound.
          reflexivity.
          all: indrep_n_tree_bound.
        * denote (concat _ = _) as Hc. rewrite Hc.
          symmetry.
          erewrite upd_range_concat_hom_start_aligned; eauto.
          rewrite concat_hom_upd_range; eauto.
          rewrite upd_range_upd_range; eauto.
          repeat f_equal; eauto.
          rewrite mult_comm with (n := len / _), <- Nat.div_mod; auto.
          erewrite concat_hom_length by eauto. omega.
          all: omega.
        * autorewrite with lists; auto.
        * autorewrite with lists; auto.
        * rewrite pred_fold_left_selN_removeN with (l := updN _ _ _).
          rewrite selN_updN_eq, removeN_updN by omega. cancel.
      - cancel.
      - cancel.
      - cancel.
      - indrep_n_tree_bound.
    Grab Existential Variables.
    all : intros; eauto.
    all : try solve [exact unit | exact nil | exact $ 0 | exact 0 | exact True | exact ($0, emp) ].
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
        let^ (lms, indbns) <- IndRec.read lxp ragged_bn 1 (BALLOCC.MSLog ms);
        let ms := BALLOCC.upd_memstate lms ms in
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
    {< F Fm Fs m0 sm m fsl l_part freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]] *
           [[ start <= length (concat l_part) ]] *
           [[ length fsl = length indbns ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' fsl' l_part',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start (roundup start N - start) $0 ]] *
           [[ incl freelist freelist' ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ length fsl' = length indbns' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_to_aligned indlvl lxp bxp indbns start ms.
  Proof.
    induction indlvl.
    intros.
    + simpl in *. subst N. rewrite mult_1_r in *.
      step. hoare.
      {
        unfold roundup. rewrite divup_eq_div by auto.
        rewrite mul_div by auto. autorewrite with core lists. auto.
      }
      denote indrep_n_helper as Hi.
      setoid_rewrite (listmatch_indrep_n_tree_forall_length 0) in Hi.
      destruct_lift Hi. rewrite mult_1_r in *.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      prestep. norml.
      assert (start / NIndirect < length l_part).
        erewrite concat_hom_length in *; eauto.
        apply Nat.div_lt_upper_bound; auto. rewrite mult_comm.
        edestruct le_lt_eq_dec; [> | eauto |]; eauto.
        subst. rewrite Nat.mod_mul in * by auto. intuition.
      cancel.
      prestep. norm. cancel.
      intuition auto.
      2: {
        rewrite roundup_eq, minus_plus by auto.
        rewrite listmatch_extract in *.
        erewrite <- upd_range_concat_hom_small; eauto.
        all : autorewrite with core lists; auto with *; eauto.
        rewrite <- roundup_eq by auto.
        erewrite concat_hom_length in * by eauto.
        apply roundup_le. omega.
        eassign (start / NIndirect).
        rewrite min_l by omega.
        rewrite combine_length_eq in *; omega.
      }
      {
        pred_apply; cancel.
        erewrite <- updN_selN_eq with (l := combine _ _) at 2.
        rewrite listmatch_updN_removeN.
        indrep_n_extract.
        repeat rewrite selN_combine by auto. cbn [fst snd].
        denote (# _ = _) as Hn. repeat rewrite Hn. rewrite indrep_n_helper_0 in *.
        cancel. rewrite indrep_n_helper_0.
        cancel.
        denote (_ = repeat _ _) as Hl. rewrite Hl.
        apply upd_range_same.
        eauto.
        all: omega.
      }
      auto.
      pred_apply; cancel.
      omega.
      step.
      indrep_n_extract. rewrite indrep_n_helper_valid by eauto. cancel.
      rewrite firstn_oob.
      prestep. norm. cancel.
      intuition auto.
      - match goal with [|- context [selN ?L ?N ?d] ] =>
          erewrite listmatch_extract with (a := combine L _) (i := N) (ad := (d, _)) in * by omega
        end. rewrite selN_combine in * by auto. cbn [fst snd] in *. eauto.
      - match goal with [|- context [selN ?L ?N ?d] ] =>
          erewrite listmatch_extract with (a := combine L _) (i := N) (ad := (d, _)) in * by omega
        end. rewrite selN_combine in * by auto. cbn [fst snd] in *.
        rewrite indrep_n_helper_items_valid in * by eauto; destruct_lifts.
        unfold IndRec.items_valid in *; intuition.
        autorewrite with lists; eauto.
      - pred_apply. indrep_n_extract. cancel.
      - pred_apply. rewrite pred_fold_left_selN_removeN with (i := start/NIndirect) (l := fsl).
        cancel. instantiate (1 := emp). cancel.
      - prestep; norm; try cancel.
        all: intuition auto.
        * pred_apply. erewrite combine_updN. rewrite listmatch_updN_removeN. cancel. all: omega.
        * rewrite roundup_eq by auto. rewrite minus_plus.
          erewrite upd_range_concat_hom_small; eauto.
          all : autorewrite with core; eauto.
          rewrite <- roundup_eq by auto.
          erewrite concat_hom_length in *; eauto.
        * auto.
        * rewrite pred_fold_left_updN_removeN by (rewrite combine_length_eq in *; omega).
          pred_apply; cancel.
        * autorewrite with lists; auto.
        * rewrite natToWord_wordToNat. rewrite combine_updN.
          rewrite listmatch_updN_removeN. pred_apply; cancel.
          all: rewrite ?combine_length_eq; try omega; indrep_n_tree_bound.
        * rewrite roundup_eq by auto. rewrite minus_plus.
          erewrite upd_range_concat_hom_small; eauto.
          rewrite <- roundup_eq by auto.
          erewrite concat_hom_length in * by eauto. auto.
          rewrite le_plus_minus_r; auto.
        * auto.
        * rewrite pred_fold_left_updN_removeN by (rewrite combine_length_eq in *; omega).
          pred_apply; cancel.
        * autorewrite with lists; auto.
      - cancel.
      - match goal with [|- context [selN ?L ?N ?d] ] =>
          rewrite listmatch_extract with (b := L) (i := N) (bd := d) in * by omega
        end. rewrite indrep_n_helper_length_piff in *.
        destruct_lifts. autorewrite with core. apply Nat.eq_le_incl. assumption.
    + cbn [indclear_to_aligned].
      prestep. norml.
      pose proof listmatch_indrep_n_tree_forall_length (S indlvl) as H'.
      simpl in H'. match goal with H: _ |- _ => rewrite H' in H; destruct_lift H end.
      cancel. hoare.
      {
        unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero.
        autorewrite with core. auto.
      }
      prestep. norml.
      rewrite listmatch_length_pimpl in *. destruct_lifts.
      assert (start / (NIndirect ^ S (S indlvl)) < length l_part); simpl in *.
        erewrite concat_hom_length in *; eauto.
        apply Nat.div_lt_upper_bound; auto. rewrite mult_comm.
        edestruct le_lt_eq_dec; [> | eauto |]; eauto.
        subst. rewrite Nat.mod_mul in * by auto. intuition.
      cancel. prestep. norm. cancel.
      instantiate (1 := updN _ _ _). intuition auto.
      {
        erewrite <- updN_selN_eq with (l := indbns) at 1.
        rewrite combine_updN. rewrite listmatch_updN_removeN.
        denote (# _ = 0) as Hn. cbn [fst snd].
        pred_apply. rewrite listmatch_extract. rewrite selN_combine.
        cbn [fst snd]. repeat rewrite Hn. cancel. reflexivity.
        all: eauto; omega.
      }
      {
        rewrite roundup_eq, minus_plus by auto.
        rewrite listmatch_extract in *. destruct_lifts.
        erewrite upd_range_concat_hom_small; eauto.
        erewrite selN_combine in *. cbn [fst snd] in *.
        denote (# _ = 0) as Hn. rewrite Hn in *.
        rewrite indrep_n_helper_0 in *. destruct_lifts.
        rewrite listmatch_indrep_n_tree_empty'' in *. destruct_lifts.
        do 2 f_equal.
        denote (selN _ _ _ = _) as Hs. repeat rewrite Hs.
        erewrite concat_hom_repeat by (auto using Forall_repeat).
        rewrite upd_range_same; auto.
        all: try omega; mult_nonzero.
        indrep_n_tree_bound.
        erewrite concat_hom_length in * by eauto.
        rewrite <- roundup_eq; auto.
        indrep_n_tree_bound.
      }
      auto.
      rewrite updN_selN_eq. auto.
      autorewrite with lists; auto.
      match goal with [|- context [selN ?L ?N ?d] ] =>
        rewrite listmatch_extract with (a := combine L _) (i := N) (ad := (d, emp)) in * by omega
      end. simpl in *. destruct_lifts.
      rewrite selN_combine in * by omega; cbn [fst snd] in *.
      step.
      { rewrite indrep_n_helper_valid by eauto. cancel. }
      rewrite firstn_oob.
      match goal with [H : context [listmatch _ (combine ?l _)] |- context [?c = ?l] ] =>
        rewrite listmatch_length_pimpl with (a := combine l _) in H;
        rewrite indrep_n_helper_length_piff in H; destruct_lift H end.
      prestep. norm. cancel.
      intuition auto.
      pred_apply; cancel.
      pred_apply. rewrite pred_fold_left_selN_removeN with (l := fsl).
      denote (selN fsl) as Hs. rewrite Hs. cancel.
      {
        erewrite concat_hom_length by eauto.
        eapply le_trans; [> | apply mult_le_compat_r]. eauto. indrep_n_tree_bound.
      }
      omega.
      safestep.
      {
        unfold roundup. rewrite <- Nat.mul_sub_distr_r. repeat rewrite Nat.div_mul by auto.
        autorewrite with core.
        match goal with [H : context [concat ?l] |- context [length ?l] ] =>
          apply f_equal with (f := @length _) in H; erewrite concat_hom_length in H; eauto end.
        rewrite upd_range_length in *; autorewrite with core; auto with *.
        erewrite concat_hom_length in * by eauto.
        rewrite Nat.mul_cancel_r in *; mult_nonzero.
        rewrite combine_length_eq in * by omega. omega.
        apply divup_le. rewrite mult_comm. eauto.
      }
      prestep. norm. cancel. intuition idtac.
      auto.
      {
        unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
        rewrite mult_1_l.
        match goal with [H : context [listmatch _ (combine ?l _)] |- context [length (upd_range ?l _ _ _)] ] =>
          rewrite listmatch_length_pimpl with (a := (combine l _)) in H; destruct_lift H end.
        denote (concat _ = upd_range _ _ _ _) as Hc.
        apply f_equal with (f := @length _) in Hc.
        rewrite combine_length_eq in * by omega.
        erewrite concat_hom_length in Hc; eauto.
        autorewrite with lists in *.
        erewrite concat_hom_length in * by eauto.
        rewrite Nat.mul_cancel_r in *; mult_nonzero.
        intuition; omega.
      }
      pred_apply; cancel.
      pred_apply; cancel.
      step; clear IHindlvl.
      - rewrite indrep_n_helper_0. cancel.
        rewrite combine_updN, listmatch_updN_removeN.
        norm. cancel. rewrite indrep_n_helper_0'. cancel.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r.
        repeat rewrite Nat.div_mul by auto.
        denote (upd_range _ _ _) as Hu. rewrite Hu.
        cancel. reflexivity.
        intuition eauto.
        rewrite upd_range_length, repeat_length in *.
        match goal with H: upd_range ?l _ _ _ = _ |- length ?l' = _ =>
          assert (length l' = length l) as Hl by indrep_n_tree_bound; rewrite Hl;
          eapply f_equal with (f := @length _) in H; autorewrite with lists in H
        end.
        all : omega.
      - rewrite roundup_eq with (a := start) by mult_nonzero.
        rewrite minus_plus.
        eapply indclear_upd_range_helper_1; eauto.
        erewrite concat_hom_length by eauto.
        rewrite combine_length_eq2 in * by omega. congruence.
      - rewrite pred_fold_left_updN_removeN.
        rewrite indrep_n_helper_0 with (Fs := IFs') in *.
        denote (IFs' <=p=> emp) as Hf; destruct_lift Hf.
        psubst. cancel.
        rewrite combine_length_eq in * by omega. omega.
      - autorewrite with lists; auto.
      - rewrite natToWord_wordToNat.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r. repeat rewrite Nat.div_mul by auto.
        rewrite combine_updN.
        rewrite listmatch_updN_removeN. cancel; eauto.
        indrep_n_tree_bound.
        all : omega.
      - erewrite indclear_upd_range_helper_1; eauto.
        f_equal. rewrite roundup_eq by auto. omega.
        erewrite concat_hom_length by eauto.
        rewrite combine_length_eq in * by omega. congruence.
      - rewrite pred_fold_left_updN_removeN. cancel.
        rewrite combine_length_eq in * by omega. omega.
      - autorewrite with lists; auto.
      - cancel.
      - cancel.
      - cancel.
      - rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *. simpl in *. omega.
    Unshelve.
    all : intros; try solve [exact unit | exact nil | exact $0 | exact emp | exact ($0, emp) | constructor].
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
    {< F Fm Fs m0 sm m l_part freelist fsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start <= length (concat l_part) ]] * [[ (N - start mod N) < len ]] *
           [[ start + len <= length (concat l_part) ]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]] *
           [[ length indbns = length fsl ]]
    POST:hm' RET:^(ms, indbns')
           exists m' freelist' l_part' fsl',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ length indbns' = length fsl' ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear_multiple_blocks indlvl lxp bxp indbns start len ms.
  Proof.
    intros. subst N.
    unfold indclear_multiple_blocks.
    step.
    step.
    { repeat rewrite Nat.div_mul by mult_nonzero.
      eapply le_trans. apply div_add_distr_le.
      denote (concat _ = _) as Hc.
      apply f_equal with (f := @length _) in Hc.
      rewrite upd_range_length in *.
      repeat erewrite concat_hom_length in * by eauto.
      rewrite Nat.mul_cancel_r in * by mult_nonzero.
      apply Nat.div_le_upper_bound; auto. rewrite mult_comm with (m := length _).
      destruct (addr_eq_dec (start mod (NIndirect * NIndirect ^ indlvl)) 0).
      - unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero.
        autorewrite with core. congruence.
      - rewrite roundup_eq by auto. rewrite minus_plus.
        rewrite <- plus_assoc. autorewrite with core; solve [congruence | omega].
    }
    { autorewrite with core; auto. }
    prestep. norm. cancel.
    intuition auto.
    + pred_apply. repeat rewrite Nat.div_mul by auto. cancel.
    + erewrite concat_hom_length by auto. autorewrite with lists.
      rewrite mult_comm with (m := _ * _ ^ _).
      rewrite <- plus_assoc, <- Nat.div_mod by auto.
      denote (concat _ = _) as Hc.
      apply f_equal with (f := @length _) in Hc.
      rewrite upd_range_length in *.
      repeat erewrite concat_hom_length in * by eauto.
      rewrite Nat.mul_cancel_r in * by mult_nonzero.
      destruct (addr_eq_dec (start mod (NIndirect * NIndirect ^ indlvl)) 0).
      - unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero.
        autorewrite with core. congruence.
      - rewrite roundup_eq by auto. rewrite minus_plus.
        rewrite <- plus_assoc. autorewrite with core; solve [congruence | omega].
    + autorewrite with core. auto.
    + autorewrite with lists in *. omega.
    + pred_apply; cancel.
    + step.
      rewrite concat_hom_upd_range in * by eauto.
      set (N := _ * _ ^ _) in *.
      rewrite le_plus_minus_r in * by auto.
      rewrite roundup_round in *.
      match goal with H: concat _ = _, H' : concat _ = _ |- _ => rewrite H, H' end.
      autorewrite with lists.
      rewrite mult_comm with (m := N), <- Nat.div_mod by mult_nonzero.
      erewrite <- le_plus_minus_r with (m := roundup start N) at 2.
      rewrite upd_range_upd_range. f_equal.
      destruct (addr_eq_dec (start mod N) 0).
      - unfold roundup. rewrite divup_eq_div by auto. rewrite mul_div by mult_nonzero. omega.
      - rewrite roundup_eq by mult_nonzero. autorewrite with core; omega.
      - auto.
    + cancel.
    Unshelve.
      all : solve [exact unit | exact nil].
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indclear_multiple_blocks _ _ _ _ _ _ _) _) => apply indclear_multiple_blocks_ok : prog.

  Fixpoint indclear indlvl lxp bxp (root : addr) start len ms :=
    let N := NIndirect ^ indlvl in
    If (addr_eq_dec root 0) {
      Ret ^(ms, 0)
    } else {
      If (addr_eq_dec len 0) {
        Ret ^(ms, root)
      } else {
        let^ (lms, indbns) <- IndRec.read lxp root 1 (BALLOCC.MSLog ms);
        let ms := BALLOCC.upd_memstate lms ms in
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
    {< F Fm Fs m0 sm m l freelist IFs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs ir l *
            BALLOCC.rep bxp freelist ms) ]]] *
           [[ start + len <= length l ]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, ir')
           exists m' freelist' l' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' ir' l' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ incl freelist freelist' ]] * [[ l' = upd_range l start len $0 ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           ([[ ir = ir' ]] \/ [[ ir' = 0 ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indclear indlvl lxp bxp ir start len ms.
    Proof.
      induction indlvl.
      + cbn -[Nat.div].
        prestep. norml.
        denote indrep_n_helper as Hi.
        rewrite indrep_n_helper_length_piff in Hi; destruct_lift Hi.
        step.
        rewrite indrep_n_helper_0 in *. destruct_lifts.
        autorewrite with lists; auto.
        - hoare.
        - step.
          rewrite indrep_n_helper_valid by auto; cancel.
          rewrite firstn_oob by indrep_n_tree_bound.
          hoare.
      + cbn [indclear].
        step. step.
        {
          denote indrep_n_helper as Hi.
          rewrite indrep_n_helper_0 in Hi. destruct_lift Hi.
          rewrite listmatch_indrep_n_tree_empty'' in H.
          destruct_lift H.
          erewrite concat_hom_repeat by eauto using Forall_repeat.
          autorewrite with lists. reflexivity.
          rewrite repeat_length in *; auto.
        }
        step. solve [step].
        step.
        { rewrite indrep_n_helper_valid by auto. cancel. }
        rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *; simpl in *.
        rewrite firstn_oob by indrep_n_tree_bound.
        step.
        - safestep.
          erewrite concat_hom_length in * by eauto.
          match goal with |- context [listmatch _ _ ?l] =>
            replace (length l) with NIndirect in * by indrep_n_tree_bound end.
          indrep_n_extract; [cancel | indrep_n_tree_bound..].
          match goal with [H : context [listmatch _ _ ?l] |- context [selN ?l ?n] ] =>
            rewrite listmatch_extract with (i := n) in H
          end.
          indrep_n_tree_extract_lengths.
          denote (length _ = _) as Hl. rewrite Hl. omega.
          indrep_n_tree_bound.
          psubst.
          match goal with |- context [selN _ ?n] =>
            rewrite pred_fold_left_selN_removeN with (i := n) end. cancel.
          instantiate (1 := emp). cancel.
          safestep; rewrite ?natToWord_wordToNat, ?updN_selN_eq.
          * prestep. norm. cancel. cancel.
            assert (dummy = repeat $0 NIndirect).
            rewrite indrep_n_helper_0 in H8. destruct_lift H8. auto.
            subst.
            rewrite repeat_selN' in *.
            {
              match goal with H: context [concat ?l] |- _ => cut (length l = NIndirect) end.
              intuition auto. pred_apply. cancel.
              erewrite listmatch_isolate with (a := combine _ _).
              erewrite combine_updN_r with (x := IFs').
              rewrite removeN_updN, selN_updN_eq.
              cbn [fst snd].
              rewrite repeat_selN'. rewrite removeN_updN, selN_updN_eq.
              cancel.
              all: rewrite ?repeat_length in *; auto.
              indrep_n_tree_bound.
              indrep_n_tree_bound.
              indrep_n_tree_bound.
              indrep_n_tree_bound.
              indrep_n_tree_bound.

              eauto.
              erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega). auto.
              pred_apply.
              rewrite pred_fold_left_updN_removeN.
              cancel.
              indrep_n_tree_bound.
              match goal with H: context [listmatch _ _ ?l] |- length ?l = _ =>
                erewrite <- listmatch_length_l by (pred_apply' H; cancel)
              end.
              indrep_n_tree_bound.
            }
            repeat cancel.
            intuition auto.
            pred_apply. norm; intuition.
            rewrite combine_updN. cancel.
            rewrite listmatch_updN_removeN. cancel.
            rewrite updN_selN_eq. cancel.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            autorewrite with lists; omega.
            eauto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega). auto.
            auto.
            rewrite pred_fold_left_updN_removeN.
            pred_apply; cancel.
            replace (length dummy1) with NIndirect by indrep_n_tree_bound.
            indrep_n_tree_bound.
          * cancel.
          * prestep. norm. cancel. cancel. intuition auto.
            pred_apply. norm; intuition.
            rewrite combine_updN. cancel.
            rewrite listmatch_updN_removeN. repeat rewrite indrep_n_helper_0. cancel.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            autorewrite with lists; auto.
            eauto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega).
            auto.
            auto.
            rewrite pred_fold_left_updN_removeN by (substl (length dummy1); indrep_n_tree_bound).
            pred_apply; cancel.
            repeat cancel.
            intuition auto.
            pred_apply. norm; intuition.
            rewrite combine_updN. cancel.
            rewrite listmatch_updN_removeN. repeat rewrite indrep_n_helper_0. cancel.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            autorewrite with lists; auto.
            eauto.
            erewrite upd_range_concat_hom_small by (eauto; mult_nonzero; omega).
            auto.
            auto.
            rewrite pred_fold_left_updN_removeN by (substl (length dummy1); indrep_n_tree_bound).
            pred_apply; cancel.
          * cancel.
          * cancel.
      - step.
        psubst. cancel.
        step.
        unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed.
        simpl. intuition auto.
        (* indrep_n_tree_bound is not smart enough to switch from one tree to another *)
        match goal with [H : concat _ = _|- _] => apply f_equal with (f := @length _) in H end.
        autorewrite with lists in *.
        repeat erewrite concat_hom_length in * by eauto.
        erewrite <- combine_length_eq by eassumption.
        rewrite Nat.mul_cancel_r in *; auto.
        match goal with H: context [listmatch _ ?l] |- length ?l = _ =>
          erewrite listmatch_length_l by (pred_apply' H; cancel) end.
        match goal with H: _ = _ |- _ => rewrite H end.
        indrep_n_tree_bound.
        step.
    Grab Existential Variables.
    all : eauto.
    all: try constructor; solve [exact $0 | exact emp].
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
    {< F Fm m0 sm m bxp indbns Fs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ BALLOCC.bn_valid bxp ir ]] *
           [[ P -> ir = 0 ]] * [[ Q -> ir <> 0 ]] *
           [[[ m ::: (Fm * indrep_n_helper Fs bxp ir indbns) ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = indbns ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indput_get_blocks lxp is_alloc ir ms.
    Proof.
      unfold indput_get_blocks. unfold indrep_n_helper. intros.
      hoare. destruct_lifts. auto.
      destruct addr_eq_dec; try omega. cancel.
      apply firstn_oob.
      unfold IndRec.rep, IndRec.items_valid, IndSig.RALen in *.
      destruct addr_eq_dec; destruct_lifts; autorewrite with lists; omega.
    Qed.

  Local Hint Extern 0 ({{_}} Bind (indput_get_blocks _ _ _ _) _) => apply indput_get_blocks_ok : prog.

  (* This is a wrapper for IndRec.write that will use an alternate spec *)
  Definition indrec_write_blind lxp xp items ms :=
    IndRec.write lxp xp items ms.

  (* This is an alternate spec for IndRec.write that does not require IndRec.rep
    to hold beforehand. This allows blind writes to blocks that have not been
    initialized beforehand with IndRec.init *)
  Theorem indrec_write_blind_ok : forall lxp xp items ms,
    {< F Fm m0 sm m old,
    PRE:hm
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
          [[ IndRec.items_valid xp items ]] * [[ xp <> 0 ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) xp [old] ]]]
    POST:hm' RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
          [[[ m' ::: Fm * IndRec.rep xp items ]]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
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
    {< F Fm m0 sm m bxp Fs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[ BALLOCC.bn_valid bxp ir ]] *
           [[[ m ::: (Fm * indrep_n_helper Fs bxp ir indbns) ]]]
    POST:hm' RET: ms
           exists m' indbns', 
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm hm' *
           [[ indbns' = updN indbns to_grow ($ v) ]] *
           [[[ m' ::: (Fm * indrep_n_helper Fs bxp ir indbns') ]]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indput_upd_if_necessary lxp ir v indbns to_grow ms.
  Proof.
    unfold indput_upd_if_necessary. unfold BALLOCC.bn_valid.
    unfold indrec_write_blind.
    hoare.
    rewrite natToWord_wordToNat. rewrite updN_selN_eq. cancel.
    unfold indrep_n_helper. destruct (addr_eq_dec ir 0); try congruence. cancel.
    unfold indrep_n_helper. destruct (addr_eq_dec ir 0); try congruence. cancel.
    rewrite indrep_n_helper_valid_sm in * by auto.
    denote lift_empty as Hl. destruct_lift Hl. auto.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indput_upd_if_necessary _ _ _ _ _ _) _) => apply indput_upd_if_necessary_ok : prog.

  Fixpoint indput indlvl lxp bxp root off bn ms :=
    let N := NIndirect ^ indlvl in
    let is_alloc := (addr_eq_dec root 0) in
    let^ (ms, ir) <- If (is_alloc) {
        BALLOCC.alloc lxp bxp ms
      } else {
        Ret ^(ms, Some root)
      };
    match ir with
    | None => Ret ^(ms, 0)
    | Some ir =>
      match indlvl with
      | 0 => lms <- If (is_alloc) {
                      indrec_write_blind lxp ir ((repeat $0 NIndirect) ⟦ off := bn ⟧) (BALLOCC.MSLog ms)
                   } else {
                      IndRec.put lxp ir off bn (BALLOCC.MSLog ms)
                   };
        Ret ^((BALLOCC.upd_memstate lms ms), ir)
      | S indlvl' =>
        let to_grow := off / N in
        let^ (lms, indbns) <- indput_get_blocks lxp is_alloc ir (BALLOCC.MSLog ms);
        let ir_to_grow := #(selN indbns to_grow $0) in
        let^ (ms, v) <- indput indlvl' lxp bxp ir_to_grow (off mod N) bn 
                (BALLOCC.upd_memstate lms ms);
        If (addr_eq_dec v 0) {
          Ret ^(ms, 0)
        } else {
          lms <- indput_upd_if_necessary lxp ir v indbns to_grow (BALLOCC.MSLog ms);
          Ret ^((BALLOCC.upd_memstate lms ms), ir)
        }
      end
    end.

  Lemma indrep_n_helper_0_sm: forall bxp l Fs,
    indrep_n_helper Fs bxp 0 l =p=> [[ Fs <=p=> emp ]] * indrep_n_helper Fs bxp 0 l.
  Proof.
    intros.
    rewrite indrep_n_helper_0.
    cancel.
  Qed.

  Theorem indput_ok : forall indlvl lxp bxp ir off bn ms,
    {< F Fm Fs m0 sm m l freelist IFs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs ir l *
              BALLOCC.rep bxp freelist ms) ]]] *
           [[ off < length l ]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, ir')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           ([[ ir' = 0 ]] \/
           exists freelist' l' IFs',
           [[ ir = 0 \/ ir = ir' ]] *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' ir' l' *
             BALLOCC.rep bxp freelist' ms) ]]] *
           [[ incl freelist' freelist ]] * [[ l' = updN l off bn ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indput indlvl lxp bxp ir off bn ms.
    Proof.
      induction indlvl; intros; simpl.
      + step.
        - hoare.
          * unfold BALLOCC.bn_valid in *. intuition auto.
          * unfold BALLOCC.bn_valid in *. intuition auto.
          * or_r. norm. cancel.
            unfold BALLOCC.bn_valid in *; intuition auto.
            rewrite indrep_n_helper_valid by omega.
            pred_apply.
            rewrite indrep_n_helper_0. cancel.
            unfold BALLOCC.bn_valid. intuition.
            reflexivity.
            auto.
            rewrite indrep_n_helper_0 in *.
            destruct_lifts.
            psubst.
            pred_apply. cancel.
        - hoare.
          * rewrite indrep_n_helper_valid by omega. cancel.
          * or_r. cancel.
            rewrite indrep_n_helper_valid in * by omega. cancel.
            match goal with [H : context [?P] |- ?P] => destruct_lift H end. auto.
            match goal with [H : context [?P] |- ?P] => destruct_lift H end. auto.
      + step.
        - step. prestep. norm. congruence. congruence.
          cancel. intuition auto.
          { rewrite repeat_selN'. pred_apply. cancel.
            rewrite indrep_n_helper_0, indrep_n_tree_0.
            instantiate (1 := emp). cancel.
          }
          { rewrite repeat_length. apply Nat.mod_bound_pos; mult_nonzero. omega. }
          rewrite indrep_n_helper_0_sm in *.
          match goal with H: context [lift_empty] |- _ => destruct_lift H end.
          pred_apply; cancel.
          (* the spec given is for updates, not blind writes *)
          unfold indput_upd_if_necessary.
          repeat rewrite repeat_selN'. rewrite roundTrip_0.
          step; try solve [step].
          step. solve [repeat step].
          step.
          unfold BALLOCC.bn_valid in *. intuition auto.
          unfold BALLOCC.bn_valid in *. intuition auto.
          prestep. cancel.
          * or_r. norm. cancel.
            match goal with H: context [listmatch _ (combine _ _) ?l] |- _ =>
              assert (length l = NIndirect) by indrep_n_tree_bound end.
            intuition auto.
            pred_apply. norm. cancel.
            unfold BALLOCC.bn_valid in *.
            rewrite indrep_n_helper_valid by intuition auto.
            cancel.
            rewrite combine_updN.
            match goal with |- context[updN ?l ?i_] =>
              rewrite listmatch_isolate with (a := l) (i := i_), listmatch_updN_removeN
            end. rewrite selN_combine. cbn [fst snd]. rewrite repeat_selN'.
            rewrite indrep_n_tree_0.
            rewrite wordToNat_natToWord_idempotent'. cancel.
            rewrite indrep_n_tree_valid in * by auto.
            destruct_lifts.
            eauto using BALLOCC.bn_valid_goodSize.
            all: autorewrite with lists; auto.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            cbv; auto.
            reflexivity.
            intuition.
            indrep_n_tree_bound.
            reflexivity.
            eapply updN_concat'; auto.
            indrep_n_tree_bound.
            match goal with H: _ |- _ =>
              rewrite listmatch_indrep_n_tree_empty'' in H; destruct_lift H
            end.
            rewrite repeat_selN; eauto.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            pred_apply; cancel.
            psubst.
            rewrite pred_fold_left_updN_removeN by indrep_n_tree_bound.
            rewrite pred_fold_left_selN_removeN.
            match goal with H: _ |- _ =>
              rewrite indrep_n_helper_0_sm in H; destruct_lift H
            end.
            denote (_ <=p=> emp) as Hi. rewrite Hi; clear Hi.
            match goal with H: context [listmatch _ (combine (repeat _ _) _)] |- _ =>
              rewrite listmatch_isolate with (a := combine (repeat _ _) _) in H;
              [ erewrite selN_combine in H; cbn [fst snd] in H;
                [rewrite repeat_selN', roundTrip_0, indrep_n_tree_0 in H;
                destruct_lift H |..] |..]
            end.
            denote (_ <=p=> emp) as Hi. rewrite Hi; clear Hi.
            cancel.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
          * cancel.
          * cancel. cancel.
        - step.
          safestep.
          indrep_n_extract; [cancel | try solve [indrep_n_tree_bound]..].
          indrep_n_tree_bound.
          match goal with |- ?a mod ?b < ?c => replace c with b; auto end.
          symmetry. apply Forall_selN. eauto.
          indrep_n_tree_bound.
          psubst.
          match goal with |- context [selN _ ?I ?d] =>
            rewrite pred_fold_left_selN_removeN with (i := I);
            unify d (@emp _ addr_eq_dec bool); cancel
          end.
          match goal with [H : context [indrep_n_helper] |- _] =>
            pose proof H; rewrite indrep_n_helper_length_piff,
                            indrep_n_helper_valid in H by omega;
            destruct_lift H end.
          hoare.
          or_r. cancel.
          rewrite combine_updN. rewrite listmatch_updN_removeN. cbn [fst snd].
          rewrite wordToNat_natToWord_idempotent' by auto.
          cancel.
          indrep_n_tree_bound.
          indrep_n_tree_bound.
          autorewrite with lists; auto.
          rewrite pred_fold_left_updN_removeN. split; cancel.
          replace (length dummy1) with NIndirect by indrep_n_tree_bound.
          indrep_n_tree_bound.
          erewrite <- updN_concat.
          rewrite plus_comm, mult_comm, <- Nat.div_mod; auto.
          auto.
          auto.
          or_r. cancel.
          rewrite combine_updN. rewrite listmatch_updN_removeN. cbn [fst snd].
          rewrite wordToNat_natToWord_idempotent' by auto.
          cancel.
          indrep_n_tree_bound.
          indrep_n_tree_bound.
          autorewrite with lists; auto.
          rewrite pred_fold_left_updN_removeN. split; cancel.
          replace (length dummy1) with NIndirect by indrep_n_tree_bound.
          indrep_n_tree_bound.
          erewrite <- updN_concat.
          rewrite plus_comm, mult_comm, <- Nat.div_mod; auto.
          auto.
          auto.
          cancel.
    Grab Existential Variables. all : eauto.
        all: solve [exact nil | exact $0].
  Qed.

  Local Hint Extern 0 ({{_}} Bind (indput _ _ _ _ _ _ _) _) => apply indput_ok : prog.
  Opaque indput.

  (************** rep invariant *)

  Opaque indrep_n_tree.

  Definition indrep bxp Fs ir (indlist : list waddr) :=
    (exists Fs0 Fs1 Fs2, [[ Fs <=p=> Fs0 * Fs1 * Fs2 ]] *
      indrep_n_tree 0 bxp Fs0 (IRIndPtr ir) (firstn NIndirect indlist) *
      indrep_n_tree 1 bxp Fs1 (IRDindPtr ir) (firstn (NIndirect ^ 2) (skipn NIndirect indlist)) *
      indrep_n_tree 2 bxp Fs2 (IRTindPtr ir) (skipn (NIndirect + NIndirect ^ 2) indlist)
    )%pred.

  Definition rep bxp Fs (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp Fs ir indlist *
      [[ l = firstn (length l) ((IRBlocks ir) ++ indlist) ]] *
      [[ list_same $0 (skipn (length l) ((IRBlocks ir) ++ indlist)) ]] )%pred.

  Definition rep_direct bxp Fs (ir : irec) (l : list waddr) : @pred _ addr_eq_dec valuset :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l <= NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp Fs ir indlist *
      [[ l = firstn (length l) (IRBlocks ir) ]] *
      [[ list_same $0 (skipn (length l) (IRBlocks ir)) ]] *
      [[ list_same $0 indlist ]] )%pred.

  Definition rep_indirect bxp Fs (ir : irec) (l : list waddr) :=
    ( [[ length l = (IRLen ir) /\ length l <= NBlocks /\ length l > NDirect ]] *
      [[ length (IRBlocks ir) = NDirect ]] *
      exists indlist, indrep bxp Fs ir indlist *
      [[ l = (IRBlocks ir) ++ firstn (length l - NDirect) indlist ]] *
      [[ list_same $0 (skipn (length l - NDirect) indlist) ]] )%pred.


  Hint Resolve list_same_app_l.
  Hint Resolve list_same_app_r.
  Hint Resolve list_same_app_both.

  Lemma rep_piff_direct : forall bxp Fs ir l,
    length l <= NDirect ->
    rep bxp Fs ir l <=p=> rep_direct bxp Fs ir l.
  Proof.
    intros. unfold rep, rep_direct. split; cancel.
    - rewrite firstn_app_l in * by omega; auto.
    - rewrite skipn_app_l in * by omega; eauto.
    - rewrite skipn_app_l in * by omega; eauto.
    - substl l at 1; rewrite firstn_app_l by omega; auto.
    - rewrite skipn_app_l by omega; eauto.
  Qed.

  Lemma rep_piff_indirect : forall bxp Fs ir l,
    length l > NDirect ->
    rep bxp Fs ir l <=p=> rep_indirect bxp Fs ir l.
  Proof.
    unfold rep, rep_indirect; intros; split; cancel; try omega.
    - rewrite <- firstn_app_r; setoid_rewrite H3.
      replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    - rewrite skipn_app_r_ge in * by omega. congruence.
    - substl l at 1; rewrite <- firstn_app_r. setoid_rewrite H3.
      replace (NDirect + (length l - NDirect)) with (length l) by omega; auto.
    - rewrite skipn_app_r_ge by omega. congruence.
  Qed.

  Lemma rep_selN_direct_ok : forall F bxp Fs ir l m off,
    (F * rep bxp Fs ir l)%pred m ->
    off < NDirect ->
    off < length l ->
    selN (IRBlocks ir) off $0 = selN l off $0.
  Proof.
    unfold rep. intros; destruct_lift H.
    substl.
    rewrite selN_firstn by auto.
    rewrite selN_app1 by omega; auto.
  Qed.

  Theorem indrep_length_pimpl : forall bxp Fs ir l,
    indrep bxp Fs ir l <=p=> indrep bxp Fs ir l * [[ length l = NBlocks - NDirect ]].
  Proof.
    intros.
    unfold indrep.
    split; [> | cancel].
    intros m' H'. pred_apply. cancel.
    destruct_lift H'.
    repeat rewrite <- plus_assoc. rewrite minus_plus.
    indrep_n_tree_extract_lengths.
    erewrite <- firstn_skipn with (l := l). rewrite app_length. f_equal; eauto.
    erewrite <- firstn_skipn with (l := skipn _ _). rewrite app_length.
    f_equal; eauto. rewrite skipn_skipn'. auto.
  Qed.

  Theorem indrep_bxp_switch : forall bxp bxp' Fs xp ilist,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    indrep bxp Fs xp ilist <=p=> indrep bxp' Fs xp ilist.
  Proof.
    intros. unfold indrep.
    split; norm; intuition eauto; cbv [pred_fold_left stars fold_left].
    repeat match goal with [|- context [indrep_n_tree ?i] ] =>
      rewrite indrep_n_tree_bxp_switch with (indlvl := i) by eassumption
    end. cancel.
    repeat match goal with [|- context [indrep_n_tree ?i] ] =>
      rewrite indrep_n_tree_bxp_switch with (indlvl := i) by (symmetry; eassumption)
    end. cancel.
  Qed.

  Theorem indrep_0 : forall bxp Fs ir l,
    IRIndPtr ir = 0 -> IRDindPtr ir = 0 -> IRTindPtr ir = 0 ->
    indrep bxp Fs ir l <=p=> [[l = repeat $0 (NBlocks - NDirect)]] * [[ Fs <=p=> emp ]].
  Proof.
    unfold indrep. intros.
    repeat match goal with [H : _ = 0 |- _] => rewrite H end.
    repeat rewrite indrep_n_tree_0. simpl.
    repeat rewrite <- plus_assoc. rewrite minus_plus.
    rewrite mult_1_r in *.
    setoid_rewrite indrep_n_tree_0.
    split; norm; psubst; try cancel;
      rewrite Nat.mul_1_r in *; intuition eauto.
    erewrite <- firstn_skipn with (l := l).
    erewrite <- firstn_skipn with (l := skipn _ l).
    rewrite skipn_skipn'.
    repeat rewrite <- repeat_app.
    repeat (f_equal; eauto).
    split; cancel.
    split; cancel.
    all : repeat rewrite skipn_repeat;
          repeat rewrite firstn_repeat by lia; f_equal; lia.
  Qed.


  Lemma rep_keep_blocks : forall bxp Fs ir ir' l,
    IRIndPtr ir = IRIndPtr ir' ->
    IRDindPtr ir = IRDindPtr ir' ->
    IRTindPtr ir = IRTindPtr ir' ->
    IRLen ir = IRLen ir' ->
    IRBlocks ir = IRBlocks ir' ->
    rep bxp Fs ir l =p=> rep bxp Fs ir' l.
  Proof.
    intros.
    unfold rep, indrep.
    repeat match goal with H : _ = _ |- _ =>
      rewrite H in *; clear H
    end.
    reflexivity.
  Qed.

  Theorem rep_bxp_switch : forall bxp bxp' Fs xp ilist,
    BmapNBlocks bxp = BmapNBlocks bxp' ->
    rep bxp Fs xp ilist <=p=> rep bxp' Fs xp ilist.
  Proof.
    intros. unfold rep.
    split; norm; intuition eauto; cbv [pred_fold_left stars fold_left].
    all: rewrite indrep_bxp_switch.
    all: try cancel.
    all: eauto.
  Qed.


  Theorem xform_indrep : forall xp Fs ir l,
    crash_xform (indrep xp Fs ir l) <=p=> indrep xp Fs ir l.
  Proof.
    unfold indrep. intros.
    split; xform_norm.
    repeat rewrite xform_indrep_n_tree.
    cancel.
    cancel. xform_norm.
    cancel. xform_norm.
    cancel. xform_norm.
    repeat rewrite xform_indrep_n_tree.
    cancel; eauto.
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

  Definition indread_range_helper indlvl lxp bn start len ms :=
    let localstart := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    let maxlen := NIndirect ^ S indlvl in
    If (lt_dec localstart (start + len)) {
      If (lt_dec start (localstart + maxlen)) {
        let start' := start - localstart in
        let len' := len - (localstart - start) in
        let len'' := Nat.min len' (maxlen - start') in
        indread_range indlvl lxp bn start' len'' ms
      } else {
        Ret ^(ms, nil)
      }
    } else {
      Ret ^(ms, nil)
    }.

  Definition read_range lxp ir start len ms :=
    rdir <- Ret (firstn len (skipn start (IRBlocks ir)));
    let len := len - (NDirect - start) in
    let start := start - NDirect in
    let^ (ms, rind) <- indread_range_helper 0 lxp (IRIndPtr ir) start len ms;
    let^ (ms, rdind) <- indread_range_helper 1 lxp (IRDindPtr ir) start len ms;
    let^ (ms, rtind) <- indread_range_helper 2 lxp (IRTindPtr ir) start len ms;
    Ret ^(ms, rdir ++ rind ++ rdind ++ rtind).

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
                         (upd_range_fast (IRBlocks ir) nl (NDirect - nl) $0))
    } else {
      let ol' := ol - NDirect in
      let nl' := nl - NDirect in
      let^ (ms, indptr, dindptr, tindptr) <- indshrink lxp bxp ir nl' ms;
      Ret ^(ms, upd_irec ir nl indptr dindptr tindptr
                         (upd_range_fast (IRBlocks ir) nl (NDirect - nl) $0))
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
    {< F Fm IFs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]] *
           [[ off < length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} get lxp ir off ms.
  Proof.
    unfold get.
    step.
    step.
    eapply rep_selN_direct_ok; eauto.
    prestep; norml.
    rewrite rep_piff_indirect in * by omega.
    unfold rep_indirect, indrep in *. destruct_lifts.
    indrep_n_tree_extract_lengths.
    hoare.
    all : substl l.
    all : repeat rewrite selN_app2 by omega.
    all : repeat rewrite selN_firstn by omega.
    all : repeat rewrite skipn_selN.
    all : repeat (congruence || omega || f_equal).
  Qed.

  Theorem read_ok : forall lxp bxp ir ms,
    {< F Fm IFs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm hm'
    >} read lxp ir ms.
  Proof.
    unfold read.
    step; denote rep as Hx.
    step.
    rewrite rep_piff_direct in Hx; unfold rep_direct in Hx; destruct_lift Hx.
    substl; substl (length l); auto.
    unfold rep in H; destruct_lift H; omega.

    unfold rep, indrep in Hx. destruct_lifts.
    indrep_n_tree_extract_lengths.
    hoare.
    rewrite app_assoc with (l := firstn _ _).
    rewrite <- firstn_sum_split. rewrite firstn_skipn.
    congruence.
  Qed.

  Theorem indread_range_helper_ok : forall lxp bn indlvl start len ms,
    let localstart := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    {< F Fm IFs m0 sm m l bxp,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs bn l) ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           let len' := (len - (localstart - start)) in
           [[ r = firstn len' (skipn (start - localstart) l) ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indread_range_helper indlvl lxp bn start len ms.
  Proof.
    unfold indread_range_helper.
    step; indrep_n_tree_extract_lengths; hoare.
    match goal with H : length l = _ |- _ => setoid_rewrite <- H end.
    let H := fresh in
    edestruct Min.min_spec as [ [? H]|[? H] ]; rewrite H; clear H.
    reflexivity.
    rewrite firstn_oob.
    rewrite firstn_oob; auto.
    autorewrite with core.
    omega.
    autorewrite with core.
    omega.
    rewrite skipn_oob, firstn_nil by omega. auto.
    rewrite sub_le_eq_0 by omega.
    auto.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indread_range_helper _ _ _ _ _ _ ) _) => apply indread_range_helper_ok : prog.

(*
  Theorem read_range_ok : forall lxp bxp ir start len ms,
    {< F Fm IFs m0 sm m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]] *
           [[ start + len <= length l ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm hm' *
           [[ r = firstn len (skipn start l) ]]
    CRASH:hm' LOG.intact lxp F m0 sm hm'
    >} read_range lxp ir start len ms.
  Proof.
    unfold read_range, rep, indrep.
    hoare.
    autorewrite with core.
    substl l.
    match goal with H: context [firstn NIndirect ?l] |- _ =>
      rename l into ind
    end.
    rewrite firstn_app.
    rewrite skipn_app_split.
    rewrite firstn_app.
    f_equal.
    rewrite firstn_double_skipn by omega; auto.
    (* TODO finish proving this and use read_range to implement BFILE.shrink *)
  Abort.
*)

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

  Theorem upd_len_indrep : forall bxp Fs ir l n,
    indrep bxp Fs ir l <=p=> indrep bxp Fs (upd_len ir n) l.
  Proof.
    intros.
    unfold indrep. autorewrite with core. auto.
  Qed.

  Theorem upd_len_direct_indrep : forall bxp Fs ir l n b,
    indrep bxp Fs ir l <=p=> indrep bxp Fs (upd_irec ir n (IRIndPtr ir) (IRDindPtr ir) (IRTindPtr ir) b) l.
  Proof.
    intros.
    unfold indrep. autorewrite with core. auto.
    all: eauto using get_ind_goodSize, get_dind_goodSize, get_tind_goodSize.
  Qed.

  Theorem indshrink_helper_ok : forall lxp bxp bn nl indlvl ms,
    let start := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    {< F Fm Fs IFs m0 sm m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs bn l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, r)  exists m' freelist' IFs' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' r l' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ l' = upd_range l (nl - start) (length l - (nl - start)) $0 ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indshrink_helper indlvl lxp bxp bn nl ms.
  Proof.
    unfold indshrink_helper.
    prestep. norml.
    indrep_n_tree_extract_lengths.
    hoare.
    replace (_ - (_ - _)) with 0 by omega. rewrite upd_range_0. auto.
  Qed.

  Local Hint Extern 1 ({{_}} Bind (indshrink_helper _ _ _ _ _ _ ) _) => apply indshrink_helper_ok : prog.

  Theorem indshrink_ok : forall lxp bxp ir nl ms,
    {< F Fm Fs IFs0 IFs1 IFs2 m0 sm m l0 l1 l2 freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ nl <= length (l0 ++ l1 ++ l2) ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp IFs0 (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp IFs1 (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp IFs2 (IRTindPtr ir) l2 *
                           BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs0 * IFs1 * IFs2 * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, indptr', dindptr', tindptr')
           exists m' freelist' l0' l1' l2' IFs0' IFs1' IFs2',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp IFs0' indptr' l0' *
                            indrep_n_tree 1 bxp IFs1' dindptr' l1' *
                            indrep_n_tree 2 bxp IFs2' tindptr' l2' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ l0' ++ l1' ++ l2' = upd_range (l0 ++ l1 ++ l2) nl (length (l0 ++ l1 ++ l2) - nl) $0 ]] *
           [[ (Fs * IFs0' * IFs1' * IFs2' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
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
    {< F Fm Fs IFs m0 sm m l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[[ m ::: (Fm * rep bxp IFs ir l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, r)  exists m' freelist' l' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' r l' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           exists ind dind tind dirl, [[ r = upd_irec ir ((IRLen ir) - nr) ind dind tind dirl ]] *
           [[ l' = firstn (IRLen ir - nr) l ]] *
           [[ incl freelist freelist' ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} shrink lxp bxp ir nr ms.
  Proof.
    unfold shrink. intros.
    repeat rewrite upd_range_fast_eq.
    prestep; norml.
    denote rep as Hx. unfold rep in Hx. destruct_lifts.
    cancel.
    + (* case 1: all in direct blocks *)
      step. unfold rep.
      autorewrite with core. cancel.
      - apply upd_len_direct_indrep.
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
      destruct_lift Hx.
      hoare.
      - repeat rewrite app_length.
        indrep_n_tree_extract_lengths. omega.
      - psubst. cancel.
      - unfold rep, indrep. autorewrite with core; auto.
        cancel; rewrite mult_1_r in *.
        rewrite indrep_n_length_pimpl with (indlvl := 0).
        rewrite indrep_n_length_pimpl with (indlvl := 1).
        rewrite indrep_n_length_pimpl with (indlvl := 2). cancel. rewrite mult_1_r in *.
        substl (NIndirect * NIndirect). substl NIndirect.
        rewrite firstn_app2. rewrite skipn_app_r. repeat rewrite skipn_app. rewrite firstn_app2.
        cancel.
        all : try rewrite upd_range_length.
        all : eauto.
        all : rewrite ?min_l by omega; try omega.
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
      - cancel.
    Grab Existential Variables.
    all: eauto.
  Qed.

  Theorem indgrow_ok : forall lxp bxp ir off bn ms,
    {< F Fm Fs m0 sm m l0 l1 l2 freelist IFs0 IFs1 IFs2,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ off < NBlocks - NDirect ]] * [[ bn <> $0 ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp IFs0 (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp IFs1 (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp IFs2 (IRTindPtr ir) l2 * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs0 * IFs1 * IFs2 * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, v, indptr', dindptr', tindptr')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           ([[ v = 0 ]] \/ [[ v <> 0 ]] *
           exists freelist' l0' l1' l2' IFs0' IFs1' IFs2',
           [[ updN (l0 ++ l1 ++ l2) off bn = l0' ++ l1' ++ l2' ]] *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp IFs0' indptr' l0' *
                            indrep_n_tree 1 bxp IFs1' dindptr' l1' *
                            indrep_n_tree 2 bxp IFs2' tindptr' l2' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * IFs0' * IFs1' * IFs2' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist' freelist ]])
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
    >} indgrow lxp bxp ir off bn ms.
  Proof.
    unfold indgrow. prestep. norml.
    indrep_n_tree_extract_lengths.
    hoare.
    all: match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
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
    {< F Fm Fs m0 sm m IFs l freelist,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm hm *
           [[ length l < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp IFs ir l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:hm' RET:^(ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' \/
           exists freelist' ir' IFs',
           [[ r = OK ir' ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm hm' *
           [[[ m' ::: (Fm * rep bxp IFs' ir' (l ++ [bn]) * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ IRAttrs ir' = IRAttrs ir /\ length (IRBlocks ir') = length (IRBlocks ir) ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist' freelist ]]
    CRASH:hm'  LOG.intact lxp F m0 sm hm'
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
    unfold rep_direct in Hx; destruct_lift Hx.
    cancel.
    or_r; cancel.
    rewrite rep_piff_direct by (autorewrite with lists; simpl; omega).
    unfold rep_direct; autorewrite with core lists; simpl.
    cancel; try omega.
    unfold indrep.
    intros m' H'. destruct_lift H'. pred_apply. autorewrite with core. cancel.
    all : auto.
    substl l at 1. substl (length l).
    apply firstn_app_updN_eq; omega.
    rewrite skipN_updN' by omega.
    eapply list_same_skipn_ge; try eassumption. omega.
    autorewrite with core lists; auto.

    (* update indirect blocks *)
    step.
    + (* write 0 block *)
      unfold rep in *. destruct_lift Hx.
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
      - eauto.
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
      unfold rep in *. destruct_lift Hx.
      rewrite indrep_length_pimpl in *. unfold indrep in *. destruct_lifts.
      indrep_n_tree_extract_lengths.
      hoare.
      - psubst; cancel.
      - rewrite <- skipn_skipn' in *. repeat rewrite firstn_skipn in *.
        indrep_n_tree_extract_lengths.
        or_r. cancel; autorewrite with core.
        rewrite <- skipn_skipn'.
        rewrite firstn_app2. rewrite skipn_app_l. rewrite skipn_oob. rewrite app_nil_l.
        rewrite firstn_app2. rewrite skipn_app_l. rewrite skipn_oob. rewrite app_nil_l.
        (* `cancel` calls `simpl` which raises a Not_found exception here; don't know why *)
        norm; intuition cancel.
        all : repeat rewrite app_length; try solve [auto | simpl; omega].
       -- apply le_nblocks_goodSize. simpl. rewrite mult_1_r. omega.
       -- split; cancel.
       -- substl l at 1. cbn.
          match goal with [H : updN _ _ _ = _ |- _] => rewrite <- H end.
          rewrite plus_comm. erewrite firstn_S_selN.
          repeat rewrite firstn_app_le by omega.
          rewrite firstn_updN_oob by omega. rewrite selN_app2 by omega.
          erewrite eq_trans with (x := _ - _); [> | reflexivity |].
          rewrite selN_updN_eq by omega. reflexivity.
          all : try rewrite app_length, length_updN; omega.
       -- cbn.
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

  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (@selN (@pred _ _ bool) ?l _ _) (@selN (@pred _ _ bool) ?l _ _)) => constructor : okToUnify.

  Lemma rep_IFs_sync_invariant: forall bxp IFs ir iblocks m F,
    (F * rep bxp IFs ir iblocks)%pred m ->
    sm_sync_invariant IFs.
  Proof.
    unfold rep, indrep.
    intros.
    destruct_lifts.
    eapply sm_sync_invariant_piff; eauto.
    repeat eapply sm_sync_invariant_sep_star;
      eapply indrep_n_tree_sm_sync_invariant with (m := m).
    all: pred_apply; cancel.
  Qed.

  Theorem xform_rep : forall xp Fs ir l,
    crash_xform (rep xp Fs ir l) <=p=> rep xp Fs ir l.
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
