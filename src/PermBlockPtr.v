Require Import Arith.
Require Import Mem Pred.
Require Import Word.
Require Import Omega.
Require Import Lia.
Require Import Rounding.
Require Import Errno.

Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.

Require Import ListPred.
Require Import FSLayout.
Require Import PermDiskSet.
Require Import PermLog.
Require Import PermBalloc.

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

  Hint Extern 0  (exists _, hashmap_subset _ _ _) => solve_hashmap_subset.
  Hint Extern 0  (block_mem_subset _ =p=> (fun _ => _ c= _)) => solve_blockmem_subset.
  Hint Extern 0 (EqDec handle) => unfold EqDec; apply handle_eq_dec.

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
  Hint Extern 0 (okToUnify (IndRec.rep _ _ _) (IndRec.rep _ _ _)) => constructor : okToUnify.

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
     else [[ BALLOCC.bn_valid bxp ibn ]] *
          IndRec.rep ibn (repeat Public (length (IndRec.Defs.ipack iblocks))) iblocks *
           exists b, [[ (Fs <=p=> ibn |-> b) ]]
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

    Ltac psubst :=
    repeat match goal with p: pred |- _ =>
      match goal with
      | H: p <=p=> _ |- _ =>
        rewrite H in *; clear H; clear p
      | H: _ <=p=> p |- _ =>
        rewrite <- H in *; clear H; clear p
      end
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

  Theorem indrep_n_helper_valid : forall bxp bn Fs l,
    bn <> 0 -> indrep_n_helper Fs bxp bn l <=p=> [[ BALLOCC.bn_valid bxp bn ]] * IndRec.rep bn (repeat Public (length (IndRec.Defs.ipack l))) l * [[ exists b, (Fs <=p=> bn |->b) ]].
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

  Theorem indrep_n_tree_0 : forall indlvl bxp Fs l,
    indrep_n_tree indlvl bxp Fs 0 l <=p=> [[ l = repeat $0 (NIndirect ^ S indlvl)]] * [[ Fs <=p=> emp ]].
  Proof.
    induction indlvl; simpl; intros.
    rewrite mult_1_r, indrep_n_helper_0; split; cancel.
    split.
    intros m' H'.
    destruct_lift H'.
    rewrite indrep_n_helper_0 in H.
    rewrite listmatch_length_pimpl in H; autorewrite with lists in *.
    destruct_lift H.
    rewrite repeat_length, min_l in * by omega.
    eapply listmatch_lift_r with (F := fun x y => ([[snd x <=p=> emp ]])%pred) in H.
    rewrite listmatch_lift_l with (F := fun x y => emp) (P := fun x => snd x <=p=> emp) in H.
    rewrite listmatch_emp in H by cancel.
    destruct_lifts.
    rewrite Forall_combine_r with (G := fun x => x <=p=> emp) in H2.
    2: autorewrite with lists; congruence.
    2: reflexivity.
    rewrite pred_fold_left_Forall_emp in H4 by eauto.
    (* working around a coq bug: "Conversion test raised an anomaly" when using 'pred_apply; cancel' *)
    eapply sep_star_lift_apply'.
    unfold lift_empty; intuition.
    erewrite concat_hom_repeat; eauto.
    psubst.
    split; cancel.
    intros; split; cancel.
    intros; simpl.
    destruct_lifts.
    destruct x.
    eapply in_combine_l in H2 as ?.
    erewrite repeat_spec with (y := w); eauto.
    rewrite IHindlvl. split; cancel.
    norm. eassign Fs. cancel.
    rewrite indrep_n_helper_0.
    cancel; eauto.
    instantiate (l_part := repeat (repeat $0 _) _).
    rewrite listmatch_lift_r with (F := fun x y => ([[ snd x <=p=> emp ]])%pred) (P := fun y => length y = NIndirect ^ S indlvl).
    rewrite listmatch_lift_l with (F := fun x y => emp%pred) (P := fun y => snd y <=p=> emp).
    rewrite listmatch_emp_piff by auto.
    autorewrite with lists.
    cancel.
    apply Forall_repeat.
    autorewrite with lists. reflexivity.
    rewrite Forall_combine_r with (G := fun x => x <=p=> emp).
    apply Forall_repeat.
    reflexivity.
    repeat rewrite repeat_length; eauto.
    reflexivity.
    split; cancel.
    intro x; destruct x; intros.
    eapply in_combine_l in H.
    erewrite repeat_spec with (y := w) by eauto.
    rewrite IHindlvl. split; cancel. subst. autorewrite with lists. auto.
    eapply repeat_spec; eauto.
    intuition subst.
    rewrite repeat_length; auto.
    rewrite repeat_length; omega.
    psubst.
    rewrite pred_fold_left_Forall_emp.
    split; cancel.
    eapply Forall_repeat; auto.
    erewrite concat_hom_repeat; autorewrite with lists; auto.
    rewrite min_l by omega.
    eauto.
    apply Forall_repeat. auto.
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

  Lemma in_combine_repeat_l : forall A B (a : A) n (b : list B) x,
    In x (combine (repeat a n) b) ->
    fst x = a.
  Proof.
    induction n; cbn; intuition.
    destruct b; cbn in *; intuition eauto.
    subst; auto.
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

  Lemma indrep_n_helper_length : forall Fs bxp ibn l m,
    indrep_n_helper Fs bxp ibn l m -> length l = NIndirect.
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
    split; [> intros m H; apply indrep_n_helper_length in H as HH; pred_apply | ]; cancel.
  Qed.

  Lemma indrep_n_length_pimpl : forall indlvl bxp ibn Fs l,
    indrep_n_tree indlvl bxp Fs ibn l <=p=>
    [[ length l = NIndirect ^ (S indlvl) ]] * indrep_n_tree indlvl bxp Fs ibn l.
  Proof.
    induction indlvl; simpl; intros.
    intros; split; intros m H; destruct_lift H; pred_apply; cancel.
    erewrite indrep_n_helper_length; eauto; omega.
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
                                                                                        
Theorem indrep_n_helper_pts_piff :
  forall Fs bxp ir l,
    ir <> 0 -> indrep_n_helper Fs bxp ir l <=p=> [[ length l = NIndirect ]] *
               [[ BALLOCC.bn_valid bxp ir ]] * (exists b, [[ Fs <=p=> ir |->b ]]) *
                ir |-> ((Public, IndRec.Defs.block2val l), []).
Proof.
  intros.
  unfold indrep_n_helper, IndRec.rep. destruct addr_eq_dec; try omega.
  unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
  rewrite mult_1_l. unfold Rec.well_formed. simpl.
  split; cancel.
  rewrite IndRec.Defs.ipack_one by (unfold IndRec.Defs.item in *; auto);
  simpl; cancel.
  eauto.
  rewrite IndRec.Defs.ipack_one by (unfold IndRec.Defs.item in *; auto);
  simpl; cancel.
  apply repeat_length.
  eauto.
Qed.

  Lemma indrep_n_tree_balloc_goodSize: forall F1 F2 bxp freelist ms indlvl Fs ir l m1 m2,
    (F1 * BALLOCC.rep bxp freelist ms)%pred m1 ->
     (F2 * indrep_n_tree indlvl bxp Fs ir l)%pred m2 ->
      goodSize addrlen ir.
  Proof.
    intros.
    destruct (addr_eq_dec ir 0); subst.
    apply PermDiskLogPadded.goodSize_0.
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
  Lemma listmatch_combine_l_length: forall A B C AT AEQ V (prd : _ -> _ -> @pred AT AEQ V)
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


  Theorem xform_indrep_n_helper : forall Fs bxp ir l,
    crash_xform (indrep_n_helper Fs bxp ir l) <=p=> indrep_n_helper Fs bxp ir l.
  Proof.
    unfold indrep_n_helper. intros.
    destruct addr_eq_dec; xform_norm.
    - auto.
    - rewrite IndRec.xform_rep.
      split; norml.
      unfold stars; simpl.
      rewrite crash_xform_exists_comm.
      setoid_rewrite crash_xform_lift_empty.
      cancel; eauto.
      cancel; eauto.
      xcrash; eauto.
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

  Ltac indrep_n_tree_bound_step :=
    match goal with
    | [ |- _ ] => reflexivity
    | [ |- _ ] => assumption
    | [ |- Forall _ _ ] => auto
    | [ H : context [IndRec.Defs.item] |- _ ] => unfold IndRec.Defs.item in *; simpl Rec.data in *
    | [ |- context [IndRec.Defs.item] ] => unfold IndRec.Defs.item in *; simpl Rec.data in *
    | [ |- _ ] => progress autorewrite with core lists
    | [ |- ?a * ?b = ?c * ?b ] => rewrite Nat.mul_cancel_r by mult_nonzero
    | [ |- ?a * ?b = ?b * ?c ] => rewrite mult_comm with (n := b) (m := c)
    | [ |- ?b * ?a = ?b * ?c ] => rewrite mult_comm with (n := b) (m := a)
    | [ H : ?a < ?b * ?c |- ?a < ?d * ?c] => assert (d = b); [ | congruence ]
    | [ H : context [indrep_n_tree _ _ _ _ ?l] |- context [length ?l] ] =>
      rewrite indrep_n_tree_length in H; destruct_lift H
    | [ H : context [indrep_n_helper _ _ _ ?l] |- context [length ?l] ] =>
      replace (length l) with NIndirect in * by (rewrite indrep_n_helper_length_piff in H; destruct_lift H; auto)
    | [ H : context [indrep_n_helper _ _ _ ?l], H' : context [length ?l] |- _ ] =>
      replace (length l) with NIndirect in * by (rewrite indrep_n_helper_length_piff in H; destruct_lift H; auto)
    | [ |- ?off / ?N < ?N' ] => apply Nat.div_lt_upper_bound; [ mult_nonzero |]
    | [ |- ?off < ?N * NIndirect] => rewrite mult_comm
    | [ H: context [length (combine ?a ?b)] |- _ ]=>
      replace (length (combine a b)) with (Nat.min (length a) (length b)) in * by
        (rewrite combine_length; reflexivity)
    | [ |- context [length (combine ?a ?b)] ]=>
      replace (length (combine a b)) with (Nat.min (length a) (length b)) in * by
        (rewrite combine_length; reflexivity)

    (* try to get an argument to indrep_n_tree or indrep_n_helper *)
    | [ H : context [listmatch _ (combine ?A _) ?c], H' : context [length ?c] |- _ ] =>
      replace (length c) with (length A) in * by (
        rewrite listmatch_combine_l_length with (a := A) in H; destruct_lift H; omega)
    | [ H : context [listmatch _ (combine _ ?B) ?c], H' : context [length ?c] |- _ ] =>
      replace (length c) with (length B) in * by (
        rewrite listmatch_combine_l_length with (b := B) in H; destruct_lift H; omega)

    | [ H : context [listmatch _ (combine ?A _) ?c] |- context [length ?c] ] =>
      replace (length c) with (length A) in * by (
        rewrite listmatch_combine_l_length with (a := A) in H; destruct_lift H; omega)
    | [ H : context [listmatch _ (combine _ ?B) ?c] |- context [length ?c] ] =>
      replace (length c) with (length B) in * by (
        rewrite listmatch_combine_l_length with (b := B) in H; destruct_lift H; omega)

    | [ H : context [listmatch _ ?A ?b] |- context [length ?b] ] =>
      replace (length b) with (length A) in * by (
        rewrite listmatch_length_pimpl with (a := A) in H; destruct_lift H; auto)
    | [ H : context [listmatch _ ?A ?b], H': context [length ?b] |- _ ] =>
      replace (length b) with (length A) in * by (
        rewrite listmatch_length_pimpl with (a := A) in H; destruct_lift H; auto)

    | [ H : context [lift_empty _] |- _ ] => progress destruct_lift H
    | [ H : context [length (concat ?l)] |- _ ] => erewrite concat_hom_length in H by eauto
    | [ |- context [length (concat _)] ] => rewrite concat_hom_length by eauto
    | [ |- context [Nat.min _ _] ] => rewrite min_l by omega
    | [ H: context [Nat.min _ _] |- _ ] => rewrite min_l in H by omega
    | [ |- _ ] => omega
    | [ |- ?a < ?b * ?c ] => rewrite mult_comm; omega
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
      let^ (ms, v) <- IndRec.get lxp bn (off / divisor) ms;;
      match indlvl with
      | 0 => Ret ^(ms, v)
      | S indlvl' => indget indlvl' lxp (# v) (off mod divisor) ms
      end
  }.
 Theorem indget_ok :
  forall indlvl lxp bxp bn off ms pr,
  {< F Fm Fs m0 sm m l,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp bn l ]]] *
           [[ off < length l ]]
    POST:bm', hm', RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[ r = selN l off $0 ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} indget indlvl lxp bn off ms.
  Proof. 
    induction indlvl; simpl.
    + repeat safestep; autorewrite with core; eauto.
      erewrite LOG.rep_hashmap_subset; eauto.
      rewrite indrep_n_helper_0 in *. destruct_lifts. auto.
      rewrite indrep_n_helper_valid by omega. cancel.
      erewrite LOG.rep_hashmap_subset; eauto.
    + repeat safestep; autorewrite with core; try eassumption; clear IHindlvl.
      erewrite LOG.rep_hashmap_subset; eauto.
    - erewrite indrep_n_tree_length in H5; eauto. (* by eauto. *)
      erewrite indrep_n_tree_repeat_concat; eauto.
      all: rewrite indrep_n_helper_0 in *; destruct_lifts;
      rewrite repeat_length in *; auto.
    - indrep_n_tree_bound.
    - rewrite indrep_n_helper_valid by omega.
      cancel.
    - apply BALLOC.Alloc.can_access_repeat_public_selN.
    - rewrite listmatch_isolate with (i := off / (NIndirect ^ S indlvl))
        by indrep_n_tree_bound.
      rewrite selN_combine by indrep_n_tree_bound.
      cbn [fst snd]; cancel.
    - match goal with [H : context [indrep_n_helper] |-_] => assert (HH := H) end.
      match goal with |- ?a mod ?n < ?b => replace b with n; auto end.
      rewrite listmatch_extract in HH; autorewrite with lists in *.
      rewrite indrep_n_length_pimpl in HH.
      destruct_lift HH. eauto.
      indrep_n_tree_bound.
    - apply selN_selN_hom; eauto.
      indrep_n_tree_bound.
    - rewrite <- H1; cancel; eauto. 
      Unshelve.
      all: eauto.
      exact ($0, emp).
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indget _ _ _ _ _ ) _) => apply indget_ok : prog.
  Opaque indget.

  Fixpoint indread (indlvl : nat) lxp (ir : addr) ms :=
    If (addr_eq_dec ir 0) {
      Ret ^(ms, repeat $0 (NIndirect ^ S indlvl))
    } else {
      let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;;
      match indlvl with
        | 0 => Ret ^(ms, indbns)
        | S indlvl' =>
          let N := (NIndirect ^ (S indlvl')) in
          r <- ForEach b indbns' (rev indbns)
            Blockmem bm
            Hashmap hm
            Ghost [ F Fm Fs fsl iblocks l_part l bxp crash m0 sm m ]
            Loopvar [ ms r ]
            Invariant
              exists remlen, [[ remlen = length indbns' ]] *
              LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
              [[[ m ::: Fm * indrep_n_helper Fs bxp ir iblocks *
                        listmatch (fun x l' => indrep_n_tree indlvl' bxp (snd x) (# (fst x)) l')
                          (combine iblocks fsl) l_part ]]] *
              [[ r = skipn (remlen * (NIndirect ^ indlvl)) l ]]
            OnCrash crash
            Begin
              let^ (ms, v) <- indread indlvl' lxp (# b) ms;;
              Ret ^(ms, v ++ r)
            Rof ^(ms, nil);;
            Ret r
      end
    }.

Theorem indread_ok :
  forall indlvl lxp bxp ir ms pr,
    {< F Fm Fs m0 sm m l,
    PERM:pr 
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: Fm * indrep_n_tree indlvl Fs bxp ir l ]]]
    POST:bm', hm', RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[ r = l ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} indread indlvl lxp ir ms.
  Proof. 
    induction indlvl; simpl.
    + hoare.
      erewrite LOG.rep_hashmap_subset; eauto.
      - rewrite indrep_n_helper_0 in *. destruct_lifts. rewrite mult_1_r. auto.
      - rewrite indrep_n_helper_valid by auto; cancel.
      - destruct (repeat Public (length (IndRec.Defs.ipack l))) eqn:D; eauto.
        apply Forall_nil.
        destruct (length (IndRec.Defs.ipack l)); simpl in *;
        inversion D; subst; eauto.
        constructor; auto.
        apply Forall_nil.
      - erewrite LOG.rep_hashmap_subset; eauto.
      - rewrite indrep_n_helper_length_piff in *.
        destruct_lifts. unfold IndRec.Defs.item in *; simpl in *.
        rewrite firstn_oob by omega. auto.
    + hoare.
      erewrite LOG.rep_hashmap_subset; eauto.
      - erewrite indrep_n_tree_repeat_concat; eauto. auto.
        rewrite indrep_n_helper_0 in *; destruct_lifts; cleanup;
        rewrite repeat_length; auto.
      - rewrite indrep_n_helper_valid by omega. cancel.
      - destruct (repeat Public (length (IndRec.Defs.ipack dummy))) eqn:D; eauto.
        apply Forall_nil.
        destruct (length (IndRec.Defs.ipack dummy)); simpl in *;
        inversion D; subst; eauto.
        constructor; auto.
        apply Forall_nil.
      - rewrite firstn_oob by indrep_n_tree_bound.
        autorewrite with list.
        rewrite skipn_oob; auto.
        erewrite concat_hom_length by eauto.
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
      - erewrite LOG.rep_hashmap_subset; eauto.
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
        rewrite combine_length_eq in H20.
        autorewrite with list in *; cbn [length] in *; omega.
        autorewrite with list; cbn [length]. omega.
      - rewrite <- H1; cancel; eauto.
      - erewrite LOG.rep_hashmap_subset; eauto.
      - eassign (false_pred(AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)).
        unfold false_pred; cancel.
    Grab Existential Variables.
    all : eauto.
    exact tt.
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indread _ _ _ _ ) _) => apply indread_ok : prog.
  Opaque indread.

  
  Fixpoint indclear_all indlvl lxp bxp root ms :=
    If (addr_eq_dec root 0) {
      Ret ms
    } else {
      let N := NIndirect ^ indlvl in
      ms <- match indlvl with
      | 0 => Ret ms
      | S indlvl' =>
        let^ (lms, indbns) <- IndRec.read lxp root 1 (BALLOCC.MSLog ms);;
        let msn := BALLOCC.upd_memstate lms ms in
        let^ (msn) <- ForEach bn indbns' indbns
          Blockmem bm
          Hashmap hm
          Ghost [ F Fm Fs bxp crash m0 sm freelist l_part fsl ]
          Loopvar [ msn ]
          Invariant
            exists m freelist',
            LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog msn) sm bm hm *
            let n := length indbns - length indbns' in
            [[[ m ::: Fm * listmatch (fun x l' => indrep_n_tree indlvl' bxp (snd x) (# (fst x)) l')
                          (combine (skipn n indbns) (skipn n fsl)) (skipn n l_part)
                         * BALLOCC.rep bxp freelist' msn ]]] *
            [[ incl freelist freelist' ]] *
            [[ (Fs * pred_fold_left (skipn n fsl) * BALLOCC.smrep freelist')%pred sm ]]
          OnCrash crash
          Begin
            msn <- indclear_all indlvl' lxp bxp # bn msn;;
            Ret ^(msn)
          Rof ^(msn);;
          Ret msn
      end;;
      BALLOCC.free lxp bxp root ms
    }.      

Theorem indclear_all_ok :
    forall indlvl lxp bxp ir ms pr,
    let N := NIndirect ^ indlvl in
    {< F Fm Fs IFS m0 sm m l freelist,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFS ir l *
              BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFS * BALLOC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET: ms
           exists m' freelist' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp emp 0 l' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * BALLOC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indclear_all indlvl lxp bxp ir ms.
    Proof.
      induction indlvl; simpl.
      + step.
        step.
        step.
        erewrite LOG.rep_hashmap_subset; eauto.
        pred_apply;
        repeat rewrite indrep_n_helper_0. cancel.        
        erewrite indrep_n_helper_0 in *.
        denote lift_empty as Hf; destruct_lift Hf.
        psubst; auto.
        destruct (addr_eq_dec ir 0). step.
        step.
        prestep; norm.
        unfold stars; simpl.
        eassign F_; erewrite LOG.rep_hashmap_subset; eauto.
        cancel.
        intuition eauto.
        pred_apply.      
        rewrite indrep_n_helper_pts_piff in * by auto.
        denote lift_empty as Hf; destruct_lift Hf.
        psubst. denote exis as Hf; destruct_lift Hf.
        cancel.
        rewrite indrep_n_helper_pts_piff in * by auto.
        denote lift_empty as Hf; destruct_lift Hf.
        psubst. denote exis as Hf; destruct_lift Hf.
        eassign Fs; pred_apply; cancel.
        auto.
        hoare.
        rewrite indrep_n_helper_0 by auto.
        cancel.
        rewrite <- H1; cancel; eauto.
      + step.
        psubst.
        (* working around same "conversion anomaly" bug as above *)
        prestep. norm. cancel.
        rewrite indrep_n_tree_repeat_Fs with (m := list2nmem m) in *.
        2: erewrite indrep_n_helper_0 in *;
           denote lift_empty as Hf; destruct_lift Hf;
           rewrite repeat_length in *; cleanup; auto.
        2: pred_apply; cancel.
        intuition eauto.
        step.
        erewrite LOG.rep_hashmap_subset; eauto.
        pred_apply. cancel.
        symmetry.
        eapply indrep_n_tree_repeat_Fs with (m := list2nmem m); eauto.
        erewrite indrep_n_helper_0 in *;
        denote lift_empty as Hf; destruct_lift Hf;
        rewrite repeat_length in *; cleanup; auto.
        pred_apply; cancel.
        cancel.
        step.
        rewrite indrep_n_helper_valid by auto. cancel.
        destruct (repeat Public (length (IndRec.Defs.ipack dummy))) eqn:D; eauto.
        apply Forall_nil.
        destruct (length (IndRec.Defs.ipack dummy)); simpl in *;
        inversion D; subst; eauto.
        constructor; auto.
        apply Forall_nil.
        rewrite indrep_n_helper_length_piff in *.
        denote indrep_n_helper as Hi; destruct_lift Hi.
        unfold IndRec.Defs.item in *; simpl in *. rewrite firstn_oob by omega.
        prestep. norm. cancel.
        rewrite Nat.sub_diag; cbn [skipn].
        intuition auto.
        - pred_apply; eassign dummy2. cancel.
        - psubst.
          pred_apply; cancel.
          eassign ((Fs * dummy0)%pred). cancel.
        - assert (length dummy2 = NIndirect) by indrep_n_tree_bound.          
          prestep. norml.
          assert (length prefix < NIndirect).
          rewrite indrep_n_helper_length_piff in *; destruct_lifts.
          autorewrite with lists in *; cbn [length] in *; omega.
          unfold stars; simpl; cancel.
          autorewrite with lists; cbn [length].
          repeat rewrite ?Nat.add_sub, ?Nat.sub_diag, ?skipn_app_r_ge by omega.
          cbn [skipn].
          erewrite skipn_selN_skipn by omega.
          cbn [combine].
          erewrite skipn_selN_skipn with (l := dummy2) by omega.
          rewrite listmatch_cons.
          cancel.
          autorewrite with lists; cbn [length].
          repeat rewrite Nat.add_sub.
          erewrite skipn_selN_skipn with (l := dummy1) by omega.
          rewrite pred_fold_left_cons.
          cancel.
          reflexivity.
          step.
          prestep. norm.
          unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
          Opaque block_mem_subset.
          repeat split.         
          autorewrite with lists; cbn [length].
          rewrite skipn_app_r_ge by omega.
          repeat match goal with |- context [?b + S ?a - ?a] =>
                                 replace (b + S a - a) with (S b) by omega end.
          repeat match goal with |- context [S ?a - ?a] =>
                                 replace (S a - a) with 1 by omega end.
          pred_apply; rewrite indrep_n_tree_0. cancel.
          auto.
          autorewrite with lists; cbn [length].
          pred_apply.
          repeat match goal with |- context [?b + S ?a - ?a] =>
                                 replace (b + S a - a) with (S b) by omega end.
          cancel.
          auto.
          eauto.
          rewrite <- H1; cancel; eauto.
        - rewrite indrep_n_helper_valid in * by auto.
          denote lift_empty as Hl; destruct_lift Hl.
          psubst.
          denote piff as Hp.
          destruct Hp.
          denote piff as Hp.
          rewrite Hp in *.
          prestep. norml.
          repeat rewrite skipn_oob in * by omega.
          rewrite Hp in *.
          unfold stars; simpl; cancel.
          
          prestep. norm.          
          unfold stars; simpl.
          eassign F_; erewrite LOG.rep_hashmap_subset; eauto.
          cancel.
          intuition; eauto.
          pred_apply; cancel.
          rewrite skipn_oob by indrep_n_tree_bound.
          rewrite indrep_n_helper_pts_piff by auto.
          unfold listmatch; cancel.
          pred_apply; cancel.
          auto.
          prestep; norm.
          unfold stars; simpl.
          cancel.
          repeat split.
          pred_apply; cancel.
          apply listmatch_indrep_n_tree_empty.
          autorewrite with lists; auto.
          rewrite pred_fold_left_repeat_emp.
          split; cancel.
          pred_apply; cancel.
          auto.
          auto.
          eauto.
          rewrite <- H1; cancel; eauto.
          cancel.
        - eassign (false_pred(AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset));
          unfold false_pred; cancel.
        - rewrite <- H1; cancel.
          eauto using LOG.intact_hashmap_subset.
    Grab Existential Variables.
    all: try exact addr_eq_dec.
    all : eauto using tt.
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indclear_all _ _ _ _ _ ) _) => apply indclear_all_ok : prog.


  
  Definition indclear_aligned indlvl lxp bxp (indbns : list waddr) start len ms :=
    let N := NIndirect ^ S indlvl in
    let indbns := firstn (len / N) (skipn (start / N) indbns) in
    ForEach bn rest indbns
      Blockmem bm
      Hashmap hm
      Ghost [ F Fm Fs l_part fsl bxp crash m0 sm freelist ]
      Loopvar [ ms ]
      Invariant
        exists l_part' indbns' fsl' freelist' m,
        LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
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
        ms <- indclear_all indlvl lxp bxp # bn ms;;
        Ret ^(ms)
      Rof ^(ms).

  Theorem indclear_aligned_ok :
    forall indlvl lxp bxp indbns start len ms pr,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part fsl freelist,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) # (fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start / N + len / N <= length l_part ]] * [[ Nat.divide N start ]] * [[ Nat.divide N len ]] *
           [[ length fsl = length indbns ]] *
           [[ (Fs * BALLOCC.smrep freelist * pred_fold_left fsl)%pred sm ]]
    POST:bm', hm', RET:^(ms)
           exists m' freelist' indbns' fsl' l_part', 
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ indbns' = upd_range indbns (start / N) (len / N) $0 ]] *
           [[ l_part' = upd_range l_part (start / N) (len / N) (repeat $0 N) ]] *
           [[ incl freelist freelist' ]] *
           [[ length fsl' = length indbns' ]] *
           [[ (Fs * BALLOCC.smrep freelist' * pred_fold_left fsl')%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
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
      - safestep.
        all: assert (length (firstn z (skipn z0 fsl)) = length (firstn z (skipn z0 indbns))) by
          (repeat rewrite ?firstn_length, ?skipn_length; congruence).
        all: assert (length (firstn z (skipn z0 l_part)) = length (firstn z (skipn z0 indbns))) by
          (rewrite firstn_length, skipn_length; indrep_n_tree_bound).
        all: assert (length prefix < length (firstn z (skipn z0 indbns))) by
          (substl (firstn z (skipn z0 indbns)); rewrite app_length; cbn; omega).
        repeat rewrite <- H5 in *.
        autorewrite with lists; cbn [length].
        repeat rewrite Nat.add_sub.
        rewrite skipn_app.
        + erewrite skipn_selN_skipn with (l := firstn _ (skipn _ fsl)) at 1.
          erewrite skipn_selN_skipn with (l := firstn _ (skipn _ l_part)) at 1.
          cbn [combine].
          rewrite listmatch_cons.
          cancel.
          all: omega.
        + repeat rewrite <- H5 in *.
          autorewrite with lists; cbn [length].
          rewrite Nat.add_sub.
          erewrite skipn_selN_skipn with (off := length prefix).
          rewrite pred_fold_left_cons.
          cancel. reflexivity.
          omega.
        + step.
          prestep; norm.
          unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
          repeat split.
          repeat rewrite <- H5.
          autorewrite with lists. cbn [length].
          repeat match goal with |- context [?b + S ?a - ?a] => replace (b + S a - a) with (b + 1) by omega end.
          rewrite skipn_app_r_ge by omega.
          rewrite minus_plus.
          rewrite <- plus_n_Sm, <- plus_n_O.
          pred_apply; rewrite indrep_n_tree_0.
          cancel.
          pred_apply;  repeat rewrite <- H5.
          autorewrite with lists. cbn [length].
          repeat match goal with |- context [?b + S ?a - ?a] => replace (b + S a - a) with (b + 1) by omega end.
          rewrite <- plus_n_Sm, <- plus_n_O.
          cancel.
          auto.
          auto.
          eauto.
        + rewrite <- H1; cancel; eauto.
      - step.
        repeat rewrite upd_range_eq_upd_range' by indrep_n_tree_bound.
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
        rewrite firstn_length_l, skipn_length by indrep_n_tree_bound.
        indrep_n_tree_bound.
        repeat rewrite pred_fold_left_app.
        cancel.
        rewrite skipn_skipn.
        rewrite skipn_oob by indrep_n_tree_bound.
        rewrite pred_fold_left_repeat_emp.
        cancel.
      - eassign (false_pred(AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset));
        unfold false_pred; cancel.
   Grab Existential Variables.
   all : eauto; try exact tt.
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indclear_aligned _ _ _ _ _ _ _ ) _) => apply indclear_aligned_ok : prog.
  

  Definition update_block lxp bxp bn contents new ms :=
    If (list_eq_dec waddr_eq_dec new (repeat $0 NIndirect)) {
      ms <- BALLOCC.free lxp bxp bn ms;;
      Ret ^(ms, 0)
    } else {
      If (list_eq_dec waddr_eq_dec contents new) {
        Ret ^(ms, bn)
      } else {
          lms <- IndRec.write lxp bn (repeat Public (length (IndRec.Defs.ipack new)))
                              new (BALLOCC.MSLog ms);;
        Ret ^(BALLOCC.upd_memstate lms ms, bn)
      }
    }.
                                                                         
Lemma indrep_n_helper_valid_sm: forall Fs bxp ir l,
  ir <> 0 ->
  indrep_n_helper Fs bxp ir l =p=> indrep_n_helper Fs bxp ir l * (exists b, [[ Fs <=p=> ir |->b ]]).
Proof.
  unfold indrep_n_helper.
  intros.
  destruct addr_eq_dec; try congruence.
  cancel; eauto.
Qed.

Theorem update_block_ok :
  forall lxp bxp ir indbns indbns' ms pr,
    {< F Fm Fs IFs m0 sm m freelist,
    PERM:pr
    PRE:bm, hm,
       LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
       [[ BALLOCC.bn_valid bxp ir ]] *
       [[ IndRec.items_valid ir indbns' ]] *
       [[[ m ::: (Fm * indrep_n_helper IFs bxp ir indbns) *
              BALLOCC.rep bxp freelist ms ]]] *
            [[ (Fs * BALLOCC.smrep freelist * IFs)%pred sm ]]
    POST:bm', hm', RET: ^(ms, ir')
           exists m' freelist' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * indrep_n_helper IFs' bxp ir' indbns' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * BALLOCC.smrep freelist' * IFs')%pred sm ]] *
           [[ incl freelist freelist' ]] *
           ([[ ir' = 0 ]] \/ [[ ir' = ir ]])
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
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
      safestep.
      erewrite LOG.rep_hashmap_subset; eauto; cancel.
      or_l; cancel.
      subst.
      pred_apply; rewrite indrep_n_helper_0 by auto.
      cancel; eauto.
      simpl; cancel.
      auto.
    + step.
      prestep. norm. repeat cancel.
      erewrite LOG.rep_hashmap_subset; eauto; cancel.
      or_r; cancel.
      intuition idtac.
      pred_apply. cancel.
      pred_apply; cancel.
      rewrite Hf; cancel.
      auto.
      eauto.
    + step.
      rewrite indrep_n_helper_valid by auto; cancel.
      apply repeat_length.
      step.
      prestep. norm. repeat cancel.
      erewrite LOG.rep_hashmap_subset; eauto; cancel.
      or_r; cancel.
      intuition idtac.
      rewrite indrep_n_helper_valid by auto.
      pred_apply; cancel; eauto.
      rewrite Hf; pred_apply; cancel.
      auto.
      auto.
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (update_block _ _ _ _ _ _) _) => apply update_block_ok : prog.


  
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
        let^ (lms, indbns) <- IndRec.read lxp ragged_bn 1 (BALLOCC.MSLog ms);;
        let ms := BALLOCC.upd_memstate lms ms in
        match indlvl with
        | 0 => 
          let indbns' := upd_range indbns 0 len $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns' ms;;
          Ret ^(ms, updN iblocks (start / N) $ v)
        | S indlvl' =>
          let N' := NIndirect ^ (S indlvl') in
          let^ (ms) <- indclear_aligned indlvl' lxp bxp indbns 0 (len / N' * N') ms;;
          let indbns' := upd_range indbns 0 (len / N') $0 in
          let^ (ms, indbns'') <- indclear_from_aligned indlvl' lxp bxp indbns' (len / N' * N') (len mod N') ms;;
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns'' ms;;
          Ret ^(ms, updN iblocks (start / N) $ v)
        end
      }
 }.
                                                                         
Lemma concat_repeat: forall T n k (x : T),
  concat (repeat (repeat x k) n) = repeat x (n * k).
Proof.
  intros.
  erewrite concat_hom_repeat.
  autorewrite with lists.
  eauto.
  apply Forall_repeat; auto.
Qed.


Theorem indclear_from_aligned_ok :
  forall indlvl lxp bxp indbns start len ms pr,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part freelist fsl,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start + len <= length (concat l_part) ]] * [[ Nat.divide N start ]] * [[ len < N ]] *
           [[ length fsl = length indbns ]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, indbns')
           exists m' freelist' l_part' fsl',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ length indbns' = length indbns ]] *
           [[ length fsl' = length indbns' ]] *
           [[ incl freelist freelist' ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indclear_from_aligned indlvl lxp bxp indbns start len ms.
  Proof. 
    induction indlvl.
    + simpl. step.
      step; step.
      erewrite LOG.rep_hashmap_subset; eauto.
      pose proof listmatch_indrep_n_tree_forall_length 0 as H'.
      simpl in H'. rewrite H' in *.
      denote combine as Hc. destruct_lift Hc. rewrite mult_1_r in *.
      prestep. norml.
      assert (start / NIndirect < length l_part) by indrep_n_tree_bound.
      assert (start / NIndirect < length indbns) by indrep_n_tree_bound.
      cancel.
    - step; step.
       erewrite LOG.rep_hashmap_subset; eauto.
        rewrite listmatch_extract in *.
        erewrite selN_combine in * by auto.
        cbn [fst snd] in *.
        denote (# _ = _) as Ha. rewrite Ha in *.
        rewrite indrep_n_helper_0 in *.
        destruct_lifts.
        erewrite upd_range_concat_hom_start_aligned by (eauto; omega).
        denote (selN _ _ _ = repeat _ _) as Hb. rewrite Hb.
        rewrite upd_range_same by omega.
        erewrite selN_eq_updN_eq; eauto.
        indrep_n_tree_bound.
      - step.
        indrep_n_extract.
        rewrite indrep_n_helper_valid by eauto. cancel.
        indrep_n_tree_bound.
        destruct (repeat Public (length (IndRec.Defs.ipack l_part ⟦ start / NIndirect ⟧))) eqn:D; eauto.
        apply Forall_nil.
        destruct (length (IndRec.Defs.ipack l_part ⟦ start / NIndirect ⟧)); simpl in *;
        inversion D; subst; eauto.
        constructor; auto.
        apply Forall_nil.
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
          cancel. eassign (Fs * pred_fold_left (removeN fsl (start / NIndirect)))%pred; cancel.
        * step; safestep.
          erewrite LOG.rep_hashmap_subset; eauto; cancel.
        **  pred_apply; rewrite combine_updN, listmatch_updN_removeN.
            cancel. all: indrep_n_tree_bound.
        **  erewrite upd_range_concat_hom_start_aligned; eauto. omega.
        **  indrep_n_tree_bound.
        **  autorewrite with lists; omega.
        **  auto.
        **  rewrite pred_fold_left_selN_removeN with (l := updN _ _ _).
            rewrite selN_updN_eq, removeN_updN by omega. cancel.
        ** erewrite LOG.rep_hashmap_subset; eauto.
        **  subst; pred_apply. rewrite natToWord_wordToNat. rewrite combine_updN.
            rewrite listmatch_updN_removeN by (eauto; indrep_n_tree_bound).
            eassign (upd_range (selN l_part (start / NIndirect) nil) 0 len $ (0)); simpl.
            cancel.
        **  erewrite upd_range_concat_hom_start_aligned by (eauto; omega). auto.
        **  indrep_n_tree_bound.
        **  autorewrite with lists; omega.
        **  auto.
        **  rewrite pred_fold_left_selN_removeN with (l := updN _ _ _).
             rewrite selN_updN_eq, removeN_updN by omega. cancel.
        * rewrite <- H1; cancel; eauto.
        * match goal with |- context [selN ?l ?ind ?d] =>
            rewrite listmatch_extract with (b := l) (i := ind) (bd := d) in *
          end. rewrite indrep_n_helper_length_piff in *.
          destruct_lifts.
          denote (length (selN _ _ _) = _) as Ha. setoid_rewrite Ha.
          omega.
          indrep_n_tree_bound.
        * rewrite <- H1; cancel; eauto.
    + cbn [indclear_from_aligned].
      prestep. norml.
      pose proof listmatch_indrep_n_tree_forall_length (S indlvl) as H'.
      simpl in H'. rewrite H' in *.
      denote (combine indbns fsl) as Hc; destruct_lift Hc.
      cancel.
      step.
      step.
      erewrite LOG.rep_hashmap_subset; eauto.
      
      prestep. norml.
      assert (start / (NIndirect ^ S (S indlvl)) < length l_part) by indrep_n_tree_bound.
      assert (start / (NIndirect ^ S (S indlvl)) < length indbns) by indrep_n_tree_bound.
      cancel.
      step.
      step.
      erewrite LOG.rep_hashmap_subset; eauto.
      {
        rewrite listmatch_extract in *.
        erewrite selN_combine in * by auto. cbn [fst snd] in *.
        denote (# _ = _) as Ha. rewrite Ha in *.
        destruct_lifts.
        rewrite indrep_n_helper_0 in *.
        destruct_lift H.
        rewrite listmatch_indrep_n_tree_empty'' in *.
        destruct_lifts.
        erewrite upd_range_concat_hom_start_aligned by (eauto; omega).
        denote (selN _ _ _ = _) as Hs. rewrite Hs.
        denote (Forall _ _) as Hf.
        rewrite concat_repeat in *.
        rewrite upd_range_same by omega.
        erewrite selN_eq_updN_eq; eauto.
        rewrite repeat_length in *; auto.
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
      destruct (repeat Public (length (IndRec.Defs.ipack dummy))) eqn:D; eauto.
      apply Forall_nil.
      destruct (length (IndRec.Defs.ipack dummy)); simpl in *;
      inversion D; subst; eauto.
      constructor; auto.
      apply Forall_nil.
      rewrite firstn_oob.
      match goal with [H : context [listmatch _ (combine ?l _)] |- context [?c = ?l] ] =>
        rewrite listmatch_length_pimpl with (a := combine l _) in H;
        rewrite indrep_n_helper_length_piff in H; destruct_lift H end.
      rewrite combine_length_eq in * by omega.
      prestep. norm.
      eassign F_; cancel.
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
      rewrite upd_range_length in *; autorewrite with lists; try omega.
      cancel.
      prestep. norm. cancel.
      rewrite selN_combine with (a := indbns) in * by eauto.
      cbn [fst snd] in *.
      intuition auto.
      unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen.
      rewrite mult_1_l. intuition.
      rewrite upd_range_length in *.
      indrep_n_tree_bound.
      pred_apply; cancel.
      pred_apply; cancel.
      - step; clear IHindlvl.
        safestep.
        erewrite LOG.rep_hashmap_subset; eauto.
        6: match goal with |- context [removeN _ ?i] =>
          erewrite pred_fold_left_selN_removeN with (l := updN fsl i (pred_fold_left fsl'0));
          rewrite selN_updN_eq, removeN_updN by omega
        end.
        * pred_apply; rewrite indrep_n_helper_0. cancel.
          rewrite combine_updN, listmatch_updN_removeN.
          norm. cancel. eassign IFs'. rewrite indrep_n_helper_0. cancel.
          intuition eauto.
          denote (IFs' <=p=> emp) as Hf. rewrite Hf. split; cancel.
          all: rewrite ?combine_length_eq; omega.
        * erewrite upd_range_concat_hom_start_aligned by (eauto; omega).
          repeat f_equal.
          denote (concat _ = _) as Hc. rewrite Hc.
          denote (selN _ _ _ = _) as Hs. rewrite Hs.
          rewrite concat_hom_upd_range by eauto. cbn -[Nat.div Nat.modulo].
          autorewrite with lists. simpl.
          rewrite mult_comm, <- Nat.div_mod; auto.
        * autorewrite with lists; auto.
        * autorewrite with lists; omega.
        * auto.
        * denote (indrep_n_helper _ _ 0) as Hi. rewrite indrep_n_helper_0 in Hi.
          destruct_lift Hi. denote (IFs' <=p=> emp) as Hf. rewrite Hf. cancel.
        * safestep.
          erewrite LOG.rep_hashmap_subset; eauto.
        ** pred_apply; rewrite natToWord_wordToNat. rewrite combine_updN.
          rewrite listmatch_updN_removeN. cancel. reflexivity.
          indrep_n_tree_bound.
          reflexivity.
          all: rewrite ?combine_length_eq; omega.
        ** denote (concat _ = _) as Hc. rewrite Hc.
          symmetry. erewrite upd_range_concat_hom_start_aligned by (eauto; mult_nonzero; omega).
          rewrite concat_hom_upd_range; eauto.
          rewrite upd_range_upd_range; eauto.
          repeat f_equal; eauto.
          rewrite mult_comm with (n := len / _), <- Nat.div_mod; auto.
        ** autorewrite with lists; auto.
        ** autorewrite with lists; auto.
        ** auto.
        ** rewrite pred_fold_left_selN_removeN with (l := updN _ _ _).
          rewrite selN_updN_eq, removeN_updN by omega. cancel.
      - rewrite <- H1; cancel; eauto.
      - rewrite <- H1; cancel; eauto.
      - rewrite <- H1; cancel; eauto.
      - indrep_n_tree_bound.
      - rewrite <- H1; cancel; eauto.
    Grab Existential Variables.
    all : intros; eauto.
    all : try solve [exact unit | exact nil | exact $ 0 | exact 0 | exact True | exact ($0, emp) ].
  Qed.

    
  Hint Extern 1 ({{_|_}} Bind (indclear_from_aligned _ _ _ _ _ _ _) _) => apply indclear_from_aligned_ok : prog.


  
  
  Fixpoint indclear_to_aligned indlvl lxp bxp iblocks start ms :=
    let N := (NIndirect ^ S indlvl) in
    If (addr_eq_dec (start mod N) 0) {
      Ret ^(ms, iblocks)
    } else {
      let ragged_bn := #(selN iblocks (start / N) $0) in
      If (addr_eq_dec ragged_bn 0) {
        Ret ^(ms, iblocks)
      } else {
        let^ (lms, indbns) <- IndRec.read lxp ragged_bn 1 (BALLOCC.MSLog ms);;
        let ms := BALLOCC.upd_memstate lms ms in
        match indlvl with
        | 0 =>
          let indbns' := upd_range indbns (start mod NIndirect) (NIndirect - (start mod NIndirect)) $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns' ms;;
          Ret ^(ms, updN iblocks (start / N) $ v)
        | S indlvl' =>
          let N' := NIndirect ^ S indlvl' in
          let start' := start mod N in
          let^ (ms, indbns') <- indclear_to_aligned indlvl' lxp bxp indbns start' ms;;
          let^ (ms) <- indclear_aligned indlvl' lxp bxp indbns' (roundup start' N') (N - (roundup start' N')) ms;;
          let indbns'' := upd_range indbns' (divup start' N') (NIndirect - (divup start' N')) $0 in
          let^ (ms, v) <- update_block lxp bxp ragged_bn indbns indbns'' ms;;
          Ret ^(ms, updN iblocks (start / N) $ v)
        end
      }
    }.

  Theorem indclear_to_aligned_ok :
    forall indlvl lxp bxp indbns start ms pr,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m fsl l_part freelist,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]] *
           [[ start <= length (concat l_part) ]] *
           [[ length fsl = length indbns ]]
    POST:bm', hm', RET:^(ms, indbns')
           exists m' freelist' fsl' l_part',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start (roundup start N - start) $0 ]] *
           [[ incl freelist freelist' ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ length fsl' = length indbns' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indclear_to_aligned indlvl lxp bxp indbns start ms.
  Proof. 
    induction indlvl.
    intros.
    + simpl in *. subst N. rewrite mult_1_r in *.
      step. hoare.
      erewrite LOG.rep_hashmap_subset; eauto.
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
      step.  
      prestep. norm.
      unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
      intuition auto.
      Focus 2. {
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
      } Unfocus.
      {
        pred_apply; cancel.
        erewrite <- updN_selN_eq with (l := combine _ _) at 2.
        rewrite listmatch_updN_removeN.
        indrep_n_extract.
        repeat rewrite selN_combine by auto. cbn [fst snd].
        denote (# _ = _) as Hn. repeat rewrite Hn. rewrite indrep_n_helper_0 in *.
        cancel. rewrite indrep_n_helper_0.
        (* same bug *)
        do 2 intro; apply sep_star_lift_apply'; cbv [lift_empty]; intuition auto.
        denote (_ = repeat _ _) as Hl. rewrite Hl.
        apply upd_range_same.
        eauto.
        all: omega.
      }
      auto.
      omega.
      step.
      indrep_n_extract. rewrite indrep_n_helper_valid by eauto. cancel.
      destruct (repeat Public (length (IndRec.Defs.ipack l_part ⟦ start / NIndirect ⟧))) eqn:D; eauto.
      apply Forall_nil.
      destruct (length (IndRec.Defs.ipack l_part ⟦ start / NIndirect ⟧)); simpl in *;
      inversion D; subst; eauto.
      constructor; auto.
      apply Forall_nil.
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
      - step.
        safestep.
        erewrite LOG.rep_hashmap_subset; eauto.
        * pred_apply. erewrite combine_updN. rewrite listmatch_updN_removeN. cancel. all: omega.
        * rewrite roundup_eq by auto. rewrite minus_plus.
          erewrite upd_range_concat_hom_small; eauto.
          all : autorewrite with core; eauto.
          rewrite <- roundup_eq by auto.
          erewrite concat_hom_length in *; eauto.
        * auto.
        * rewrite pred_fold_left_updN_removeN by (rewrite combine_length_eq in *; omega).
          cancel.
        * autorewrite with lists; auto.
        * safestep.
          erewrite LOG.rep_hashmap_subset; eauto.
        ** pred_apply; rewrite natToWord_wordToNat. rewrite combine_updN.
           rewrite listmatch_updN_removeN.
           eassign  (upd_range (selN l_part (start / NIndirect) nil) (start mod NIndirect)
          (NIndirect - start mod NIndirect) $ (0)). cancel.
          all: rewrite ?combine_length_eq; try omega; indrep_n_tree_bound.
          rewrite mult_comm; eauto using div_lt_mul_lt.
        ** rewrite roundup_eq by auto. rewrite minus_plus.
          erewrite upd_range_concat_hom_small; eauto.
          rewrite <- roundup_eq by auto.
          erewrite concat_hom_length in * by eauto. auto.
          rewrite le_plus_minus_r; auto.
        ** auto.
        ** rewrite pred_fold_left_updN_removeN by (rewrite combine_length_eq in *; omega).
          cancel.
        ** autorewrite with lists; auto.
      - rewrite <- H1; cancel; eauto.
      - match goal with [|- context [selN ?L ?N ?d] ] =>
          rewrite listmatch_extract with (b := L) (i := N) (bd := d) in * by omega
        end. rewrite indrep_n_helper_length_piff in *.
        destruct_lifts. autorewrite with core. apply Nat.eq_le_incl. assumption.
      - rewrite <- H1; cancel; eauto.
    + cbn [indclear_to_aligned].
      prestep. norml.
      pose proof listmatch_indrep_n_tree_forall_length (S indlvl) as H'.
      simpl in H'. match goal with H: _ |- _ => rewrite H' in H; destruct_lift H end.
      cancel. hoare.
      erewrite LOG.rep_hashmap_subset; eauto.
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
      cancel. step. prestep. norm. cancel.
      erewrite LOG.rep_hashmap_subset; eauto.  
      instantiate (1 := updN _ _ _). intuition auto.
      {
        erewrite <- updN_selN_eq with (l := indbns) at 1.
        rewrite combine_updN. rewrite listmatch_updN_removeN.
        denote (# _ = 0) as Hn. cbn [fst snd].
        pred_apply. rewrite listmatch_extract. rewrite selN_combine.
        cbn [fst snd]. repeat rewrite Hn. cancel. reflexivity.
        eassign (selN fsl (start / (NIndirect * (NIndirect * NIndirect ^ indlvl))) emp); eauto.
        eassign (selN l_part (start / (NIndirect * (NIndirect * NIndirect ^ indlvl))) nil); eauto.
        all: try eauto; try omega.
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
        all: try rewrite repeat_length in *; try omega; mult_nonzero.
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
       destruct (repeat Public (length (IndRec.Defs.ipack dummy))) eqn:D; eauto.
      apply Forall_nil.
      destruct (length (IndRec.Defs.ipack dummy)); simpl in *;
      inversion D; subst; eauto.
      constructor; auto.
      apply Forall_nil.
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
      step. safestep; clear IHindlvl.
      erewrite LOG.rep_hashmap_subset; eauto.
      - pred_apply; rewrite indrep_n_helper_0. cancel.
        rewrite combine_updN, listmatch_updN_removeN.
        norm. cancel. rewrite indrep_n_helper_0'. cancel.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r.
        repeat rewrite Nat.div_mul by auto.
        denote (upd_range _ _ _) as Hu. rewrite Hu.
        cancel. reflexivity.
        intuition eauto.
        all : try rewrite repeat_length in *; try rewrite upd_range_length in *; try omega.
        cleanup.
        erewrite <- upd_range_length.
        rewrite H37.
        apply repeat_length.
      - rewrite roundup_eq with (a := start) by mult_nonzero.
        rewrite minus_plus.
        eapply indclear_upd_range_helper_1; eauto.
        erewrite concat_hom_length by eauto.
        rewrite combine_length_eq2 in * by omega. congruence.
      - auto.
      - rewrite pred_fold_left_updN_removeN.
        rewrite indrep_n_helper_0 with (Fs := IFs') in *.
        denote (IFs' <=p=> emp) as Hf; destruct_lift Hf.
        psubst. cancel.
        rewrite combine_length_eq in * by omega. omega.
      - autorewrite with lists; auto.
      - safestep.
        erewrite LOG.rep_hashmap_subset; eauto.
      * pred_apply; rewrite natToWord_wordToNat.
        unfold roundup. rewrite <- Nat.mul_sub_distr_r. repeat rewrite Nat.div_mul by auto.
        rewrite combine_updN.
        rewrite listmatch_updN_removeN. cancel; eauto.        
        all : try rewrite upd_range_length in *; omega.
      * erewrite indclear_upd_range_helper_1; eauto.
        f_equal. rewrite roundup_eq by auto. omega.
        erewrite concat_hom_length by eauto.
        rewrite combine_length_eq in * by omega. congruence.
      * auto.
      * rewrite pred_fold_left_updN_removeN. cancel.
        rewrite combine_length_eq in * by omega. omega.
      * autorewrite with lists; auto.
      - rewrite <- H1; cancel; eauto.
      - rewrite <- H1; cancel; eauto.
      - rewrite <- H1; cancel; eauto.
      - rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *. simpl in *. omega.
      - rewrite <- H1; cancel; eauto.
    Unshelve.
    all : intros; try solve [exact unit | exact nil | exact $0 | exact emp | exact ($0, emp) | constructor]; eauto.
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indclear_to_aligned _ _ _ _ _ _) _) => apply indclear_to_aligned_ok : prog.




  Definition indclear_multiple_blocks indlvl lxp bxp indbns start len ms :=
    let N := NIndirect ^ S indlvl in
    let^ (ms, indbns') <- indclear_to_aligned indlvl lxp bxp indbns start ms;;
    let len' := len - (roundup start N - start) in
    let start' := start + (roundup start N - start) in
    let^ (ms) <- indclear_aligned indlvl lxp bxp indbns' start' (len' / N * N) ms;;
    let indbns'' := upd_range indbns' (start' / N) (len' / N) $0 in
    let start'' := start' + (len' / N * N) in
    let len'' := len' mod N in
    indclear_from_aligned indlvl lxp bxp indbns'' start'' len'' ms.

  Theorem indclear_multiple_blocks_ok :
    forall indlvl lxp bxp indbns start len ms pr,
    let N := NIndirect ^ S indlvl in
    {< F Fm Fs m0 sm m l_part freelist fsl,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns fsl) l_part
                         * BALLOCC.rep bxp freelist ms) ]]] *
           [[ start <= length (concat l_part) ]] * [[ (N - start mod N) < len ]] *
           [[ start + len <= length (concat l_part) ]] *
           [[ (Fs * pred_fold_left fsl * BALLOCC.smrep freelist)%pred sm ]] *
           [[ length indbns = length fsl ]]
    POST:bm', hm', RET:^(ms, indbns')
           exists m' freelist' l_part' fsl',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * listmatch (fun x l => indrep_n_tree indlvl bxp (snd x) #(fst x) l) (combine indbns' fsl') l_part'
                          * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ concat (l_part') = upd_range (concat l_part) start len $0 ]] *
           [[ (Fs * pred_fold_left fsl' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ length indbns' = length fsl' ]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
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
    + rewrite <- H1; cancel; eauto.
    + rewrite <- H1; cancel; eauto.   
    Unshelve.
      all : try solve [exact unit | exact nil]; eauto.
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indclear_multiple_blocks _ _ _ _ _ _ _) _) => apply indclear_multiple_blocks_ok : prog.

  Fixpoint indclear indlvl lxp bxp (root : addr) start len ms :=
    let N := NIndirect ^ indlvl in
    If (addr_eq_dec root 0) {
      Ret ^(ms, 0)
    } else {
      If (addr_eq_dec len 0) {
        Ret ^(ms, root)
      } else {
        let^ (lms, indbns) <- IndRec.read lxp root 1 (BALLOCC.MSLog ms);;
        let ms := BALLOCC.upd_memstate lms ms in
        let^ (ms, indbns') <- match indlvl with
        | 0 =>
           Ret ^(ms, upd_range indbns start len $0)
        | S indlvl' =>
          If (le_lt_dec len (N - start mod N)) {
            let^ (ms, v) <- indclear indlvl' lxp bxp #(selN indbns (start / N) $0) (start mod N) len ms;;
            Ret ^(ms, updN indbns (start / N) $ v)
          } else {
            indclear_multiple_blocks indlvl' lxp bxp indbns start len ms
          }
        end;;
        update_block lxp bxp root indbns indbns' ms
      }
    }.

 Theorem indclear_ok :
    forall indlvl lxp bxp ir start len ms pr,
    {< F Fm Fs m0 sm m l freelist IFs,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs ir l *
            BALLOCC.rep bxp freelist ms) ]]] *
           [[ start + len <= length l ]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, ir')
           exists m' freelist' l' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' ir' l' *
              BALLOCC.rep bxp freelist' ms) ]]] *
           [[ incl freelist freelist' ]] * [[ l' = upd_range l start len $0 ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           ([[ ir = ir' ]] \/ [[ ir' = 0 ]])
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indclear indlvl lxp bxp ir start len ms.
    Proof. 
      induction indlvl.
      + cbn -[Nat.div].
        prestep. norml.
        denote indrep_n_helper as Hi.
        rewrite indrep_n_helper_length_piff in Hi; destruct_lift Hi.
        step.
        step.
        erewrite LOG.rep_hashmap_subset; eauto; cancel.
        or_l; cancel.
        rewrite indrep_n_helper_0 in *. destruct_lifts.
        autorewrite with lists; auto.
        - hoare.
          erewrite LOG.rep_hashmap_subset; eauto; cancel.
          or_l; cancel.
        - step.
          rewrite indrep_n_helper_valid by auto; cancel.
          destruct (repeat Public (length (IndRec.Defs.ipack l))) eqn:D; eauto.
          apply Forall_nil.
          destruct (length (IndRec.Defs.ipack l)); simpl in *;
          inversion D; subst; eauto.
          constructor; auto.
          apply Forall_nil.
          rewrite firstn_oob by indrep_n_tree_bound.
          step.
          prestep; norm.
          unfold stars; simpl; eassign F_;
          erewrite LOG.rep_hashmap_subset; eauto; cancel.
          intuition eauto.
          pred_apply; cancel.
          prestep; norm.
          unfold stars; simpl; cancel.
          or_r; cancel.
          intuition eauto.
          pred_apply; cancel.
          unfold stars; simpl; cancel.
          or_l; cancel.
          intuition eauto.
          pred_apply; cancel.
          rewrite <- H1; cancel; eauto.
          rewrite <- H1; cancel; eauto.
      + cbn [indclear].
        step. step. step.
        erewrite LOG.rep_hashmap_subset; eauto; cancel.
        or_l; cancel.
        {
          pred_apply.
          denote indrep_n_helper as Hi.
          rewrite indrep_n_helper_0 in Hi. destruct_lift Hi.
          rewrite listmatch_indrep_n_tree_empty'' in H0.
          destruct_lift H0.
          erewrite concat_hom_repeat by eauto using Forall_repeat.
          autorewrite with lists. cancel.
          rewrite concat_repeat; auto.
          rewrite repeat_length in *; auto.
        }
        step.
        step.
        step.
        erewrite LOG.rep_hashmap_subset; eauto; cancel.
        or_l; cancel.
        pred_apply; cancel.

        step.
        { rewrite indrep_n_helper_valid by auto. cancel. }
        destruct (repeat Public (length (IndRec.Defs.ipack dummy))) eqn:D; eauto.
        apply Forall_nil.
        destruct (length (IndRec.Defs.ipack dummy)); simpl in *;
        inversion D; subst; eauto.
        constructor; auto.
        apply Forall_nil.
        rewrite indrep_n_helper_length_piff in *. destruct_lifts.
        unfold IndRec.Defs.item in *; simpl in *.
        rewrite firstn_oob by indrep_n_tree_bound.
        step.
        - safestep.
          indrep_n_extract; solve [cancel | indrep_n_tree_bound].
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
          * prestep. norm.
            unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
            intuition eauto.
            pred_apply; cancel.
            pred_apply; cancel.
            prestep; norm.
            cancel.
            or_r; cancel.
            assert (dummy = repeat $0 NIndirect).
            rewrite indrep_n_helper_0 in H9. destruct_lift H9. auto.
            subst.
            rewrite repeat_selN' in *.
            {
              Opaque block_mem_subset.
              repeat split. pred_apply. cancel.
              erewrite listmatch_isolate with (a := combine _ _).
              erewrite combine_updN_r with (x := IFs').
              rewrite removeN_updN, selN_updN_eq.
              cbn [fst snd].
              rewrite repeat_selN'. rewrite removeN_updN, selN_updN_eq.
              cancel.
              all: autorewrite with lists; auto.
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
              rewrite repeat_length in *; substl (length dummy1).
              indrep_n_tree_bound.
              eauto.
            }
            repeat cancel.
            repeat split.
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
            auto.
            eauto.
            rewrite <- H1; cancel; eauto.
          * cancel.
          * prestep. norm.
            unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
            intuition auto.
            pred_apply. norm; intuition.
            unfold stars; simpl.
            eassign (Fm *
                     listmatch
                       (fun (ibn'_fs : waddr * pred) (l' : list waddr) =>
                          indrep_n_tree indlvl bxp (snd ibn'_fs) # (fst ibn'_fs) l')
                       (removeN (combine dummy dummy1) (start / (NIndirect * NIndirect ^ indlvl)))
                       (removeN dummy2 (start / (NIndirect * NIndirect ^ indlvl))) *
                    indrep_n_tree indlvl bxp IFs' 0
                     (upd_range (selN dummy2 (start / (NIndirect * NIndirect ^ indlvl) ) nil )
                      (start mod (NIndirect * NIndirect ^ indlvl)) len $ (0)))%pred. cancel.
            pred_apply; cancel.
            prestep; norm.
            eassign m'0; unfold stars; simpl.
            rewrite sep_star_or_distr.
            or_r; cancel.
            repeat split.
            pred_apply; cancel.
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
            auto.
            eauto.
            unfold stars; simpl; rewrite sep_star_or_distr.
            or_l; cancel.
            repeat split.
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
            auto.
            eauto.
            rewrite <- H1; cancel; eauto.
          * cancel.
          * rewrite <- H1; cancel; eauto.
      - prestep; norm.
        unfold stars; simpl; eassign F_; cancel.
        intuition eauto.
        omega.
        psubst. pred_apply; cancel.
        prestep; norm.
        unfold stars; simpl; eassign F_; cancel.
        unfold IndRec.items_valid, IndSig.xparams_ok, IndSig.RAStart, IndSig.RALen, Rec.well_formed.
        simpl. intuition eauto.
        indrep_n_tree_bound.
        match goal with [H : concat _ = _|- _] => apply f_equal with (f := @length _) in H end.
        autorewrite with lists in *.
        indrep_n_tree_bound.
        rewrite Nat.mul_cancel_r in *; auto.
        pred_apply; cancel.
        pred_apply; cancel.
        prestep; norm.
        unfold stars; simpl;
        rewrite sep_star_or_distr; or_r; cancel.
        repeat split.
        pred_apply; cancel.
        all: eauto.
        pred_apply; cancel.
        unfold stars; simpl;
        rewrite sep_star_or_distr; or_l; cancel.
        repeat split.
        pred_apply; cancel.
        all: eauto.
        pred_apply; cancel.
        rewrite <- H1; cancel; eauto.
        rewrite <- H1; cancel; eauto.
      - rewrite <- H1; cancel; eauto.
    Grab Existential Variables.
    all : eauto.
    all: try constructor; solve [exact $0 | exact emp].
  Qed.

  Local Hint Extern 1 ({{_|_}} Bind (indclear _ _ _ _ _ _ _ ) _) => apply indclear_ok : prog.
  Opaque indclear.

  Definition indput_get_blocks {P} {Q} lxp (is_alloc : {P} + {Q}) ir ms :=
    If (is_alloc) {
      Ret ^(ms, repeat $0 NIndirect)
    } else {
      IndRec.read lxp ir 1 ms
    }.

 Theorem indput_get_blocks_ok :
    forall P Q lxp (is_alloc : {P} + {Q}) ir ms pr,
    {< F Fm m0 sm m bxp indbns Fs,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[ BALLOCC.bn_valid bxp ir ]] *
           [[ P -> ir = 0 ]] * [[ Q -> ir <> 0 ]] *
           [[[ m ::: (Fm * indrep_n_helper Fs bxp ir indbns) ]]]
    POST:bm', hm', RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[ r = indbns ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indput_get_blocks lxp is_alloc ir ms.
    Proof. 
      unfold indput_get_blocks. unfold indrep_n_helper. intros.
      step.
      step.
      step.
      erewrite LOG.rep_hashmap_subset; eauto.
      destruct_lifts. auto.
      step.
      step.
      step.
      destruct addr_eq_dec; try omega. cancel.
      destruct (repeat Public (length (IndRec.Defs.ipack indbns))) eqn:D; eauto.
      apply Forall_nil.
      destruct (length (IndRec.Defs.ipack indbns)); simpl in *;
      inversion D; subst; eauto.
      constructor; auto.
      apply Forall_nil.
      step.
      apply firstn_oob.
      unfold IndRec.rep, IndRec.items_valid, IndSig.RALen in *.
      destruct addr_eq_dec; destruct_lifts; autorewrite with lists; omega.
      rewrite <- H1; cancel; eauto.
    Qed.

  Local Hint Extern 0 ({{_|_}} Bind (indput_get_blocks _ _ _ _) _) => apply indput_get_blocks_ok : prog.

  (* This is a wrapper for IndRec.write that will use an alternate spec *)
  Definition indrec_write_blind lxp xp items ms :=
    IndRec.write lxp xp (repeat Public (length (IndRec.Defs.ipack items))) items ms.

  (* This is an alternate spec for IndRec.write that does not require IndRec.rep
    to hold beforehand. This allows blind writes to blocks that have not been
    initialized beforehand with IndRec.init *)
  Theorem indrec_write_blind_ok :
    forall lxp xp items ms pr,
    {< F Fm m0 sm m old,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ IndRec.items_valid xp items ]] * [[ xp <> 0 ]] *
          [[[ m ::: Fm * arrayN (@ptsto _ addr_eq_dec _) xp [old] ]]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: Fm * IndRec.rep xp (repeat Public (length (IndRec.Defs.ipack items))) items ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} indrec_write_blind lxp xp items ms.
  Proof. 
    unfold indrec_write_blind, IndRec.write, IndRec.rep, IndRec.items_valid.
    step.
    apply repeat_length.
    apply repeat_spec in H; subst; auto.
    safestep.
    erewrite LOG.rep_hashmap_subset; eauto.
    erewrite LOG.rep_blockmem_subset; eauto.
    unfold IndSig.RAStart. instantiate (1 := [_]). pred_apply; cancel.
    erewrite <- extract_blocks_length.
    rewrite H16.
    setoid_rewrite combine_length_eq.
    rewrite repeat_length.
    rewrite IndRec.Defs.ipack_one. auto.
    unfold IndRec.Defs.item in *. simpl in *. omega.
    apply repeat_length.
    auto.
    auto.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    pred_apply.
    rewrite vsupsyn_range_synced_list; auto.
    erewrite <- extract_blocks_subset_trans; eauto.
    rewrite H16.
    cancel; eauto.
    apply repeat_length.
    erewrite <- extract_blocks_subset_trans; eauto.
    rewrite H16.
    rewrite IndRec.Defs.ipack_one.
    setoid_rewrite combine_length_eq.
    rewrite repeat_length; simpl; auto.
    apply repeat_length.
    unfold IndRec.Defs.item in *. simpl in *. omega.
    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: eauto.
  Qed.

       
  Local Hint Extern 0 ({{_|_}} Bind (indrec_write_blind _ _ _ _) _) => apply indrec_write_blind_ok : prog.

  Definition indput_upd_if_necessary lxp ir v indbns to_grow ms := 
    If (addr_eq_dec v #(selN indbns to_grow $0)) {
      Ret ms
    } else {
      indrec_write_blind lxp ir (indbns ⟦ to_grow := ($ v)⟧) ms
    }.

 Theorem indput_upd_if_necessary_ok :
    forall lxp ir v indbns to_grow ms pr,
    {< F Fm m0 sm m bxp Fs,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[ BALLOCC.bn_valid bxp ir ]] *
           [[[ m ::: (Fm * indrep_n_helper Fs bxp ir indbns) ]]]
    POST:bm', hm', RET: ms
           exists m' indbns', 
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[ indbns' = updN indbns to_grow ($ v) ]] *
           [[[ m' ::: (Fm * indrep_n_helper Fs bxp ir indbns') ]]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indput_upd_if_necessary lxp ir v indbns to_grow ms.
  Proof. 
    unfold indput_upd_if_necessary. unfold BALLOCC.bn_valid.
    unfold indrec_write_blind.
    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    pred_apply; rewrite natToWord_wordToNat. rewrite updN_selN_eq. cancel.

    step.
    unfold indrep_n_helper. destruct (addr_eq_dec ir 0); try congruence. cancel.
    apply repeat_length.
    step.
    unfold indrep_n_helper. destruct (addr_eq_dec ir 0); try congruence.
    rewrite indrep_n_helper_valid_sm in * by auto.
    denote lift_empty as Hl. destruct_lift Hl. cancel; eauto.
  Qed.

  
  Local Hint Extern 1 ({{_|_}} Bind (indput_upd_if_necessary _ _ _ _ _ _) _) => apply indput_upd_if_necessary_ok : prog.

  Fixpoint indput indlvl lxp bxp root off bn ms :=
    let N := NIndirect ^ indlvl in
    let is_alloc := (addr_eq_dec root 0) in
    let^ (ms, ir) <- If (is_alloc) {
        BALLOCC.alloc lxp bxp ms
      } else {
        Ret ^(ms, Some root)
      };;
    match ir with
    | None => Ret ^(ms, 0)
    | Some ir =>
      match indlvl with
      | 0 => lms <- If (is_alloc) {
                      indrec_write_blind lxp ir ((repeat $0 NIndirect) ⟦ off := bn ⟧) (BALLOCC.MSLog ms)
                   } else {
                      IndRec.put lxp ir off Public bn (BALLOCC.MSLog ms)
                   };;
        Ret ^((BALLOCC.upd_memstate lms ms), ir)
      | S indlvl' =>
        let to_grow := off / N in
        let^ (lms, indbns) <- indput_get_blocks lxp is_alloc ir (BALLOCC.MSLog ms);;
        let ir_to_grow := #(selN indbns to_grow $0) in
        let^ (ms, v) <- indput indlvl' lxp bxp ir_to_grow (off mod N) bn 
                (BALLOCC.upd_memstate lms ms);;
        If (addr_eq_dec v 0) {
          Ret ^(ms, 0)
        } else {
          lms <- indput_upd_if_necessary lxp ir v indbns to_grow (BALLOCC.MSLog ms);;
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

Theorem indput_ok :
  forall indlvl lxp bxp ir off bn ms pr,
    {< F Fm Fs m0 sm m l freelist IFs,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs ir l *
              BALLOCC.rep bxp freelist ms) ]]] *
           [[ off < length l ]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, ir')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           ([[ ir' = 0 ]] \/
           exists freelist' l' IFs',
           [[ ir = 0 \/ ir = ir' ]] *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' ir' l' *
             BALLOCC.rep bxp freelist' ms) ]]] *
           [[ incl freelist' freelist ]] * [[ l' = updN l off bn ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]])
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indput indlvl lxp bxp ir off bn ms.
    Proof. 
      induction indlvl; intros; simpl.
      + step.
      - step.
        prestep; norm; try congruence.
        unfold stars; simpl; eassign F_; cancel.
        inversion H7; subst.
        intuition.
          * unfold BALLOCC.bn_valid in *. intuition auto.
          * unfold BALLOCC.bn_valid in *. intuition auto.
          * pred_apply;  cancel.
          * step.
            step.
            erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_r; cancel.
            unfold BALLOCC.bn_valid in *; intuition.
            rewrite indrep_n_helper_0. rewrite indrep_n_helper_valid by omega.
            unfold BALLOCC.bn_valid. cancel.
            denote (IFs <=p=> emp) as Hi.
            eexists. rewrite Hi. split; cancel.
          * rewrite <- H1; cancel; eauto.
          * unfold stars; simpl; eauto.
          * intuition.
            step.
            erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_l; cancel.
            cancel.
      - step.
        prestep; norm; try congruence.
        unfold stars; simpl; eauto.
        intuition.
        
        step.
        prestep; norm.
        unfold stars; simpl; eassign F_;
        erewrite LOG.rep_hashmap_subset; eauto; cancel.
        intuition.
        eauto.
        pred_apply; rewrite indrep_n_helper_valid by omega. cancel.

        step.
        step.
        erewrite LOG.rep_hashmap_subset; eauto; cancel.
        or_r. cancel.
        rewrite indrep_n_helper_valid in * by omega. cancel.
        rewrite BALLOC.Alloc.repeat_updN_noop.
        repeat rewrite IndRec.Defs.ipack_length.
        rewrite length_updN; auto.
        match goal with [H : context [?P] |- ?P] => destruct_lift H end. auto.
        match goal with [H : context [?P] |- ?P] => destruct_lift H end. auto.
        rewrite <- H1; cancel.

      + step.
        - step. prestep. norm; try congruence. 
          cancel. intuition auto.
          prestep; norm.
          unfold stars; simpl; eassign F_;
          erewrite LOG.rep_hashmap_subset; eauto; cancel.
          intuition.
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
          step.
          step.
          step.
          erewrite LOG.rep_hashmap_subset; eauto; cancel.
          or_l; cancel.

          step.
          step.
          step.
          erewrite LOG.rep_hashmap_subset; eauto; cancel.
          or_l; cancel.
          step.
          step.
          prestep; norm.
          cancel.
          Opaque corr2.
          repeat split.
          unfold BALLOCC.bn_valid in *. intuition auto.
          rewrite length_updN.
          rewrite repeat_length.
          unfold IndSig.RALen; omega.
          intuition auto.
          unfold BALLOCC.bn_valid in *; intuition auto.
          pred_apply; cancel.
          auto.
          prestep. cancel.
          step.
          * erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_r.
            safecancel.
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
            cbv; auto.
            eexists; eauto.
            indrep_n_tree_bound.
            rewrite pred_fold_left_updN_removeN.
            rewrite indrep_n_helper_0_sm in *.
            psubst.
            match goal with H: context [lift_empty] |- _ => destruct_lift H end.
            denote (_ <=p=> emp) as Hi. rewrite Hi; clear Hi.
            rewrite indrep_n_helper_0 in *.
            match goal with H: context [lift_empty] |- _ => destruct_lift H end.
            rewrite repeat_length in *.
            match goal with H: context [listmatch _ (combine (repeat _ _) _)] |- _ =>
              rewrite listmatch_isolate with (a := combine (repeat _ _) _) in H;
              [ erewrite selN_combine in H; cbn [fst snd] in H;
                [rewrite repeat_selN', roundTrip_0, indrep_n_tree_0 in H;
                destruct_lift H |..] |..]
            end.
            match goal with |- context [removeN _ ?n] =>
              rewrite pred_fold_left_selN_removeN with (i := n) end.
            denote (_ <=p=> emp) as Hi. rewrite Hi; clear Hi.
            split; cancel.
            all: autorewrite with lists.
            omega.
            indrep_n_tree_bound.
            indrep_n_tree_bound.
            replace (length dummy1) with NIndirect by indrep_n_tree_bound.
            indrep_n_tree_bound.
            match goal with |- context [updN ?l ?i] =>
              replace (repeat _ _) with (selN l i nil)
            end. erewrite <- updN_concat.
            rewrite plus_comm, mult_comm.
            rewrite <- Nat.div_mod by mult_nonzero. reflexivity.
            auto.
            auto.
            rewrite indrep_n_helper_0 in *.
            match goal with H : _ |- context [selN ?l ?I ?d] =>
              erewrite listmatch_isolate with (b := l) (i := I) (bd := d), selN_combine in H;
              [cbn [fst snd] in H; rewrite repeat_selN' in H|..]
            end.
            rewrite indrep_n_tree_0 in *.
            destruct_lifts. auto.
            substl (length dummy1).
            indrep_n_tree_bound.
            autorewrite with lists. substl (length dummy1). indrep_n_tree_bound.
            indrep_n_tree_bound.
          * cancel.
          * intros; rewrite <- H1; cancel; eauto.
          * prestep; norm.
            cancel.
            repeat split.
            step.
            erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_l; cancel.
            cancel.
          * step.
          * rewrite <- H1; cancel; eauto.
          * cancel.
          * norml; try congruence.
            norm.
            cancel.
            repeat split.
            step.
            erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_l; cancel.
            cancel.
        - prestep; norm.
          cancel.
          repeat split; [ |cancel].
          (* prestep; norm.
          unfold stars; simpl; rewrite LOG.rep_hashmap_subset; eauto; cancel.
          repeat split.*)
          safestep; [ | | | | | intros; rewrite <- H1; cancel; eauto].
          rewrite LOG.rep_hashmap_subset; eauto; cancel.
          eauto.
          pred_apply; cancel.
          eauto.
          2: cancel.
          prestep; norm.
          cancel.
          repeat split.
          pred_apply; indrep_n_extract; solve [cancel | indrep_n_tree_bound].
          match goal with |- ?a mod ?b < ?c => replace c with b; auto end.
          symmetry. apply Forall_selN. eauto.
          indrep_n_tree_bound.
          psubst.
          pred_apply.
          match goal with |- context [selN _ ?I ?d] =>
            rewrite pred_fold_left_selN_removeN with (i := I);
            unify d (@emp _ addr_eq_dec bool); cancel
          end.
          auto.
          2: intros; rewrite <- H1; cancel; eauto.
          prestep; norm.
          all: try cancel.
          {
            repeat split.
            prestep; norm.
            cancel.
            repeat split.
            2: cancel.
            prestep; norm.
            unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_l; cancel.
            repeat (split; eauto).
     
            prestep; norm.
          }
          
          repeat split.
          {
            prestep; norm.
            cancel.
            repeat split.
            2: cancel.
            prestep; norm.
            all: try (unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel).
            all: try (or_l; cancel).
            all: repeat (split; eauto).
          }


          safestep.
          all: try (rewrite <- H1; cancel; eauto).
          {
            prestep; norm.
            cancel.
            repeat split.
            2: cancel.
            prestep; norm.
            unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_r; cancel.
            match goal with [H : context [indrep_n_helper] |- _] =>
               pose proof H; rewrite indrep_n_helper_length_piff,
               indrep_n_helper_valid in H by omega;
               destruct_lift H end.
            rewrite combine_updN. rewrite listmatch_updN_removeN. cbn [fst snd].
            eassign (nil:list waddr).
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
            eauto.
            repeat (split; eauto).
          }

          {
            prestep; norm.
            cancel.
            repeat split.
            2: cancel.
            prestep; norm.
            unfold stars; simpl; erewrite LOG.rep_hashmap_subset; eauto; cancel.
            or_r. safecancel.
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
            auto.
            eassign 1.
            eassign 0.
            simpl; auto.
            repeat (split; eauto).
          }
    Grab Existential Variables. all : eauto.
        all: solve [exact nil | exact valuset0].
  Qed.

  Local Hint Extern 0 ({{_|_}} Bind (indput _ _ _ _ _ _ _) _) => apply indput_ok : prog.
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
      let^ (ms, indbns) <- indread 0 lxp (IRIndPtr ir) ms;;
      let^ (ms, dindbns) <- indread 1 lxp (IRDindPtr ir) ms;;
      let^ (ms, tindbns) <- indread 2 lxp (IRTindPtr ir) ms;;
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
    let^ (ms, indptr)  <- indshrink_helper 0 lxp bxp (IRIndPtr ir)  nl ms;;
    let^ (ms, dindptr) <- indshrink_helper 1 lxp bxp (IRDindPtr ir) nl ms;;
    let^ (ms, tindptr) <- indshrink_helper 2 lxp bxp (IRTindPtr ir) nl ms;;
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
      let^ (ms, indptr, dindptr, tindptr) <- indshrink lxp bxp ir nl' ms;;
      Ret ^(ms, upd_irec ir nl indptr dindptr tindptr
                         (upd_range_fast (IRBlocks ir) nl (NDirect - nl) $0))
    }.

  Definition indgrow lxp bxp ir off bn ms :=
    If (lt_dec off NIndirect) {
      let^ (ms, v) <- indput 0 lxp bxp (IRIndPtr ir) off bn ms;;
      Ret ^(ms, v, v, (IRDindPtr ir), (IRTindPtr ir))
    } else {
      let off := off - NIndirect in
      If (lt_dec off (NIndirect ^ 2)) {
        let^ (ms, v) <- indput 1 lxp bxp (IRDindPtr ir) off bn ms;;
        Ret ^(ms, v, (IRIndPtr ir), v, (IRTindPtr ir))
      } else {
        let off := off - NIndirect ^ 2 in
        let^ (ms, v) <- indput 2 lxp bxp (IRTindPtr ir) off bn ms;;
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
        let^ (ms, v, indptr, dindptr, tindptr) <- indgrow lxp bxp ir off bn ms;;
        If (addr_eq_dec v 0) {
          Ret ^(ms, Err ENOSPCBLOCK)
        } else {
          Ret ^(ms, OK (upd_irec ir (S len) indptr dindptr tindptr (IRBlocks ir)))
        }
      }
    }.

  Theorem get_ok :
    forall lxp bxp ir off ms pr,
    {< F Fm IFs m0 sm m l,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]] *
           [[ off < length l ]]
    POST:bm', hm', RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[ r = selN l off $0 ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} get lxp ir off ms.
  Proof. 
    unfold get.
    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    eapply rep_selN_direct_ok; eauto.
    prestep; norml.
    rewrite rep_piff_indirect in * by omega.
    unfold rep_indirect, indrep in *. destruct_lifts.
    indrep_n_tree_extract_lengths.
    step.
    step.
    all : try substl l.
    all : repeat rewrite selN_app2 by omega.
    all : repeat rewrite selN_firstn by omega.
    all : repeat rewrite skipn_selN.
    all : repeat (congruence || omega || f_equal).
    
    step.
    step.
    all : try substl l.
    all : repeat rewrite selN_app2 by omega.
    all : repeat rewrite selN_firstn by omega.
    all : repeat rewrite skipn_selN.
    all : repeat (congruence || omega || f_equal).

    step.
    step.
    all : try substl l.
    all : repeat rewrite selN_app2 by omega.
    all : repeat rewrite selN_firstn by omega.
    all : repeat rewrite skipn_selN.
    all : repeat (congruence || omega || f_equal).
  Qed.

  
  Theorem read_ok :
    forall lxp bxp ir ms pr,
    {< F Fm IFs m0 sm m l,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: Fm * rep bxp IFs ir l ]]]
    POST:bm', hm', RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
           [[ r = l ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' sm bm' hm'
    >} read lxp ir ms.
  Proof.
    unfold read.
    step; denote rep as Hx.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    rewrite rep_piff_direct in Hx; unfold rep_direct in Hx; destruct_lift Hx.
    substl; substl (length l); auto.
    unfold rep in H0; destruct_lift H0; omega.

    unfold rep, indrep in Hx. destruct_lifts.
    indrep_n_tree_extract_lengths.
    step.
    step.
    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    rewrite app_assoc with (l := firstn _ _).
    rewrite <- firstn_sum_split. rewrite firstn_skipn.
    congruence.
    rewrite <- H1; cancel; eauto.
    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: eauto.
  Qed.


  Lemma indrec_ptsto_pimpl : forall ibn tags indrec,
    IndRec.rep ibn tags indrec =p=> exists v, ibn |-> (v, nil).
  Proof.
    unfold IndRec.rep; cancel.
    assert (length (synced_list (combine tags (IndRec.Defs.ipack indrec))) = 1).
    unfold IndRec.items_valid in *; intuition.
    rewrite synced_list_length; subst.
    setoid_rewrite combine_length.
    rewrite min_r.
    rewrite IndRec.Defs.ipack_length.
    setoid_rewrite H0.
    rewrite Rounding.divup_mul; auto.
    rewrite H2; auto.

    rewrite arrayN_isolate with (i := 0) by omega.
    unfold IndSig.RAStart; rewrite Nat.add_0_r.
    rewrite skipn_oob by omega; simpl.
    instantiate (2 := valuset0).
    setoid_rewrite synced_list_selN; cancel.
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

  Theorem indshrink_helper_ok :
    forall lxp bxp bn nl indlvl ms pr,
    let start := fold_left plus (map (fun i => NIndirect ^ S i) (seq 0 indlvl)) 0 in
    {< F Fm Fs IFs m0 sm m l freelist,
    PERM:pr
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * indrep_n_tree indlvl bxp IFs bn l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, r)  exists m' freelist' IFs' l',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * indrep_n_tree indlvl bxp IFs' r l' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ l' = upd_range l (nl - start) (length l - (nl - start)) $0 ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indshrink_helper indlvl lxp bxp bn nl ms.
  Proof. 
    unfold indshrink_helper.
    prestep. norml.
    indrep_n_tree_extract_lengths.
    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    replace (_ - (_ - _)) with 0 by omega. rewrite upd_range_0. auto.
  Qed.


  Local Hint Extern 1 ({{_|_}} Bind (indshrink_helper _ _ _ _ _ _ ) _) => apply indshrink_helper_ok : prog.

  Theorem indshrink_ok :
    forall lxp bxp ir nl ms pr,
    {< F Fm Fs IFs0 IFs1 IFs2 m0 sm m l0 l1 l2 freelist,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[ nl <= length (l0 ++ l1 ++ l2) ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp IFs0 (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp IFs1 (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp IFs2 (IRTindPtr ir) l2 *
                           BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs0 * IFs1 * IFs2 * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, indptr', dindptr', tindptr')
           exists m' freelist' l0' l1' l2' IFs0' IFs1' IFs2',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp IFs0' indptr' l0' *
                            indrep_n_tree 1 bxp IFs1' dindptr' l1' *
                            indrep_n_tree 2 bxp IFs2' tindptr' l2' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ l0' ++ l1' ++ l2' = upd_range (l0 ++ l1 ++ l2) nl (length (l0 ++ l1 ++ l2) - nl) $0 ]] *
           [[ (Fs * IFs0' * IFs1' * IFs2' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indshrink lxp bxp ir nl ms.
  Proof. 
    unfold indshrink.
    step.
    step.
    step.
    step.
    safestep.
    erewrite LOG.rep_hashmap_subset; eauto.
    repeat rewrite app_length in *.
    indrep_n_tree_extract_lengths.
    autorewrite with core.
    repeat rewrite upd_range_eq_app_firstn_repeat by (repeat rewrite app_length; omega).
    destruct (le_dec nl NIndirect);
    destruct (le_dec nl (NIndirect + NIndirect * NIndirect)); try omega.
    pred_apply; cancel.
    pred_apply; cancel.
    pred_apply; cancel.
    subst.

    repeat rewrite app_length in *.
    indrep_n_tree_extract_lengths.
    autorewrite with core.
    repeat rewrite upd_range_eq_app_firstn_repeat by (repeat rewrite app_length; omega).
    destruct (le_dec nl NIndirect);
    destruct (le_dec nl (NIndirect + NIndirect * NIndirect)); try omega.

    all: repeat match goal with
      | [|- context [?a - ?b] ] => replace (a - b) with 0 by omega
      | [|- context [firstn ?x ?l'] ] => rewrite firstn_oob with (n := x) (l := l') by omega
      | [|- context [firstn ?x ?l'] ] => rewrite firstn_app_le with (n := x) by omega
      | [|- context [firstn ?x ?l'] ] => rewrite firstn_app_l with (n := x) by omega
     end; repeat rewrite <- app_assoc; simpl; autorewrite with core; repeat rewrite repeat_app.    
    all : repeat rewrite app_length; try solve [repeat (omega || f_equal)].

    cancel.
    auto.
    rewrite <- H1; cancel; eauto.
    rewrite <- H1; cancel; eauto.
    Unshelve.
    all: eauto.
  Qed.


  Local Hint Extern 1 ({{_|_}} Bind (indshrink _ _ _ _ _) _) => apply indshrink_ok : prog.

  Theorem shrink_ok :
    forall lxp bxp ir nr ms pr,
    {< F Fm Fs IFs m0 sm m l freelist,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[[ m ::: (Fm * rep bxp IFs ir l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, r)  exists m' freelist' l' IFs',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' r l' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           exists ind dind tind dirl, [[ r = upd_irec ir ((IRLen ir) - nr) ind dind tind dirl ]] *
           [[ l' = firstn (IRLen ir - nr) l ]] *
           [[ incl freelist freelist' ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} shrink lxp bxp ir nr ms.
  Proof.
    unfold shrink. intros.
    repeat rewrite upd_range_fast_eq.
    prestep; norml.
    denote rep as Hx. unfold rep in Hx. destruct_lifts.
    cancel.
    + (* case 1: all in direct blocks *)
      step.
      step.
      erewrite LOG.rep_hashmap_subset; eauto.
      pred_apply. unfold rep.
      autorewrite with core. cancel.
      - apply upd_len_direct_indrep.
      - rewrite min_l by omega. setoid_rewrite Nat.mul_1_r; omega.
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
      prestep; norml.
      safecancel.
      - repeat rewrite app_length.
        indrep_n_tree_extract_lengths. omega.
      - psubst. cancel.
        
      - step.
        safestep.
        erewrite LOG.rep_hashmap_subset; eauto.
        pred_apply; unfold rep, indrep. autorewrite with core; auto.
        safecancel; rewrite mult_1_r in *.
        rewrite indrep_n_length_pimpl with (indlvl := 0).
        rewrite indrep_n_length_pimpl with (indlvl := 1).
        rewrite indrep_n_length_pimpl with (indlvl := 2). cancel. rewrite mult_1_r in *.
        substl (NIndirect * NIndirect). substl NIndirect.
        rewrite firstn_app2. rewrite skipn_app_r. repeat rewrite skipn_app. rewrite firstn_app2.
        cancel.
        auto.
        auto.
        eassign (firstn (IRLen ir - nr) l).
        apply firstn_length_l.
        omega.
        rewrite firstn_length_l; omega.
        rewrite upd_range_length; eauto.
        eauto.
        rewrite firstn_length_l by omega.
        indrep_n_tree_extract_lengths.
        all : try rewrite upd_range_length.
        all : eauto.
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
        rewrite firstn_length_l by omega.
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
        cancel.
    Grab Existential Variables.
    all: eauto.
  Qed.



  Theorem indgrow_ok :
    forall lxp bxp ir off bn ms pr,
    {< F Fm Fs m0 sm m l0 l1 l2 freelist IFs0 IFs1 IFs2,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[ off < NBlocks - NDirect ]] * [[ bn <> $0 ]] *
           [[[ m ::: (Fm * indrep_n_tree 0 bxp IFs0 (IRIndPtr ir) l0 *
                           indrep_n_tree 1 bxp IFs1 (IRDindPtr ir) l1 *
                           indrep_n_tree 2 bxp IFs2 (IRTindPtr ir) l2 * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs0 * IFs1 * IFs2 * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, v, indptr', dindptr', tindptr')
           exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           ([[ v = 0 ]] \/ [[ v <> 0 ]] *
           exists freelist' l0' l1' l2' IFs0' IFs1' IFs2',
           [[ updN (l0 ++ l1 ++ l2) off bn = l0' ++ l1' ++ l2' ]] *
           [[[ m' ::: (Fm * indrep_n_tree 0 bxp IFs0' indptr' l0' *
                            indrep_n_tree 1 bxp IFs1' dindptr' l1' *
                            indrep_n_tree 2 bxp IFs2' tindptr' l2' * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ (Fs * IFs0' * IFs1' * IFs2' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist' freelist ]])
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} indgrow lxp bxp ir off bn ms.
  Proof. 
    unfold indgrow. prestep. norml.
    indrep_n_tree_extract_lengths.
    prestep.
    norml.
    norm.
    cancel.
    Opaque corr2.
    repeat split.
    pred_apply; cancel.
    omega.
    pred_apply; cancel.
    auto.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    or_l; cancel.

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
    repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence.

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
    repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence.
    intros; rewrite<- H1; cancel.


    norml.
    norm.
    cancel.
    Opaque corr2.
    repeat split.
    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    or_l; cancel.

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
    repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence.

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
    repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence.

    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    or_l; cancel.
    

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
    repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence.

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    cancel.
    match goal with |- context [?a = 0] =>
      destruct (addr_eq_dec a 0); [or_l|or_r]; cancel
    end.
    repeat rewrite updN_app2 by omega; try rewrite updN_app1 by omega; congruence.
  Qed.

       
  Local Hint Extern 1 ({{_|_}} Bind (indgrow _ _ _ _ _ _) _) => apply indgrow_ok : prog.

  Theorem grow_ok :
    forall lxp bxp ir bn ms pr,
    {< F Fm Fs m0 sm m IFs l freelist,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BALLOCC.MSLog ms) sm bm hm *
           [[ length l < NBlocks ]] *
           [[[ m ::: (Fm * rep bxp IFs ir l * BALLOCC.rep bxp freelist ms) ]]] *
           [[ (Fs * IFs * BALLOCC.smrep freelist)%pred sm ]]
    POST:bm', hm', RET:^(ms, r)
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' \/
           exists freelist' ir' IFs',
           [[ r = OK ir' ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (BALLOCC.MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep bxp IFs' ir' (l ++ [bn]) * BALLOCC.rep bxp freelist' ms) ]]] *
           [[ IRAttrs ir' = IRAttrs ir /\ length (IRBlocks ir') = length (IRBlocks ir) ]] *
           [[ (Fs * IFs' * BALLOCC.smrep freelist')%pred sm ]] *
           [[ incl freelist' freelist ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
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

    step.
    erewrite LOG.rep_hashmap_subset; eauto.
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
    cancel.

    (* update indirect blocks *)
    step.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    + (* write 0 block *)
      unfold rep in *. destruct_lift Hx.
      rewrite indrep_length_pimpl in *. unfold indrep in *. destruct_lifts.
      indrep_n_tree_extract_lengths.
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
      step.
      hoare.
      - rewrite mult_1_r. omega.
      - psubst; cancel.
      - step.
        step.
        step.
        erewrite LOG.rep_hashmap_subset; eauto.
        or_l; cancel.

        step.
        step.
        step.
        safestep.
        rewrite <- skipn_skipn' in *. repeat rewrite firstn_skipn in *.
        indrep_n_tree_extract_lengths.
        or_r. 
        erewrite LOG.rep_hashmap_subset; eauto.
        safecancel; autorewrite with core.
        eauto.
        autorewrite with core.
        setoid_rewrite <- skipn_skipn'.
        cancel.
        rewrite firstn_app2. setoid_rewrite skipn_app_l. rewrite skipn_oob. rewrite app_nil_l.
        rewrite firstn_app2. rewrite skipn_app_l. rewrite skipn_oob. rewrite app_nil_l.
        (* `cancel` calls `simpl` which raises a Not_found exception here; don't know why *)
        cancel.
        all: autorewrite with core; eauto.
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

  Hint Extern 1 ({{_|_}} Bind (get _ _ _ _) _) => apply get_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (shrink _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (grow _ _ _ _ _) _) => apply grow_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _ _) (rep _ _ _ _)) => constructor : okToUnify.

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