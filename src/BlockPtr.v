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
      then [[ iblocks = repeat ($ 0) NIndirect ]]
      else [[ BALLOC.bn_valid bxp ibn ]] * IndRec.rep ibn iblocks
    )%pred.

  (* indlvl = 0 if ibn is the address of an indirect block,
     indlvl = 1 for doubly indirect, etc. *)

 Fixpoint indrep_n_tree indlvl bxp ibn l nvalid :=
    (exists iblocks l_part, indrep_n_helper bxp ibn iblocks nvalid *
    [[ l = concat l_part ]] *
    match indlvl with
    | 0 => [[ iblocks = concat l_part ]]
    | S indlvl' =>  let divisor := NIndirect ^ indlvl in
                    let nr := divup nvalid divisor in
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
    indrep_n_helper bxp ibn l 0 <=p=> [[ l = repeat $0 NIndirect ]] * emp.
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
    | [ |- 0 < Nat.pow _ _ ] => apply neq_0_lt, not_eq_sym
    | [ |- 0 < _ ] => apply neq_0_lt
    | [ |- 0 <> _ ] => apply not_eq_sym
    end; auto).


  (************* program *)

  Fixpoint indget (indlvl : nat) lxp (bn : addr) off ms :=
    let divisor := NIndirect ^ indlvl in
    let^ (ms, v) <- IndRec.get lxp bn (off / divisor) ms;
    match indlvl with
    | 0 => Ret ^(ms, v)
    | S indlvl' => indget indlvl' lxp (# (Rec.to_word v)) (off mod divisor) ms
    end.

  Definition get lxp (ir : irec) off ms :=
    If (lt_dec off NDirect) {
      Ret ^(ms, selN (IRBlocks ir) off $0)
    } else {
      let^ (ms, v) <- indget 0 lxp (IRIndPtr ir) (off - NDirect) ms;
      Ret ^(ms, v)
    }.

  Fixpoint indread (indlvl : nat) lxp (ir : addr) ms :=
    let^ (ms, indbns) <- IndRec.read lxp ir 1 ms;
    match indlvl with
      | 0 => Ret ^(ms, indbns)
      | S indlvl' =>
        let^ (ms', r) <- ForN i < NIndirect
          Hashmap hm
          Ghost [ F Fm l bxp crash m0 m nvalid ]
          Loopvar [ ms r ]
          Invariant
            LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
            [[[ m ::: Fm * indrep_ind indlvl bxp ir l nvalid ]]] *
            [[ r = firstn (i * NIndirect ^ indlvl) l ]]
          OnCrash crash
          Begin
            let^ (ms, v) <- indread indlvl' lxp #(selN indbns i IndRec.Defs.item0) ms;
            Ret ^(ms, r ++ v)
          Rof ^(ms, nil);
          Ret ^(ms', r)
    end.

  Definition read lxp (ir : irec) ms :=
    If (le_dec (IRLen ir) NDirect) {
      Ret ^(ms, firstn (IRLen ir) (IRBlocks ir))
    } else {
      let^ (ms, indbns) <- indread 0 lxp (IRIndPtr ir) ms;
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

  Theorem indget_ok : forall indlvl lxp bxp bn off ms,
    {< F Fm m0 m l nvalid,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * indrep_ind indlvl bxp bn l nvalid ]]] *
           [[ off < nvalid ]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = selN l off $0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} indget indlvl lxp bn off ms.
  Proof.
    induction indlvl; simpl.
    hoare; autorewrite with core; auto; omega.
    repeat safestep.
    - apply Nat.div_lt_upper_bound; mult_nonzero.
      unfold IndRec.rep, IndRec.items_valid, IndRec.Defs.item in *; simpl in *.
      repeat match goal with
        | [H : length ?l = _ |- context [length ?l] ] => rewrite H
        | [H : context [length ?l] |- context [length ?l] ] => destruct_lift H
      end.
      lia.
    - erewrite listmatch_isolate; autorewrite with list.
      unfold Rec.to_word; simpl.
      repeat (rewrite firstn_enumerate ||
              rewrite selN_enumerate   ||
              rewrite selN_firstn      ||
              erewrite snd_pair); eauto.
      cancel.
      all : repeat match goal with
            | [ |- ?off / ?N < divup ?nvalid ?N] => eapply lt_le_trans
            | [ |- ?off / ?N < _ ]=> apply div_lt_divup
            | [ H: ?off < ?nvalid |- ?off < _ ] => apply H
            | [ |- context [length (firstn _ _)] ] => rewrite firstn_length_l
            | [ H : context [IndRec.rep _ ?l] |- context [length ?l] ] =>
                    unfold IndRec.rep, IndRec.items_valid in H; destruct_lift H; substl (length l)
            | [ |- ?a <= ?a ] => auto
            | [ |- divup _ _ <= length ?a ] => substl (length a)
            | [ |- divup _ _ <= _ ] => apply divup_le; lia
            end; auto; mult_nonzero.
    - edestruct Nat.min_spec as [ [H' Hmin] | [H' Hmin] ]; rewrite Hmin; clear Hmin.
      + rewrite <- Nat.lt_add_lt_sub_r.
        apply le_lt_trans with (m := off); auto.
        apply div_mod_le; auto.
      + apply Nat.mod_upper_bound; mult_nonzero.
    - eapply selN_selN_firstn_hom.
      match goal with [H : context [listmatch _ _ _] |- _ ]=>
        rewrite listmatch_lift_r in H; destruct_lift H; eauto end.
      intros; destruct x; simpl.
      rewrite indrep_ind_lift_length.
      instantiate (1 := fun n_w y => indrep_ind _ _ (# (snd n_w)) y (min (_ - (fst n_w) * _) _)); simpl.
      apply piff_refl.
      apply div_lt_mul_lt; mult_nonzero.
      eapply lt_le_trans; [> apply div_lt_divup; mult_nonzero |]; eauto.
      match goal with [H : ?a = _ |- context [?a] ] => substl a end.
      lia.
      Grab Existential Variables.
      all : auto.
  Qed.

  Fact indrep_ind_0_is : forall bxp ibn l, indrep_ind bxp 0 ibn l = 
    ([[length l = NIndirect ]] * [[ BALLOC.bn_valid bxp ibn ]] * IndRec.rep ibn l)%pred.
  Proof. unfold indrep_ind; simpl; rewrite mult_1_r; auto. Qed.

  Fact indrep_ind_S_is : forall bxp indlvl ibn l, indrep_ind bxp (S indlvl) ibn l =
    ([[length l = (NIndirect * NIndirect ^ (S indlvl))%nat ]] * [[ BALLOC.bn_valid bxp ibn ]] * 
      exists iblocks l_part, IndRec.rep ibn iblocks *
        [[ length iblocks = NIndirect ]] * [[ l = concat l_part ]] *
        listmatch (fun ibn' l' => indrep_ind bxp indlvl # (ibn') l') iblocks l_part)%pred.
  Proof. unfold indrep_ind; auto. Qed.

  Fact listmatch_inj : forall  A B l l1 l2 AT AEQ V F1 F2 (f : A -> B -> @pred AT AEQ V) m,
    (forall Fa Fb x a b, (Fa * f x a)%pred m -> (Fb * f x b)%pred m -> a = b) -> (F1 * listmatch f l l1)%pred m
      -> (F2 * listmatch f l l2)%pred m -> l1 = l2.
  Proof.
    induction l; intros; destruct l1, l2; auto.
    all : unfold listmatch in *;
          destruct_lift H0; destruct_lift H1;
          match goal with
          | [ H : 0 = S _ |- _] => inversion H
          | [ H : S _ = 0 |- _] => inversion H
          | [ |- _] => idtac
          end.
    f_equal.
    eapply H with (x := a).
      eapply pimpl_apply; [> | exact H0]; cancel.
      eapply pimpl_apply; [> | exact H1]; cancel.
      eapply IHl.
      eassumption.
      eapply pimpl_apply; [> | exact H0]; cancel.
      eapply pimpl_apply; [> | exact H1]; cancel.
  Qed.

  Theorem indrep_ind_inj : forall indlvl Fa Fb l1 l2 bxp ibn m,
    (Fa * indrep_ind bxp indlvl ibn l1)%pred m -> (Fb * indrep_ind bxp indlvl ibn l2)%pred m -> l1 = l2.
  Proof.
    induction indlvl; intros; simpl in *.
    eapply IndRec.rep_inj; eauto.
    eapply pimpl_apply; [> | exact H]; cancel.
    eapply pimpl_apply; [> | exact H0]; cancel.
    destruct_lift H.
    destruct_lift H0.
    assert (dummy1 = dummy).
    eapply IndRec.rep_inj.
    eapply pimpl_apply; [> | exact H0]; cancel.
    eapply pimpl_apply; [> | exact H]; cancel.
    subst.
    f_equal.
    eapply listmatch_inj with
      (f := fun a b => indrep_ind bxp indlvl (# a) b)
      (l := dummy); intros.
    eapply IHindlvl; eauto.
    eapply pimpl_apply; [> | exact H]; cancel.
    eapply pimpl_apply; [> | exact H0]; cancel.
  Qed.

  Theorem indrec_rep_unify : forall l1 l2 l3 l4 Fa Fb Fc Fd bxp indlvl ir m,
    (Fa * IndRec.rep ir l1)%pred m -> (Fb * IndRec.rep ir l2)%pred m ->
    (Fc * listmatch (fun a b => indrep_ind bxp indlvl (# a) b) l1 l3)%pred m ->
    (Fd * listmatch (fun a b => indrep_ind bxp indlvl (# a) b) l2 l4)%pred m ->
    l1 = l2 /\ l3 = l4.
  Proof.
    intros.
    assert (l1 = l2) by (eapply IndRec.rep_inj; eauto).
    subst; intuition.
    eapply listmatch_inj; eauto.
    simpl; intros.
    eapply indrep_ind_inj; eauto.
  Qed.

  Ltac unify_rep := match goal with
    [ l1 : IndRec.Defs.itemlist, l2 : IndRec.Defs.itemlist,
      l3 : list (list waddr), l4 : list (list waddr),
      H1 : context [listmatch _ ?l1 ?l3],
      H2 : context [listmatch _ ?l2 ?l4]
      |- _] => assert (l1 = l2 /\ l3 = l4);
      [> eapply indrec_rep_unify;
        [> eapply pimpl_apply; [> | exact H1]; cancel |
           eapply pimpl_apply; [> | exact H2]; cancel |
           eapply pimpl_apply; [> | exact H1]; cancel |
           eapply pimpl_apply; [> | exact H2]; cancel ] | intuition; subst]
      end.

  Theorem indread_ok : forall indlvl lxp bxp ir ms,
  {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: Fm * indrep_ind bxp indlvl ir l ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = l ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} indread indlvl lxp ir ms.
  Proof.
    induction indlvl.
    unfold indread; hoare.
    unfold IndRec.Defs.item; simpl; apply firstn_oob; omega.
    unfold indread; hoare; try unify_rep.
    rewrite firstn_oob by omega.
    rewrite listmatch_extract.
    cancel.
    unfold IndRec.Defs.item in *; simpl in *; omega.
    erewrite plus_comm, firstn_sum_split.
    f_equal.
    apply listmatch_length_r in H8 as H'.
    unfold IndRec.Defs.item in *; simpl in *.
    rewrite concat_hom_skipn.
    erewrite <- concat_hom_subselect_firstn; auto.
    rewrite firstn_oob; auto.
    rewrite listmatch_extract in H8.
    rewrite indrep_ind_lift in H8.
    destruct_lift H8.
    rewrite H16; auto.
    all : try match goal with
          | [ |- _ < _ ] => unfold IndRec.Defs.item in *; simpl in *; omega
          | [ |- firstn _ _ = _] => apply firstn_oob; omega
          | [l1 : (list (list waddr)), H : context[listmatch _ _ ?l1] |- Forall _ ?l1]
            => rewrite listmatch_lift_r in H;
              [> destruct_lift H; simpl; eassumption
               | intros; rewrite indrep_ind_lift; split; cancel ]
          end.
    apply LOG.rep_hashmap_subset; auto.
    Grab Existential Variables.
    all : eauto; try exact ($ 0); try exact tt.
  Qed.

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

