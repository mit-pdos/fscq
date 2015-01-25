Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArray.
Require Import GenSep.
Require Import ListPred.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
  IXLen : addr
}.

Module INODE.
  Definition blocks_per_inode := 3.
  Definition inodetype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) blocks_per_inode)]).

  Definition inode' := Rec.data inodetype.
  Definition inode0' := @Rec.of_word inodetype $0.

  Definition itemsz := Rec.len inodetype.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (IXStart xp) (IXLen xp).

  Definition rep' xp (ilist : list inode') :=
    ([[ length ilist = wordToNat (IXLen xp ^* items_per_valu) ]] *
     RecArray.array_item inodetype items_per_valu itemsz_ok (xp_to_raxp xp) ilist
    )%pred.

  Definition iget' T lxp xp inum rx : prog T :=
    RecArray.get inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum rx.

  Definition iput' T lxp xp inum i rx : prog T :=
    RecArray.put inodetype items_per_valu itemsz_ok
      lxp (xp_to_raxp xp) inum i rx.

  Theorem iget_ok' : forall lxp xp inum,
    {< F A mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep' xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = ino ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget' lxp xp inum.
  Proof.
    unfold iget', rep'; intros.
    eapply pimpl_ok2. 
    eapply RecArray.get_ok; word_neq.
    intros; norm.
    cancel.
    intuition; eauto.
    apply list2mem_inbound in H4.
    apply lt_wlt; omega.
    apply list2mem_sel with (def:=inode0') in H4.
    step.
  Qed.

  Theorem iput_ok' : forall lxp xp inum i,
    {< F A mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep' xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ Rec.well_formed i ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m' ilist', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep' xp ilist')%pred m' ]] *
            [[ (A * inum |-> i)%pred (list2mem ilist')]] )
    CRASH  LOG.log_intact lxp mbase
    >} iput' lxp xp inum i.
  Proof.
    unfold iput', rep'.
    intros. eapply pimpl_ok2. eapply RecArray.put_ok; word_neq.
    intros; norm.
    cancel.
    intuition; eauto.
    apply list2mem_inbound in H5.
    apply lt_wlt; omega.
    apply list2mem_sel with (def:=inode0') in H5 as H5'.
    step.
    apply pimpl_or_r; right.
    cancel.
    autorewrite with core; auto.
    eapply list2mem_upd; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget' _ _ _) _) => apply iget_ok' : prog.
  Hint Extern 1 ({{_}} progseq (iput' _ _ _ _) _) => apply iput_ok' : prog.


  Opaque Rec.recset Rec.recget.

  Ltac rec_simpl :=
      unfold Rec.recset', Rec.recget'; simpl;
      repeat (repeat rewrite Rec.set_get_same; auto;
              repeat rewrite <- Rec.set_get_other by discriminate; auto).

  Lemma inode_set_len_get_len : forall (ino : inode') v,
    ((ino :=> "len" := v) :-> "len") = v.
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_blocks_get_blocks : forall (ino : inode') v,
    ((ino :=> "blocks" := v) :-> "blocks") = v.
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_len_get_blocks : forall (ino : inode') v,
    ((ino :=> "len" := v) :-> "blocks") = ino :-> "blocks".
  Proof.
    intros; rec_simpl.
  Qed.

  Lemma inode_set_blocks_get_len : forall (ino : inode') v,
    ((ino :=> "blocks" := v) :-> "len") = ino :-> "len".
  Proof.
    intros; rec_simpl.
  Qed.

  Transparent Rec.recset Rec.recget.

  Hint Rewrite inode_set_len_get_len : core.
  Hint Rewrite inode_set_len_get_blocks : core.
  Hint Rewrite inode_set_blocks_get_blocks : core.
  Hint Rewrite inode_set_blocks_get_len : core.



  (* separation logic based theorems *)

  Record inode := {
    IBlocks : list addr
    (* add indirect link later *)
  }.

  Definition inode0 := Build_inode nil.

  Definition igetlen T lxp xp inum rx : prog T :=
    i <- iget' lxp xp inum;
    rx (i :-> "len").

  Definition iget T lxp xp inum off rx : prog T :=
    i <- iget' lxp xp inum ;
    rx (sel (i :-> "blocks") off $0).

  Definition iput T lxp xp inum off a rx : prog T :=
    i <- iget' lxp xp inum ;
    let i' := i :=> "blocks" := (upd (i :-> "blocks") off a) in
    ok <- iput' lxp xp inum i'; rx ok.

  Definition igrow T lxp xp inum a rx : prog T :=
    i <- iget' lxp xp inum ;
    let i' := i :=> "blocks" := (upd (i :-> "blocks") (i :-> "len") a) in
    let i'' := i' :=> "len" := (i' :-> "len" ^+ $1) in
    ok <- iput' lxp xp inum i''; rx ok.

  Definition ishrink T lxp xp inum rx : prog T :=
    i <- iget' lxp xp inum ;
    let i' := i :=> "len" := (i :-> "len" ^- $1) in
    ok <- iput' lxp xp inum i'; rx ok.

  Definition inode_match ino (ino' : inode') : @pred valu := (
    [[ length (IBlocks ino) = wordToNat (ino' :-> "len") ]] *
    (* The following won't hold after introducing indirect blocks.
       For indirect blocks, we need to refer to disk state,
       so write inode_match in separation logic style. *)
    [[ wordToNat (ino' :-> "len") <= blocks_per_inode ]] *
    [[ IBlocks ino = firstn (length (IBlocks ino)) (ino' :-> "blocks") ]]
    )%pred.

  Definition rep xp (ilist : list inode) :=
    (exists ilist', rep' xp ilist' *
     listmatch inode_match ilist ilist')%pred.


  Lemma inode_blocks_length: forall m xp l inum F,
    (F * rep' xp l)%pred m ->
    inum < length l ->
    length (selN l inum inode0' :-> "blocks") = blocks_per_inode.
  Proof.
    intros.
    remember (selN l inum inode0') as i.
    unfold Rec.recset', Rec.recget', rep' in H.
    rewrite RecArray.array_item_well_formed' in H.
    destruct i; destruct p. 
    destruct_lift H.
    rewrite Forall_forall in *.
    apply (H3 (d, (d0, tt))).
    rewrite Heqi.
    apply Array.in_selN; auto.
  Qed.

  Lemma inode_blocks_length': forall m xp l inum F d d0 u,
    (F * rep' xp l)%pred m ->
    inum < length l ->
    (d, (d0, u)) = selN l inum inode0' ->
    length d0 = blocks_per_inode.
  Proof.
    intros.
    unfold rep' in H.
    rewrite RecArray.array_item_well_formed' in H.
    destruct_lift H.
    rewrite Forall_forall in *.
    apply (H4 (d, (d0, tt))).
    rewrite H1.
    apply Array.in_selN; intuition.
  Qed.


  (* Hints for resolving default values *)

  Fact resolve_sel_inode0' : forall l i d,
    d = inode0' -> sel l i d = sel l i inode0'.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0' : forall l i d,
    d = inode0' -> selN l i d = selN l i inode0'.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_inode0 : forall l i d,
    d = inode0 -> sel l i d = sel l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_inode0 : forall l i d,
    d = inode0 -> selN l i d = selN l i inode0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_addr0 : forall l i (d : addr),
    d = $0 -> sel l i d = sel l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_addr0 : forall l i (d : addr),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_sel_valu0 : forall l i (d : valu),
    d = $0 -> sel l i d = sel l i $0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_valu0 : forall l i (d : valu),
    d = $0 -> selN l i d = selN l i $0.
  Proof.
    intros; subst; auto.
  Qed.


  Hint Rewrite resolve_sel_inode0'  using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0' using reflexivity : defaults.
  Hint Rewrite resolve_sel_inode0   using reflexivity : defaults.
  Hint Rewrite resolve_selN_inode0  using reflexivity : defaults.
  Hint Rewrite resolve_sel_addr0    using reflexivity : defaults.
  Hint Rewrite resolve_selN_addr0   using reflexivity : defaults.
  Hint Rewrite resolve_sel_valu0    using reflexivity : defaults.
  Hint Rewrite resolve_selN_valu0   using reflexivity : defaults.


  Lemma rep_bound: forall F xp l m,
    (F * rep xp l)%pred m
    -> length l <= wordToNat (IXLen xp ^* items_per_valu).
  Proof.
    unfold rep, rep'; intros.
    destruct_lift H.
    erewrite listmatch_length_r; eauto; omega.
  Qed.

  Lemma blocks_bound: forall F xp l m i,
    (F * rep xp l)%pred m
    -> length (IBlocks (sel l i inode0)) <= wordToNat (natToWord addrlen blocks_per_inode).
  Proof.
    unfold rep, sel; intros.
    destruct_lift H.
    destruct (lt_dec (wordToNat i) (length l)).
    extract_listmatch_at i; unfold blocks_per_inode in *.
    autorewrite with defaults; omega.
    rewrite selN_oob by omega.
    simpl; omega.
  Qed.

  Ltac inode_bounds' := match goal with
    | [ H : context [ (rep' _ ?l) ] |- length ?l <= _ ] =>
        unfold rep' in H; destruct_lift H
    | [ H : length ?l = _ |- context [ length ?l ] ] =>
        solve [ rewrite H ; eauto ; try omega ]
    | [ H : _ = length ?l |- context [ length ?l ] ] =>
        solve [ rewrite <- H ; eauto ; try omega ]
  end.

  Ltac inode_bounds := eauto; try list2mem_bound; repeat inode_bounds'; eauto.

  Hint Extern 0 (okToUnify (rep' _ _) (rep' _ _)) => constructor : okToUnify.

  Theorem igetlen_ok : forall lxp xp inum,
    {< F A mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = $ (length (IBlocks ino)) ]]
    CRASH  LOG.log_intact lxp mbase
    >} igetlen lxp xp inum.
  Proof.
    unfold igetlen, rep.
    hoare.
    list2mem_ptsto_cancel; inode_bounds.

    rewrite_list2mem_pred.
    destruct_listmatch.
    subst; apply wordToNat_inj.
    erewrite wordToNat_natToWord_bound; eauto.
    rewrite H13; auto.
  Qed.

  Theorem iget_ok : forall lxp xp inum off,
    {< F A B mbase m ilist ino a,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ (B * off |-> a)%pred (list2mem (IBlocks ino)) ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) * [[ r = a ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp inum off.
  Proof.
    unfold iget, rep.
    hoare.
    list2mem_ptsto_cancel; inode_bounds.

    repeat rewrite_list2mem_pred.
    destruct_listmatch.
    unfold sel; subst.
    rewrite H16.
    rewrite selN_firstn; inode_bounds.
  Qed.


  Theorem iput_ok : forall lxp xp inum off a,
    {< F A B mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ (B * off |->?)%pred (list2mem (IBlocks ino)) ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m' ilist' ino',
            LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp ilist')%pred m' ]] *
            [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
            [[ (B * off |-> a)%pred (list2mem (IBlocks ino')) ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp inum off a.
  Proof.
    unfold iput, rep.
    step.
    list2mem_ptsto_cancel; inode_bounds.
    step.
    list2mem_ptsto_cancel; inode_bounds.

    destruct r_; destruct p3; simpl; intuition.
    rewrite length_upd.
    setoid_rewrite H9; unfold sel.
    eapply inode_blocks_length with (m := m0); inode_bounds.
    pred_apply; cancel.
    rewrite Forall_forall in *; intuition.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.
    apply pimpl_or_r; left; cancel.
    apply pimpl_or_r; right; cancel.

    instantiate (a1 := Build_inode(upd (IBlocks i) off a)).
    2: eapply list2mem_upd; eauto.
    2: eapply list2mem_upd; eauto.


    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.

    unfold upd.
    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    unfold sel, upd; unfold inode_match; intros.
    simpl; autorewrite with core.
    cancel.
    rewrite updN_firstn_comm; inode_bounds.
    f_equal; auto.
  Qed.


  (* small helpers *)
  Lemma le_minus_one_lt : forall a b,
    a > 0 -> a <= b -> a - 1 < b.
  Proof.
    intros; omega.
  Qed.

  Lemma S_minus_one : forall n,
    n > 0 -> S (n - 1) = n.
  Proof.
    intros; omega.
  Qed.

  Lemma gt_0_wneq_0: forall (n : addr),
    (wordToNat n > 0)%nat -> n <> $0.
  Proof.
    intros.
    apply word_neq.
    ring_simplify (n ^- $0).
    destruct (weq n $0); auto; subst.
    rewrite roundTrip_0 in H; intuition.
  Qed.


  Theorem igrow_ok : forall lxp xp inum a,
    {< F A B mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ length (IBlocks ino) < blocks_per_inode ]] *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[  B (list2mem (IBlocks ino)) ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m' ilist' ino',
            LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp ilist')%pred m' ]] *
            [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
            [[ (B * $ (length (IBlocks ino)) |-> a)%pred (list2mem (IBlocks ino')) ]])
    CRASH  LOG.log_intact lxp mbase
    >} igrow lxp xp inum a.
  Proof.
    unfold igrow, rep.
    hoare.
    list2mem_ptsto_cancel; inode_bounds.
    list2mem_ptsto_cancel; inode_bounds.

    destruct r_; destruct p2; simpl; intuition.
    rewrite length_upd.
    setoid_rewrite H10; unfold sel.
    eapply inode_blocks_length with (m := m0); inode_bounds.
    pred_apply; cancel.
    rewrite Forall_forall in *; intuition.

    apply pimpl_or_r; right; cancel.

    instantiate (a1 := Build_inode ((IBlocks i) ++ [a])).
    2: eapply list2mem_upd; eauto.
    2: eapply list2mem_app; eauto.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.

    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    unfold sel, upd; unfold inode_match; intros.
    simpl; autorewrite with core.
    cancel.

    (* omega doesn't work well *)
    rewrite app_length; simpl.
    erewrite wordToNat_plusone with (w' := $ blocks_per_inode).
    rewrite Nat.add_1_r; auto.
    apply lt_wlt; rewrite <- H15; auto.

    erewrite wordToNat_plusone with (w' := $ blocks_per_inode).
    rewrite <- H15; rewrite lt_le_S; auto.
    apply lt_wlt; rewrite <- H15; auto.

    rewrite app_length; simpl.
    rewrite <- H15.
    apply firstn_app_updN; auto.
    erewrite inode_blocks_length with (m := m0); inode_bounds.
    pred_apply; cancel.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.
    unfold sel; inode_bounds.
  Qed.


  Theorem ishrink_ok : forall lxp xp inum,
    {< F A B mbase m ilist ino,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (IBlocks ino) <> nil ]] *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (A * inum |-> ino)%pred (list2mem ilist) ]] *
           [[ (B * $ (length (IBlocks ino) - 1) |->? )%pred (list2mem (IBlocks ino)) ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m' ilist' ino',
            LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp ilist')%pred m' ]] *
            [[ (A * inum |-> ino')%pred (list2mem ilist') ]] *
            [[  B (list2mem (IBlocks ino')) ]])
    CRASH  LOG.log_intact lxp mbase
    >} ishrink lxp xp inum.
  Proof.
    unfold ishrink, rep.
    hoare.
    list2mem_ptsto_cancel; inode_bounds.
    list2mem_ptsto_cancel; inode_bounds.

    destruct r_; destruct p3; simpl; intuition.
    eapply inode_blocks_length' with (m := m0); inode_bounds.
    pred_apply; cancel.
    rewrite Forall_forall; auto.

    apply pimpl_or_r; right; cancel.
    instantiate (a1 := Build_inode (removelast (IBlocks i))).
    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_removelast; eauto.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.
    eapply listmatch_updN_selN; autorewrite with defaults; inode_bounds.
    unfold sel, upd; unfold inode_match; intros.
    simpl; autorewrite with core.
    cancel.

    (* omega doesn't work well *)
    rewrite length_removelast by auto.
    rewrite wordToNat_minus_one; auto.
    apply gt_0_wneq_0; rewrite <- H16.
    apply length_not_nil; auto.

    rewrite wordToNat_minus_one; auto.
    rewrite Nat.sub_1_r; apply Nat.le_le_pred; auto.
    apply gt_0_wneq_0; rewrite <- H16.
    apply length_not_nil; auto.

    unfold sel; rewrite length_removelast by auto.
    rewrite <- removelast_firstn.
    f_equal; rewrite S_minus_one; auto.
    apply length_not_nil; auto.
    erewrite inode_blocks_length with (m := m0); inode_bounds.
    pred_apply; cancel.

    repeat rewrite_list2mem_pred; inode_bounds.
    destruct_listmatch.
    unfold sel; inode_bounds.
  Qed.

  Hint Extern 1 ({{_}} progseq (igetlen _ _ _) _) => apply igetlen_ok : prog.
  Hint Extern 1 ({{_}} progseq (iget _ _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _ _) _) => apply iput_ok : prog.
  Hint Extern 1 ({{_}} progseq (igrow _ _ _ _) _) => apply igrow_ok : prog.
  Hint Extern 1 ({{_}} progseq (ishrink _ _ _) _) => apply ishrink_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.

End INODE.
