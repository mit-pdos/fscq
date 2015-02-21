Require Import Eqdep_dec Arith Omega List.
Require Import Word WordAuto Pred GenSep Rec Prog BasicProg Hoare SepAuto Array MemLog.
Require Import BFile RecArray Inode.
Require Import GenSep.
Require Import GenSepN.
Require Import ListPred.

Set Implicit Arguments.

Section RECBFILE.

  Variable itemtype : Rec.type.
  Variable items_per_valu : addr.
  Definition item := Rec.data itemtype.
  Definition item_zero := @Rec.of_word itemtype $0.
  Definition blocktype : Rec.type := Rec.ArrayF itemtype (wordToNat items_per_valu).
  Definition block := Rec.data blocktype.
  Definition block_zero := @Rec.of_word blocktype $0.
  Variable blocksz_ok : valulen = Rec.len blocktype.


  Theorem items_per_valu_not_0 : items_per_valu <> $0.
  Proof.
    intro H.
    unfold blocktype in blocksz_ok.
    rewrite H in blocksz_ok.
    simpl in blocksz_ok.
    rewrite valulen_is in blocksz_ok.
    discriminate.
  Qed.

  Theorem items_per_valu_not_0' : wordToNat items_per_valu <> 0.
  Proof.
    intros H.
    apply items_per_valu_not_0.
    apply wordToNat_inj; auto.
  Qed.

  Hint Resolve items_per_valu_not_0.
  Hint Resolve items_per_valu_not_0'.


  Definition rep_block := RecArray.rep_block blocksz_ok.
  Definition valu_to_block := RecArray.valu_to_block itemtype items_per_valu blocksz_ok.
  Definition rep_valu_id := RecArray.rep_valu_id blocksz_ok.

  (** Get the [pos]'th item in the [block_ix]'th block of inode [inum] *)
  Definition bf_get_pair T lxp ixp inum block_ix pos mscs rx : prog T :=
    let2 (mscs, v) <- BFILE.bfread lxp ixp inum block_ix mscs;
    let ib := valu_to_block v in
    let i := sel ib pos item_zero in
    rx (mscs, i).

  (** Update the [pos]'th item in the [block_ix]'th block of inode [inum] to [i] *)
  Definition bf_put_pair T lxp ixp inum block_ix pos i mscs rx : prog T :=
    let2 (mscs, v) <- BFILE.bfread lxp ixp inum block_ix mscs;
    let ib' := upd (valu_to_block v) pos i in
    let v' := rep_block ib' in
    mscs <- BFILE.bfwrite lxp ixp inum block_ix v' mscs;
    rx mscs.

  Definition array_item_pairs (vs : list block) : pred :=
    ([[ Forall Rec.well_formed vs ]] *
     arrayN 0 (map rep_block vs))%pred.

  Definition array_item_file file (vs : list item) : @pred _ (@weq addrlen) valuset :=
    (exists vs_nested,
     [[ length vs_nested = length (BFILE.BFData file) ]] *
     [[ array_item_pairs vs_nested (list2nmem (BFILE.BFData file)) ]] *
     [[ vs = fold_right (@app _) nil vs_nested ]])%pred.


  Definition item0_list := valu_to_block $0.

  Lemma valu_to_block_zero:
    block_zero = valu_to_block $0.
  Proof.
    unfold block_zero, valu_to_block.
    unfold RecArray.valu_to_block, valu_to_wreclen.
    f_equal.
    rewrite blocksz_ok.
    simpl; auto.
  Qed.

  Lemma item0_list_block_zero:
    block_zero = item0_list.
  Proof.
    unfold item0_list.
    apply valu_to_block_zero.
  Qed.

  Hint Resolve valu_to_block_zero.
  Hint Resolve item0_list_block_zero.

  Theorem array_item_pairs_app_eq: forall blocks fdata newfd v,
    (array_item_pairs blocks)%pred (list2nmem fdata)
    -> (array_item_pairs blocks * (length fdata) |-> v)%pred (list2nmem newfd)
    -> newfd = fdata ++ v :: nil.
  Proof.
    unfold array_item_pairs.
    intros.
    eapply list2nmem_array_app_eq.
    pred_apply; cancel.
    destruct_lift H.
    apply list2nmem_array_eq in H.
    subst; auto.
  Qed.

  Theorem array_item_pairs_app: forall blocks fdata b v,
    array_item_pairs blocks (list2nmem fdata)
    -> b = valu_to_block v
    -> Rec.well_formed b
    -> (array_item_pairs (blocks ++ b :: nil))%pred (list2nmem (fdata ++ v :: nil)).
  Proof.
    unfold array_item_pairs; intros.
    destruct_lift H.
    rewrite map_app; simpl.
    rewrite listapp_progupd.
    eapply arrayN_app_progupd with (v := v) in H as Hx.
    rewrite map_length in Hx.
    replace (length fdata) with (length blocks).
    pred_apply; cancel.
    unfold rep_block, valu_to_block.
    rewrite valu_rep_id; auto.
    apply Forall_app; auto.
    apply list2nmem_array_eq in H.
    rewrite H.
    rewrite map_length; auto.
  Qed.

  Lemma fold_right_app_init : forall A l a,
    (fold_right (app (A:=A)) nil l) ++ a  = fold_right (app (A:=A)) a l.
  Proof.
    induction l; firstorder; simpl.
    rewrite <- IHl with (a := a0).
    rewrite app_assoc; auto.
  Qed.

  Hint Rewrite map_length.
  Hint Rewrite seq_length.
  Hint Resolve wlt_lt.
  Hint Rewrite sel_map_seq using auto.
  Hint Rewrite rep_valu_id.

  Ltac rec_bounds := autorewrite with defaults core; eauto;
                     try list2nmem_bound;
                     try solve_length_eq; eauto.

  Theorem bf_get_pair_ok : forall lxp bxp ixp inum mscs block_ix pos,
    {< F A mbase m flist f ilistlist,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
           [[ array_item_pairs ilistlist (list2nmem (BFILE.BFData f)) ]] *
           [[ length ilistlist = length (BFILE.BFData f) ]] *
           [[ wordToNat block_ix < length (BFILE.BFData f) ]] *
           [[ (pos < items_per_valu)%word ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = sel (sel ilistlist block_ix nil) pos item_zero ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bf_get_pair lxp ixp inum block_ix pos mscs.
  Proof.
    unfold bf_get_pair.
    unfold array_item_pairs.
    hoare.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.

    subst.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block, sel, upd.
    erewrite selN_map by rec_bounds.
    rewrite valu_wreclen_id; rewrite Rec.of_to_id; auto.
    rewrite Forall_forall in *; apply H12.
    apply in_selN; rec_bounds.
  Qed.


  Theorem bf_put_pair_ok : forall lxp bxp ixp inum mscs block_ix pos i,
    {< F A mbase m flist f ilistlist,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
             [[ array_item_pairs ilistlist (list2nmem (BFILE.BFData f)) ]] *
             [[ length ilistlist = length (BFILE.BFData f) ]] *
             [[ wordToNat block_ix < length (BFILE.BFData f) ]] *
             [[ (pos < items_per_valu)%word ]] *
             [[ Rec.well_formed i ]]
    POST:mscs' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * # inum |-> f')%pred (list2nmem flist') ]] *
             [[ array_item_pairs (upd ilistlist block_ix 
                                     (upd (sel ilistlist block_ix nil) pos i))
                                 (list2nmem (BFILE.BFData f')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} bf_put_pair lxp ixp inum block_ix pos i mscs.
  Proof.
    unfold bf_put_pair.
    unfold array_item_pairs.
    hoare.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.
    instantiate (def := $0).

    unfold sel, upd; autorewrite with core.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block.
    rewrite arrayN_ex_updN_eq.
    rewrite selN_updN_eq by rec_bounds.
    erewrite selN_map by rec_bounds.
    rewrite valu_wreclen_id; rewrite Rec.of_to_id; auto.
    cancel.
    rewrite Forall_forall in *; apply H13.
    apply in_selN; rec_bounds.

    assert (Hx := H13).
    apply Forall_upd; auto.
    rewrite Forall_forall in Hx.
    unfold Rec.well_formed in Hx; simpl in Hx.
    unfold Rec.well_formed; simpl.
    rewrite length_upd; intuition.
    apply Hx; apply in_sel; rec_bounds.
    apply Forall_upd; auto.
    apply Hx; apply in_sel; rec_bounds.
  Qed.


  Hint Extern 1 ({{_}} progseq (bf_get_pair _ _ _ _ _ _) _) => apply bf_get_pair_ok : prog.
  Hint Extern 1 ({{_}} progseq (bf_put_pair _ _ _ _ _ _ _) _) => apply bf_put_pair_ok : prog.



  Definition bf_get T lxp ixp inum idx mscs rx : prog T :=
    let2 (mscs, i) <- bf_get_pair lxp ixp inum (idx ^/ items_per_valu)
                                               (idx ^% items_per_valu) mscs;
    rx (mscs, i).

  Definition bf_put T lxp ixp inum idx v mscs rx : prog T :=
    mscs <- bf_put_pair lxp ixp inum (idx ^/ items_per_valu)
                                     (idx ^% items_per_valu) v mscs;
    rx mscs.

  Definition bf_getlen T lxp ixp inum mscs rx : prog T :=
    let2 (mscs, len) <- BFILE.bflen lxp ixp inum mscs;
    let r := (len ^* items_per_valu)%word in
    rx (mscs, r).

  (* extending one block and put v at the first entry *)
  Definition bf_extend T lxp bxp ixp inum v mscs rx : prog T :=
    let2 (mscs1, off) <- BFILE.bflen lxp ixp inum mscs;
    let2 (mscs2, r) <- BFILE.bfgrow lxp bxp ixp inum mscs1;
    If (Bool.bool_dec r true) {
      let ib := rep_block (upd (valu_to_block $0) $0 v) in
      mscs3 <- BFILE.bfwrite lxp ixp inum off ib mscs2;
      rx (mscs3, true)
    } else {
      rx (mscs2, false)
    }.

  Lemma helper_wlt_wmult_wdiv_lt: forall sz (a b : word sz) (c : nat),
    wordToNat b <> 0 -> (a < ($ c ^* b))%word
    -> wordToNat (a ^/ b) < c.
  Proof.
    unfold wdiv, wmult, wordBin; intros.
    rewrite wordToNat_div; auto.
    apply Nat.div_lt_upper_bound; auto.
    word2nat_auto.
    rewrite Nat.mul_comm; auto.
  Qed.

  Theorem upd_divmod : forall (l : list block) (pos : addr) (v : item),
    Forall Rec.well_formed l
    -> upd (fold_right (@app _) nil l) pos v =
       fold_right (@app _) nil (upd l (pos ^/ items_per_valu)
         (upd (sel l (pos ^/ items_per_valu) nil) (pos ^% items_per_valu) v)).
  Proof.
    pose proof items_per_valu_not_0.
    intros. unfold upd.
    rewrite <- updN_concat with (m := wordToNat items_per_valu).
    word2nat_auto. rewrite Nat.mul_comm. rewrite Nat.add_comm. rewrite <- Nat.div_mod.
    trivial. assumption. word2nat_auto.
    rewrite Forall_forall in *; intros; apply H0; assumption.
  Qed.

  Hint Resolve helper_wlt_wmult_wdiv_lt.
  Hint Resolve wmod_upper_bound.
  Hint Resolve upd_divmod.

  Theorem bf_get_ok : forall lxp bxp ixp inum idx mscs,
    {< F A mbase m flist f ilist,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           array_item_file f ilist *
           [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ (idx < $ (length (BFILE.BFData f)) ^* items_per_valu)%word ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = sel ilist idx item_zero ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bf_get lxp ixp inum idx mscs.
  Proof.
    unfold bf_get, array_item_file.
    intros; eapply pimpl_ok2; eauto with prog; intros.
    norm.
    cancel.
    repeat rewrite_list2nmem_pred.
    intuition; try (eauto; pred_apply; cancel).

    step.
    subst; unfold array_item_pairs, rep_block in H9.
    destruct_lift H9.
    apply nested_sel_divmod_concat; auto.
    eapply Forall_impl; [ | apply H8 ].
    unfold Rec.well_formed.
    simpl; intuition.
  Qed.

  Theorem bf_put_ok : forall lxp bxp ixp inum idx v mscs,
    {< F A mbase m flist f ilist,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             array_item_file f ilist *
             [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (idx < $ (length (BFILE.BFData f)) ^* items_per_valu)%word ]] *
             [[ Rec.well_formed v ]]
    POST:mscs' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             array_item_file f' (upd ilist idx v) *
             [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bf_put lxp ixp inum idx v mscs.
  Proof.
    unfold bf_put, array_item_file, array_item_pairs.
    intros; eapply pimpl_ok2; eauto with prog; intros; norm.
    cancel.
    repeat rewrite_list2nmem_pred.
    unfold array_item_pairs.
    intuition; try (eauto; pred_apply; cancel).

    eapply pimpl_ok2; eauto with prog; intros.
    norm. cancel.
    subst; repeat rewrite_list2nmem_pred; subst.
    intuition; try (pred_apply; cancel).
    apply list2nmem_array_eq in H15 as Heq.
    rewrite Heq; autorewrite with core; auto.
    pred_apply; cancel.
  Qed.

  Theorem bf_extend_ok : forall lxp bxp ixp inum v mscs,
    {< F A mbase m flist f ilist,
    PRE   MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
          array_item_file f ilist *
          [[ (F * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ Rec.well_formed v ]]
    POST: (mscs', r) exists m', MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
          ([[ r = false ]] \/
           [[ r = true ]] * exists flist' f',
           array_item_file f' (ilist ++ (upd item0_list $0 v)) *
           [[ (F * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] )
    CRASH  MEMLOG.log_intact lxp mbase
    >} bf_extend lxp bxp ixp inum v mscs.
  Proof.
    unfold bf_extend, array_item_file.
    step.
    step.
    step; [ step | step | | step ].
    eapply pimpl_ok2; eauto with prog; intros.
    erewrite wordToNat_natToWord_bound.
    cancel.
    step.
    eapply pimpl_or_r; right.
    norm; [ cancel | intuition ].
    4: eauto.
    4: eauto.

    instantiate (a7 := l1 ++ (upd item0_list $0 v) :: nil).
    erewrite array_item_pairs_app_eq with (newfd := BFILE.BFData b4); eauto.
    repeat rewrite app_length; rec_bounds.
    erewrite array_item_pairs_app_eq with (newfd := BFILE.BFData b4); eauto.
    apply array_item_pairs_app; auto.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block.
    rewrite valu_wreclen_id.
    rewrite Rec.of_to_id.
    f_equal.
    admit. (* well-formed *)
    admit.

    rewrite fold_right_app; simpl; rewrite app_nil_r.
    rewrite fold_right_app_init; f_equal; auto.
    cancel.
    repeat rewrite_list2nmem_pred.
    eapply BFILE.bfdata_bound'; eauto.

    Grab Existential Variables.
    exact $0.
    exact emp.
    exact BFILE.bfile0.
    exact emp.
    exact nil.
    exact emp.
    exact bxp.
  Qed.




End RECBFILE.

Hint Extern 1 ({{_}} progseq (bf_get _ _ _ _ _ _ _ _) _) => apply bf_get_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_put _ _ _ _ _ _ _ _ _) _) => apply bf_put_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_extend _ _ _ _ _ _ _ _) _) => apply bf_extend_ok : prog.

(* Two BFileRec arrays should always be equal *)
Hint Extern 0 (okToUnify (array_item_file ?a ?b ?c ?d _) (array_item_file ?a ?b ?c ?d _)) =>
  unfold okToUnify; constructor : okToUnify.
