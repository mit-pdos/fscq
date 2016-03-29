Require Import Eqdep_dec Arith Omega List.
Require Import Word WordAuto Pred GenSep Rec Prog BasicProg Hoare SepAuto2 Array Log.

Set Implicit Arguments.

(**
 * A variant of array that packs multiple items into a single disk block.
 *)

Record xparams := {
  RAStart : addr;
  RALen : addr
}.

Section RECARRAY.


  Lemma concat_length : forall T (l : list (list T)),
    length (concat l) = fold_right plus 0 (map (@length _) l).
  Proof.
    induction l; auto.
    simpl; rewrite app_length; rewrite IHl; trivial.
  Qed.

  Lemma nested_selN_concat : forall t a b m l (z:t), b < m ->
    Forall (fun sl => length sl = m) l ->
    selN (selN l a nil) b z = selN (fold_right (app (A:=t)) nil l) (b + a * m) z.
  Proof.
    induction a; intros; destruct l; simpl; inversion H0.
    trivial.
    replace (b + 0) with b by omega. subst.
    rewrite selN_app1; auto.
    trivial.
    subst. remember (a * length l) as al. rewrite selN_app2 by omega.
    replace (b + (length l + al) - length l) with (b + al) by omega. subst.
    apply IHa; assumption.
  Qed.

  (** If we index into the concatenation of a list of length-[m] lists, it's
      the same as indexing into the [n % m]'th element of the [n / m]'th list *)
  Lemma nested_sel_divmod_concat : forall t l n m (z:t), m <> $0 ->
    Forall (fun sl => length sl = wordToNat m) l ->
    sel (sel l (n ^/ m) nil) (n ^% m) z = sel (fold_right (app (A:=t)) nil l) n z.
  Proof.
    intros. unfold sel. erewrite nested_selN_concat; word2nat_auto.
    rewrite Nat.mul_comm. rewrite Nat.add_comm. rewrite <- Nat.div_mod; auto.
  Qed.

  Theorem selN_list_eq' : forall A len (vs vs' : list A) default,
    length vs = len
    -> length vs' = len
    -> (forall i, i < len -> selN vs i default = selN vs' i default)
    -> vs = vs'.
  Proof.
    induction len.
    - destruct vs; destruct vs'; simpl; intros; try congruence.
    - destruct vs; destruct vs'; simpl; intros; try congruence.
      f_equal.
      apply (H1 0); omega.
      eapply IHlen; eauto.
      intros.
      apply (H1 (S i)); omega.
  Qed.

  Theorem selN_list_eq : forall A (vs vs' : list A) default,
    length vs = length vs'
    -> (forall i, i < length vs -> selN vs i default = selN vs' i default)
    -> vs = vs'.
  Proof.
    intros.
    eapply selN_list_eq'; [ apply eq_refl | auto | auto ].
  Qed.

  Theorem selN_updN_ne : forall vs n n' v, n < length vs
    -> n <> n'
    -> selN (updN vs n v) n' ($0 : valu) = selN vs n' ($0 : valu).
  Proof.
    induction vs; destruct n'; destruct n; simpl; intuition; try omega.
  Qed.

  Lemma concat_In :
    forall T ls (x : T), In x (concat ls) -> exists l, In l ls /\ In x l.
  Proof.
    induction ls.
    intros. simpl in H. inversion H.
    simpl. intros x Hi. apply in_app_or in Hi. destruct Hi.
    exists a. tauto.
    apply IHls in H. destruct H. exists x0. tauto.
  Qed.

  Set Default Proof Using "All".

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

  Definition valu_to_wreclen (v : valu) : word (Rec.len blocktype).
    rewrite blocksz_ok in v.  refine v.
  Defined.

  Definition wreclen_to_valu (v : word (Rec.len blocktype)) : valu.
    rewrite blocksz_ok. refine v.
  Defined.

  Definition rep_block (b : block) : valu := wreclen_to_valu (Rec.to_word b).
  Definition valu_to_block (v : valu) : block := Rec.of_word (valu_to_wreclen v).

  Lemma valu_wreclen_id : forall w, valu_to_wreclen (wreclen_to_valu w) = w.
  Proof.
    unfold valu_to_wreclen, wreclen_to_valu, eq_rec, eq_rec_r.
    intros.
    rewrite eq_rect_nat_double.
    rewrite <- eq_rect_eq_dec; [| apply eq_nat_dec ].
    reflexivity.
  Qed.

  Lemma rep_valu_id : forall b, Rec.well_formed b -> valu_to_block (rep_block b) = b.
  Proof.
    unfold valu_to_block, rep_block.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite valu_wreclen_id.
    apply Rec.of_to_id; assumption.
  Qed.

  Lemma wreclen_valu_id : forall v,
    wreclen_to_valu (valu_to_wreclen v) = v.
  Proof.
    unfold valu_to_wreclen, wreclen_to_valu, eq_rec, eq_rec_r.
    intros.
    rewrite eq_rect_nat_double.
    rewrite <- eq_rect_eq_dec; [| apply eq_nat_dec ].
    reflexivity.
  Qed.

  Lemma valu_rep_id : forall v,
    rep_block (valu_to_block v) = v.
  Proof.
    unfold valu_to_block, rep_block.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Rec.to_of_id.
    rewrite wreclen_valu_id; auto.
  Qed.

  Definition array_item_pairs (xp : xparams) (vs : list block) : pred :=
    ([[ length vs = wordToNat (RALen xp) ]] *
     [[ Forall Rec.well_formed vs ]] *
     array (RAStart xp) (map rep_block vs) $1)%pred.

  Definition array_item (xp : xparams) (vs : list item) :=
    (exists vs_nested, array_item_pairs xp vs_nested *
     [[ vs = concat vs_nested ]])%pred.

  Theorem array_item_well_formed :
    forall xp vs m, array_item xp vs m -> Forall Rec.well_formed vs.
  Proof.
    intros; rewrite Forall_forall; simpl; intros.
    unfold array_item, array_item_pairs in *.
    destruct H. destruct_lift H. rewrite Forall_forall in H5.
    subst. apply concat_In in H0. destruct H0.
    eapply Forall_forall; [apply H5|]; apply H0.
  Qed.

  Theorem array_item_well_formed' :
    forall xp vs, array_item xp vs =p=> [[ Forall Rec.well_formed vs ]] * array_item xp vs.
  Proof.
    intros. apply lift_impl. apply array_item_well_formed.
  Qed.

  Lemma block_length_is : forall x (vs : list block),
    Forall Rec.well_formed vs
    -> In x vs
    -> length x = # items_per_valu.
  Proof.
    intros.
    rewrite Forall_forall in H.
    apply H in H0.
    apply H0.
  Qed.

  Lemma well_formed_valu_to_block : forall v,
    Rec.well_formed (valu_to_block v).
  Proof.
    unfold blocktype, valu_to_block; intuition.
    apply Rec.of_word_length.
  Qed.

  Lemma well_formed_valu_to_block_list : forall l,
    Forall Rec.well_formed (map valu_to_block l).
  Proof.
    intros; rewrite Forall_forall; intros.
    apply in_map_iff in H. deex.
    apply well_formed_valu_to_block.
  Qed.

  Lemma fold_right_add_const : forall (vs : list block),
    Forall Rec.well_formed vs ->
    fold_right Nat.add 0 (map (length (A:=item)) vs) = length vs * #items_per_valu.
  Proof.
    induction vs; intros; simpl; auto.
    erewrite IHvs; auto.
    simpl in H.
    f_equal.
    eapply block_length_is; eauto.
    simpl; left; auto.
    rewrite Forall_forall in *.
    intros; apply H; auto.
    simpl; right; auto.
  Qed.

  Lemma selN_zero : forall idx,
    selN (Rec.of_word (valu_to_wreclen $0)) idx item_zero = item_zero.
  Proof.
    unfold valu_to_wreclen, blocktype, item_zero.
    generalize blocksz_ok; rewrite blocksz_ok; intros. simpl.
    unfold eq_rec. rewrite <- (eq_rect_eq_dec eq_nat_dec).
    generalize (wordToNat items_per_valu).
    induction idx; simpl; intros.
    + destruct n; auto.
      unfold Rec.of_word; simpl. rewrite split1_zero.
      destruct itemtype; auto.
    + destruct n; auto.
      simpl. rewrite split2_zero; simpl. eauto.
  Qed.

  Lemma init_helper : forall l m idx,
    (forall idx, idx < m * # (items_per_valu) ->
      selN (concat l) idx item_zero = item_zero)
    -> idx < (m + 1) * # (items_per_valu)
    -> m < length l
    -> Forall (fun v => length v = # (items_per_valu) /\ Forall Rec.well_formed v) l
    -> selN (concat (updN l m (valu_to_block $0))) idx item_zero = item_zero.
  Proof.
    pose proof (Rec.of_word_length blocktype (valu_to_wreclen $0)) as H'.
    destruct H'. unfold valu_to_block.

    induction l; simpl; intros.
    - auto.
    - destruct m; simpl.
      + rewrite selN_app1 by omega.
        apply selN_zero.
      + assert (length a = #items_per_valu).
        rewrite Forall_forall in H4. destruct (H4 a). constructor; auto. auto.

        destruct (lt_dec idx #items_per_valu).
        * rewrite selN_app1 by omega.
          specialize (H1 idx).
          rewrite selN_app1 in H1 by omega. apply H1. simpl.
          apply lt_plus_trans; eauto.
        * rewrite selN_app2 by omega. rewrite H5 in *.
          apply IHl.
          intros. specialize (H1 (#items_per_valu+idx0)).
          rewrite selN_app2 in H1. rewrite H5 in *. rewrite minus_plus in *.
          apply H1. simpl. omega.
          rewrite H5. omega.
          replace (S m + 1) with (S (m + 1)) in * by omega. simpl in *.
          omega.
          omega.
          inversion H4; eauto.
  Qed.

  Definition init T lxp xp mscs rx : prog T :=
    let^ (mscs) <- For i < (RALen xp)
      Ghost [ mbase F Fm ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant
        exists m' l, LOG.rep lxp F (ActiveTxn mbase m') mscs *
        [[ (Fm * array_item xp l)%pred (list2mem m') ]] *
        [[ forall idx, idx < (#i * #items_per_valu) -> selN l idx item_zero = item_zero ]] *
        [[ length l = (# (RALen xp) * #items_per_valu)%nat ]]
      OnCrash
        LOG.would_recover_old lxp F mbase
      Begin
        mscs <- LOG.write_array lxp (RAStart xp) i $1 $0 mscs;
        lrx ^(mscs)
      Rof ^(mscs);
    rx mscs.

  Theorem init_ok : forall lxp xp mscs,
    {< mbase m F Fm,
    PRE         exists a, LOG.rep lxp F (ActiveTxn mbase m) mscs *
                [[ (Fm * array (RAStart xp) a $1)%pred (list2mem m) ]] *
                [[ length a = # (RALen xp) ]] *
                [[ goodSize addrlen (# (RALen xp) * #items_per_valu) ]]
    POST RET:mscs
                exists m' l, LOG.rep lxp F (ActiveTxn mbase m') mscs *
                [[ (Fm * array_item xp l)%pred (list2mem m') ]] *
                [[ length l = (# (RALen xp) * #items_per_valu)%nat ]] *
                [[ Forall (fun i => i = item_zero) l ]]
    CRASH       LOG.would_recover_old lxp F mbase
    >} init lxp xp mscs.
  Proof.
    unfold init.
    step.

    unfold array_item, array_item_pairs. norm.
    instantiate (a := map valu_to_block l).
    rewrite map_map.
    rewrite map_ext with (g:=id).
    rewrite map_id.
    cancel.
    intros. rewrite valu_rep_id. reflexivity.

    intuition.
    rewrite map_length. auto.
    rewrite Forall_forall.
    intuition.
    apply in_map_iff in H. deex.
    pose proof (@Rec.of_word_length blocktype (valu_to_wreclen x0)) as Hlen.
    destruct Hlen. auto.
    apply in_map_iff in H. deex.
    apply well_formed_valu_to_block.

    rewrite concat_length.
    rewrite fold_right_add_const. rewrite map_length. auto.
    apply well_formed_valu_to_block_list.

    unfold array_item, array_item_pairs.
    step.
    apply wlt_lt in H. congruence.

    eapply pimpl_ok2; eauto with prog.
    cancel.
    unfold array_item, array_item_pairs; norm.
    instantiate (a := (upd l0 m0 (valu_to_block $0))).
    rewrite map_upd. rewrite valu_rep_id. cancel.
    intuition.

    rewrite length_upd. auto.
    apply Forall_upd.
    intuition.
    split; try apply well_formed_valu_to_block.

    unfold upd. apply wlt_lt in H.
    replace (# (m0 ^+ $1)) with (# (m0) + 1) in *.
    erewrite init_helper; eauto.
    rewrite <- H15 in H. auto.
    rewrite wplus_alt. unfold wplusN, wordBinN. simpl.
    rewrite wordToNat_natToWord_bound with (bound:=RALen xp); auto.
    omega.

    rewrite concat_length.
    rewrite fold_right_add_const. f_equal.
    rewrite length_upd. auto.
    apply Forall_upd.
    intuition.
    split; try apply well_formed_valu_to_block.

    apply LOG.activetxn_would_recover_old.

    eapply pimpl_ok2; eauto with prog.
    intros; norm. cancel.
    instantiate (a0 := l0). intuition.
    rewrite Forall_forall; intros.

    eapply In_nth in H0. destruct H0 as [inidx H']; destruct H' as [Hlen Hnth].
    rewrite <- Hnth. rewrite <- nth_selN_eq. apply H11. rewrite <- H10. auto.
    eauto.
  Qed.

  (** Get the [pos]'th item in the [block_ix]'th block *)
  Definition get_pair T lxp xp block_ix (pos : addr) mscs rx : prog T :=
    let^ (mscs, v) <- LOG.read_array lxp (RAStart xp) block_ix $1 mscs;
    let i := Rec.of_word (Rec.word_selN #pos (valu_to_wreclen v)) in
    rx ^(mscs, i).

  (** Update the [pos]'th item in the [block_ix]'th block to [i] *)
  Definition put_pair T lxp xp block_ix (pos : addr) (i : item) mscs rx : prog T :=
    let^ (mscs, v) <- LOG.read_array lxp (RAStart xp) block_ix $1 mscs;
    let v' := wreclen_to_valu (Rec.word_updN #pos (valu_to_wreclen v) (Rec.to_word i)) in
    mscs <- LOG.write_array lxp (RAStart xp) block_ix $1 v' mscs;
    rx mscs.

  Hint Rewrite map_length.
  Hint Rewrite seq_length.
  Hint Resolve wlt_lt.
  Hint Rewrite sel_map_seq using auto.
  Hint Rewrite rep_valu_id.


  Theorem get_pair_ok : forall lxp xp mscs block_ix pos,
    {< F F' mbase m ilistlist,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (array_item_pairs xp ilistlist * F')%pred (list2mem m) ]] *
                   [[ (block_ix < RALen xp)%word ]] *
                   [[ (pos < items_per_valu)%word ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ r = sel (sel ilistlist block_ix nil) pos item_zero ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} get_pair lxp xp block_ix pos mscs.
  Proof.
    unfold get_pair.
    unfold array_item_pairs.
    hoare.
    autorewrite with core.
    word2nat_auto.
    subst.
    erewrite sel_map.
    rewrite Rec.word_selN_equiv with (def:=item_zero).
    unfold rep_block. rewrite valu_wreclen_id. rewrite Rec.of_to_id.
    reflexivity.
    rewrite Forall_forall in *. apply H10. apply in_selN. abstract word2nat_auto.
    abstract word2nat_auto.
    abstract word2nat_auto.
    apply LOG.activetxn_would_recover_old.
  Qed.

  Local Hint Extern 0 (okToUnify (array (RAStart _) _ _) (array (RAStart _) _ _)) => constructor : okToUnify.

  Theorem put_pair_ok : forall lxp xp mscs block_ix pos i,
    {< F Fm mbase m ilistlist,
    PRE        LOG.rep lxp F (ActiveTxn mbase m) mscs *
               [[ (array_item_pairs xp ilistlist * Fm)%pred (list2mem m) ]] *
               [[ (block_ix < RALen xp)%word ]] *
               [[ (pos < items_per_valu)%word ]] *
               [[ Rec.well_formed i ]]
    POST RET:mscs
               exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
               [[ (array_item_pairs xp (upd ilistlist block_ix (upd (sel ilistlist block_ix nil) pos i)) * Fm)%pred (list2mem m') ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} put_pair lxp xp block_ix pos i mscs.
  Proof.
    unfold put_pair.
    unfold array_item_pairs.
    intros.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    autorewrite with core.
    abstract word2nat_auto.
    eapply pimpl_ok2.
    clear H2.
    eauto with prog.
    cancel.
    autorewrite with core.
    abstract word2nat_auto.

    eapply pimpl_ok2.
    auto.
    cancel.
    erewrite sel_map.
    unfold rep_block. rewrite valu_wreclen_id. rewrite Rec.word_updN_equiv.
    rewrite Rec.of_to_id.
    autorewrite with core.
    cancel.

    rewrite Forall_forall in *. apply H11.
    apply in_selN. abstract word2nat_auto.
    abstract word2nat_auto.
    abstract word2nat_auto.
    autorewrite with core. auto.
    apply Forall_upd. assumption.
    split. autorewrite with core. rewrite Forall_forall in *. apply H11.
    apply in_sel. rewrite H7. auto.
    apply Forall_upd. rewrite Forall_forall in H11. apply H11. apply in_sel. rewrite H7. auto.
    rewrite Forall_forall in *.
    auto.
    cancel.
    apply LOG.activetxn_would_recover_old.
    cancel.
    apply LOG.activetxn_would_recover_old.
  Qed.


  Hint Extern 1 ({{_}} progseq (get_pair _ _ _ _ _) _) => apply get_pair_ok : prog.
  Hint Extern 1 ({{_}} progseq (put_pair _ _ _ _ _ _) _) => apply put_pair_ok : prog.

  Definition get T lxp xp inum mscs rx : prog T :=
    let^ (mscs, i) <- get_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu) mscs;
    rx ^(mscs, i).

  Definition put T lxp xp inum i mscs rx : prog T :=
    mscs <- put_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu) i mscs;
    rx mscs.

  Local Hint Extern 0 (okToUnify (array_item_pairs _ _) (array_item_pairs _ _)) => constructor : okToUnify.

  Theorem get_ok : forall lxp xp mscs inum,
    {< F F' mbase m ilist,
    PRE            LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ (F' * array_item xp ilist)%pred (list2mem m) ]] *
                   [[ (inum < RALen xp ^* items_per_valu)%word ]]
    POST RET:^(mscs,r)
                   LOG.rep lxp F (ActiveTxn mbase m) mscs *
                   [[ r = sel ilist inum item_zero ]]
    CRASH          LOG.would_recover_old lxp F mbase
    >} get lxp xp inum mscs.
  Proof.
    unfold get, array_item.
    pose proof items_per_valu_not_0.

    intros.
    eapply pimpl_ok2. eauto with prog.

    cancel.
    word2nat_auto.
    apply Nat.div_lt_upper_bound.
    abstract word2nat_auto.
    rewrite mult_comm; assumption.

    abstract word2nat_auto.
    step.
    subst.
    unfold array_item_pairs in H0. unfold rep_block in H0.
    destruct_lift H0.
    apply nested_sel_divmod_concat; auto.
    eapply Forall_impl; [ | apply H9 ].
    intro a. simpl. tauto.
  Qed.


  Theorem upd_divmod : forall (l : list block) (pos : addr) (v : item),
    Forall Rec.well_formed l
    -> Array.upd (concat l) pos v =
       concat (Array.upd l (pos ^/ items_per_valu)
         (Array.upd (sel l (pos ^/ items_per_valu) nil) (pos ^% items_per_valu) v)).
  Proof.
    intros. unfold upd. pose proof items_per_valu_not_0.
    rewrite <- updN_concat with (m := wordToNat items_per_valu).
    word2nat_auto. rewrite Nat.mul_comm. rewrite Nat.add_comm. rewrite <- Nat.div_mod.
    trivial. assumption. word2nat_auto.
    rewrite Forall_forall in *; intros; apply H; assumption.
  Qed.

  Theorem put_ok : forall lxp xp inum i mscs,
    {< F F' mbase m ilist,
    PRE        LOG.rep lxp F (ActiveTxn mbase m) mscs *
               [[ (F' * array_item xp ilist)%pred (list2mem m) ]] *
               [[ (inum < RALen xp ^* items_per_valu)%word ]] *
               [[ Rec.well_formed i ]]
    POST RET:mscs
               exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
               [[ (F' * array_item xp (upd ilist inum i))%pred (list2mem m') ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} put lxp xp inum i mscs.
  Proof.
    unfold put, array_item.
    unfold array_item_pairs.
    pose proof items_per_valu_not_0.
    step.

    unfold array_item_pairs.
    cancel.
    apply wdiv_lt_upper_bound; try rewrite wmult_comm; auto.
    apply wmod_upper_bound; auto.

    eapply pimpl_ok2.
    eauto with prog.
    intros; simpl; subst.
    unfold array_item_pairs.
    cancel.

    rewrite upd_divmod; auto.
  Qed.

End RECARRAY.

Hint Extern 1 ({{_}} progseq (init _ _ _ _ _ _) _) => apply init_ok : prog.
Hint Extern 1 ({{_}} progseq (get _ _ _ _ _ _ _) _) => apply get_ok : prog.
Hint Extern 1 ({{_}} progseq (put _ _ _ _ _ _ _ _) _) => apply put_ok : prog.


(* If two arrays are in the same spot, their contents have to be equal *)
Hint Extern 0 (okToUnify (array_item ?a ?b ?c ?xp _) (array_item ?a ?b ?c ?xp _)) =>
  unfold okToUnify; constructor : okToUnify.
