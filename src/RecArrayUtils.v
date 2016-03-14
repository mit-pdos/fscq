Require Import Arith Rounding Psatz Omega Eqdep_dec List ListUtils Word Prog.
Require Import AsyncDisk Rec.
Import ListNotations.


Module Type RASig.

  Parameter xparams : Type.
  Parameter RAStart : xparams -> addr.
  Parameter RALen   : xparams -> addr.

  Parameter itemtype : Rec.type.
  Parameter items_per_val : nat.
  Parameter blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).

End RASig.



Module RADefs (RA : RASig).

  Import RA.

  Definition item := Rec.data itemtype.
  Definition itemsz := Rec.len itemtype.
  Definition item0 := @Rec.of_word itemtype $0.

  Definition blocktype : Rec.type := Rec.ArrayF itemtype items_per_val.
  Definition blocksz := Rec.len blocktype.
  Definition block := Rec.data blocktype.


  Definition val2word (v : valu) : word (blocksz).
    rewrite blocksz_ok in v; trivial.
  Defined.

  Definition word2val (w : word blocksz) : valu.
    rewrite blocksz_ok; trivial.
  Defined.

  Definition block2val (b : block) := word2val (Rec.to_word b).
  Definition val2block (v : valu) := Rec.of_word (val2word v).
  Definition block0 := val2block $0.

  Definition xparams_ok xp := goodSize addrlen ((RALen xp) * items_per_val).
  Definition itemlist := list item.

  Definition nils n := @repeat (list valu) nil n.

  Local Hint Resolve eq_nat_dec : core.

  Theorem val2word2val_id : forall w, val2word (word2val w) = w.
  Proof.
    unfold val2word, word2val, eq_rec_r; simpl; intros.
    rewrite eq_rect_nat_double.
    erewrite eq_rect_eq_dec; auto.
  Qed.

  Theorem word2val2word_id : forall v, word2val (val2word v) = v.
  Proof.
    unfold val2word, word2val, eq_rec_r; simpl; intros.
    rewrite eq_rect_nat_double.
    erewrite eq_rect_eq_dec; auto.
  Qed.

  Local Hint Resolve Rec.of_to_id Rec.to_of_id val2word2val_id word2val2word_id.
  Hint Rewrite val2word2val_id word2val2word_id Rec.of_to_id Rec.to_of_id : core.

  (** crush any small goals.  Do NOT use for big proofs! *)
  Ltac t' := intros; autorewrite with core; autorewrite with core in *;
             eauto; simpl in *; intuition; eauto.
  Ltac t := repeat t'; subst; simpl; eauto.

  Theorem val2block2val_id : forall b, 
    Rec.well_formed b -> val2block (block2val b) = b.
  Proof.
    unfold block2val, val2block; t.
  Qed.

  Theorem block2val2block_id : forall v,
    block2val (val2block v) = v.
  Proof.
    unfold block2val, val2block; t.
  Qed.

  Local Hint Resolve val2block2val_id block2val2block_id Forall_forall: core.
  Local Hint Resolve divup_mono firstn_nil.
  Hint Rewrite val2block2val_id block2val2block_id: core.
  Hint Rewrite combine_length : core.

  Theorem val2block2val_selN_id : forall bl i,
    Forall Rec.well_formed bl
    -> val2block (selN (map block2val bl) i $0) = selN bl i block0.
  Proof.
    induction bl; intros; t.
    destruct i; rewrite Forall_forall in *.
    t; apply H; intuition.
    apply IHbl; rewrite Forall_forall.
    t; apply H; intuition.
  Qed.
  Hint Rewrite val2block2val_selN_id.

  Lemma items_per_val_not_0 : items_per_val <> 0.
  Proof.
    generalize blocksz_ok.
    rewrite valulen_is.
    intros; intro.
    rewrite H0 in H.
    discriminate.
  Qed.

  Lemma items_per_val_gt_0 : items_per_val > 0.
  Proof.
    pose proof items_per_val_not_0; omega.
  Qed.

  Lemma items_per_val_gt_0' : 0 < items_per_val.
  Proof.
    pose proof items_per_val_not_0; omega.
  Qed.

  Local Hint Resolve items_per_val_not_0 items_per_val_gt_0 items_per_val_gt_0'.

  Hint Rewrite firstn_nil : core.
  Hint Rewrite setlen_nil : core.

  Theorem block0_repeat : block0 = repeat item0 items_per_val.
  Proof.
    unfold block0, item0, val2block, blocktype, val2word.
    generalize blocksz_ok.
    rewrite blocksz_ok; intros; simpl.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    generalize dependent items_per_val.
    induction n; simpl; auto; intros.
    erewrite <- IHn; t.
    unfold Rec.of_word at 1 3.
    rewrite split1_zero.
    rewrite split2_zero; auto.
  Qed.
  Hint Resolve block0_repeat.
  Hint Resolve divup_ge.


  Local Hint Resolve Rec.of_word_well_formed.
  Lemma item0_wellformed : Rec.well_formed item0.
  Proof.
    unfold item0; auto.
  Qed.
  Lemma block0_wellformed : Rec.well_formed block0.
  Proof.
    unfold block0, val2block; auto.
  Qed.
  Local Hint Resolve item0_wellformed block0_wellformed.

  Hint Rewrite setlen_length : core.

  Lemma setlen_wellformed : forall l n,
    Forall Rec.well_formed l
    -> Forall (@Rec.well_formed itemtype) (setlen l n item0).
  Proof.
    intros; rewrite Forall_forall in *; intros.
    destruct (setlen_In _ _ _ _ H0); t.
  Qed.

  Local Hint Resolve setlen_wellformed : core.
  Local Hint Resolve forall_skipn.


  (* list chunks *)

  Fixpoint list_chunk' {A} (l : list A) (sz : nat) (def : A) (nr : nat) : list (list A) :=
    match nr with
    | S n => setlen l sz def :: (list_chunk' (skipn sz l) sz def n)
    | O => []
    end.

  (** cut list l into chunks of lists of length sz, pad the tailing list with default value def *)
  Definition list_chunk {A} l sz def : list (list A) :=
    list_chunk' l sz def (divup (length l) sz).

  Lemma list_chunk'_length: forall A nr l sz (def : A),
      length (list_chunk' l sz def nr) = nr.
  Proof.
    induction nr; simpl; auto.
  Qed.
  Hint Rewrite list_chunk'_length : core.

  Lemma list_chunk_length: forall A l sz (def : A),
      length (list_chunk l sz def) = divup (length l) sz.
  Proof.
    unfold list_chunk; intros.
    apply list_chunk'_length.
  Qed.
  Hint Rewrite list_chunk_length : core.


  Theorem list_chunk'_wellformed : forall nr items,
    Forall Rec.well_formed items
    -> Forall (@Rec.well_formed blocktype) (list_chunk' items items_per_val item0 nr).
  Proof.
    induction nr; t.
    apply Forall_cons; t.
  Qed.

  Theorem list_chunk_wellformed : forall items,
    Forall Rec.well_formed items
    -> Forall (@Rec.well_formed blocktype) (list_chunk items items_per_val item0).
  Proof.
    intros; eapply list_chunk'_wellformed; eauto.
  Qed.
  Local Hint Resolve list_chunk_wellformed.


  (** specialized list_chunk_length that works better with dependent type in Rec *)
  Lemma block_chunk_length: forall l sz,
      @length block (@list_chunk item l sz item0) = divup (length l) sz.
  Proof.
    intros; apply list_chunk_length.
  Qed.
  Hint Rewrite block_chunk_length : core.

  Lemma list_chunk_nil : forall  A sz (def : A),
    list_chunk nil sz def = nil.
  Proof.
    unfold list_chunk; t.
    rewrite divup_0; t.
  Qed.

  Lemma list_chunk'_Forall_length : forall A nr l sz (i0 : A),
    Forall (fun b => length b = sz) (list_chunk' l sz i0 nr).
  Proof.
    induction nr; t.
    apply Forall_cons; t.
  Qed.

  Lemma list_chunk_In_length : forall A l sz (i0 : A) x,
    In x (list_chunk l sz i0) -> length x = sz.
  Proof.
    intros until i0; apply Forall_forall.
    unfold list_chunk.
    apply list_chunk'_Forall_length.
  Qed.

  Local Hint Resolve in_selN.
  Hint Rewrite skipn_length.

  Lemma list_chunk_selN_length : forall l i,
    length (selN (list_chunk l items_per_val item0) i block0) = items_per_val.
  Proof.
    intros.
    destruct (lt_dec i (length (list_chunk l items_per_val item0))).
    eapply list_chunk_In_length; eauto.
    rewrite selN_oob by t.
    apply block0_wellformed.
  Qed.
  Hint Rewrite list_chunk_selN_length.

  Lemma list_chunk'_spec : forall A nr i l sz (i0 : A) b0,
    i < nr ->
    selN (list_chunk' l sz i0 nr) i b0 = setlen (skipn (i * sz) l) sz i0.
  Proof.
    induction nr; t. inversion H.
    destruct i. t.
    erewrite IHnr by t.
    rewrite skipn_skipn; simpl.
    f_equal; f_equal; omega.
  Qed.

  Lemma list_chunk_spec' : forall A l i n (e0 : A) b0,
    n <> 0 -> b0 = repeat e0 n ->
    selN (list_chunk l n e0) i b0 
    = setlen (skipn (i * n) l) n e0.
  Proof.
    unfold list_chunk; intros.
    destruct (lt_dec i (divup (length l) n)).
    apply list_chunk'_spec; auto.
    rewrite selN_oob by t.
    rewrite skipn_oob; t.
  Qed.

  Lemma list_chunk_spec : forall l i,
    selN (list_chunk l items_per_val item0) i block0 
    = setlen (skipn (i * items_per_val) l) items_per_val item0.
  Proof.
    intros; apply list_chunk_spec'; eauto.
  Qed.

  Lemma list_chunk'_skipn_1: forall A n l k (e0 : A),
    list_chunk' (skipn n l) n e0 (k - 1) = skipn 1 (list_chunk' l n e0 k).
  Proof.
    induction k; intros; simpl; auto; rewrite Nat.sub_0_r; auto.
  Qed.

  Lemma list_chunk_skipn_1 : forall A n l (e0 : A),
    list_chunk (skipn n l) n e0 = skipn 1 (list_chunk l n e0).
  Proof.
    unfold list_chunk; intros.
    rewrite skipn_length.
    destruct (Nat.eq_dec n 0).
    subst; simpl; auto.
    destruct (lt_dec (length l) n).
    replace (length l - n) with 0 by omega.
    rewrite divup_0.
    apply Nat.lt_le_incl in l0; apply divup_le_1 in l0.
    destruct (Nat.eq_dec (divup (length l) n) 1).
    rewrite e.
    setoid_rewrite skipn_oob at 2; simpl; auto.
    replace (divup (length l) n) with 0 by omega.
    simpl; auto.
    rewrite divup_sub_1 by omega.
    apply list_chunk'_skipn_1.
  Qed.

  Lemma skipn_list_chunk_skipn_eq : forall A i l n (e0 : A),
    skipn i (list_chunk l n e0) = list_chunk (skipn (i * n) l) n e0.
  Proof.
    induction i; intros.
    simpl; auto.
    simpl (S i * n).
    rewrite <- skipn_skipn'.
    rewrite <- IHi; auto.
    rewrite list_chunk_skipn_1.
    rewrite skipn_skipn.
    replace (S i) with (i + 1) by omega; auto.
  Qed.

  Local Hint Resolve divup_le divup_mul_ge.

  Lemma skipn_repeat_list_chunk : forall A i l n (e0 : A) B (x : B),
    skipn i (repeat x (length (list_chunk l n e0)))
    = repeat x (length (list_chunk (skipn (i * n) l) n e0)).
  Proof.
    intros.
    destruct (Nat.eq_dec n 0).
    subst; simpl; rewrite skipn_nil; auto.
    destruct (lt_dec (length l) (n * i)); autorewrite with core.
    replace (length l - i * n) with 0 by nia.
    rewrite divup_0.
    rewrite skipn_oob; autorewrite with core; simpl; auto.
    autorewrite with lists.
    apply divup_le; nia.
    rewrite divup_sub by nia.
    rewrite skipn_repeat; auto.
    apply divup_mul_ge; omega.
  Qed.

  Local Hint Resolve skipn_list_chunk_skipn_eq list_chunk_skipn_1 skipn_repeat_list_chunk.
  Hint Rewrite app_nil_l app_nil_r firstn_length Nat.sub_diag Nat.sub_0_r: core.

  Lemma setlen_inbound : forall A n (l : list A) def,
    n <= length l ->
    setlen l n def = firstn n l.
  Proof.
    unfold setlen; intros.
    replace (n - length l) with 0 by omega; t.
  Qed.

  Lemma list_chunk'_firstn' : forall A i n l (e0 : A),
    length l >= i * n ->
    list_chunk' (firstn (i * n) l) n e0 i = list_chunk' l n e0 i.
  Proof.
    induction i; intros; simpl; auto.
    repeat rewrite setlen_inbound by (autorewrite with core lists; nia).
    rewrite firstn_firstn.
    rewrite Nat.min_l by nia.
    setoid_rewrite <- IHi at 2; autorewrite with core; try nia.
    f_equal; f_equal.
    apply skipn_firstn_comm.
  Qed.

  Lemma list_chunk'_firstn : forall A i n l (e0 : A),
    list_chunk' (firstn (i * n) l) n e0 i = list_chunk' l n e0 i.
  Proof.
    intros.
    destruct (le_lt_dec (i * n) (length l)).
    apply list_chunk'_firstn'; auto.
    rewrite firstn_oob; auto.
    nia.
  Qed.

  Lemma firstn_list_chunk' : forall A m n i l (e0 : A),
    n <= m ->
    firstn n (list_chunk' l i e0 m) = list_chunk' l i e0 n.
  Proof.
    induction m; destruct n; t.
    inversion H.
    rewrite IHm; t.
  Qed.

  Hint Rewrite divup_mul Nat.mul_0_r Nat.mul_0_l.

  Lemma list_chunk_firstn' : forall A i n l (e0 : A),
    n <> 0 -> length l >= i * n ->
    list_chunk (firstn (i * n) l) n e0 = firstn i (list_chunk l n e0).
  Proof.
    unfold list_chunk; t.
    rewrite Nat.min_l; t.
    rewrite list_chunk'_firstn.
    rewrite firstn_list_chunk'; t.
    apply divup_mul_ge; nia.
  Qed.

  Lemma list_chunk_firstn : forall A i n l (e0 : A),
    list_chunk (firstn (i * n) l) n e0 = firstn i (list_chunk l n e0).
  Proof.
    intros.
    destruct (Nat.eq_dec n 0); t. t.
    destruct (le_lt_dec (i * n) (length l)).
    apply list_chunk_firstn'; t.
    rewrite firstn_oob by nia.
    rewrite firstn_oob; t.
    apply divup_le; nia.
  Qed.

  Lemma firstn_list_chunk_app : forall l i pre,
    items_per_val + i * items_per_val < length l
    -> pre = firstn (i * items_per_val) l
    -> firstn (i * items_per_val + items_per_val) l 
       = pre ++ (selN (list_chunk l items_per_val item0) i block0).
  Proof.
    t; rewrite list_chunk_spec.
    rewrite firstn_sum_split; f_equal.
    rewrite setlen_inbound; t.
  Qed.

  Lemma firstn_setlen_firstn : forall A l m n (def : A),
    n <= m -> n <= length l -> firstn n (setlen l m def) = firstn n l.
  Proof.
    unfold setlen; intros.
    rewrite firstn_app_l.
    rewrite firstn_firstn; rewrite Nat.min_l; auto.
    rewrite firstn_length.
    apply Min.min_glb; auto.
  Qed.

  Lemma list_chunk'_app : forall A na sz a b (def : A),
    sz <> 0 ->
    length a = sz * na ->
    list_chunk' (a ++ b) sz def (na + divup (length b) sz) =
    list_chunk' a sz def na ++ list_chunk' b sz def (divup (length b) sz).
  Proof.
    induction na; t.
    replace (a ++ b) with b; auto.
    rewrite length_nil with (l := a); auto; omega.
    repeat rewrite setlen_inbound by (autorewrite with lists; nia).
    rewrite firstn_app_l by nia.
    f_equal.
    rewrite skipn_app_l by nia.
    rewrite IHna; auto.
    autorewrite with core; nia.
  Qed.


  Lemma list_chunk_app: forall A na sz a b (def : A),
    sz <> 0 ->
    length a = sz * na ->
    list_chunk (a ++ b) sz def = list_chunk a sz def ++ list_chunk b sz def.
  Proof.
    unfold list_chunk; intros.
    rewrite app_length; autorewrite with core lists.
    repeat (rewrite H0; rewrite Nat.mul_comm; rewrite divup_mul by auto).
    rewrite <- list_chunk'_app; auto.
    f_equal.
    replace (na * sz + length b) with (length b + sz * na) by lia.
    rewrite divup_add by auto; omega.
  Qed.




  (* reps *)
  Definition ipack items := map block2val (list_chunk items items_per_val item0).

  Definition iunpack (r : itemlist) (v : valu) : itemlist :=
    r ++ (val2block v).

  Definition items_valid xp start (items : itemlist) :=
    xparams_ok xp /\  start <= (RALen xp) /\
    Forall Rec.well_formed items /\
    length items <= (RALen xp - start) * items_per_val.

  Lemma well_formed_app_iff : forall A (a b : list (Rec.data A)) ,
     Forall Rec.well_formed (a ++ b)
     <-> Forall Rec.well_formed a /\ Forall Rec.well_formed b.
  Proof.
    intros; repeat (try split; rewrite Forall_forall in *; t).
    destruct (in_app_or a b x); t.
  Qed.

  Lemma items_valid_app : forall xp st a b,
    items_valid xp st (a ++ b) ->
    items_valid xp st a /\ items_valid xp st b.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.
  Qed.

  Lemma le_add_helper: forall a b c d,
    b <= d -> a + d <= c -> a + b <= c.
  Proof.
    intros; omega.
  Qed.

  Lemma le_add_le_sub : forall a b c,
    a <= c -> b <= c - a -> a + b <= c.
  Proof.
    intros. omega.
  Qed.

  Lemma items_valid_app2 : forall xp st a b,
    length b <= (roundup (length a) items_per_val - length a)
    -> items_valid xp st a
    -> Forall Rec.well_formed b
    -> items_valid xp st (a ++ b).
  Proof.
    unfold items_valid, roundup; intuition.
    pose proof (well_formed_app_iff itemtype a b); intuition.
    rewrite app_length.
    eapply le_add_helper. apply H.
    rewrite le_plus_minus_r by (apply roundup_ge; auto).
    apply mult_le_compat_r.
    apply divup_le; lia.
  Qed.

  Lemma items_valid_app3 : forall xp st a b na,
    length a = na * items_per_val ->
    items_valid xp st (a ++ b) -> items_valid xp (st + na) b.
  Proof.
    unfold items_valid; intros; split; intros;
    pose proof (well_formed_app_iff itemtype a b);
    rewrite app_length in *; intuition.

    apply le_add_le_sub; auto.
    eapply Nat.mul_le_mono_pos_r; eauto.
    rewrite <- H; omega.

    rewrite Nat.sub_add_distr.
    rewrite Nat.mul_sub_distr_r.
    apply Nat.le_add_le_sub_l.
    setoid_rewrite <- H; auto.
  Qed.


  Lemma nils_length : forall n,
    length (nils n) = n.
  Proof.
    unfold nils; intros.
    apply repeat_length.
  Qed.

  Lemma ipack_length : forall items,
    length (ipack items) = divup (length items) items_per_val.
  Proof.
    unfold ipack; intros.
    rewrite map_length.
    setoid_rewrite list_chunk_length; auto.
  Qed.

  Lemma ipack_app: forall na a b,
    length a = na * items_per_val ->
    ipack (a ++ b) = ipack a ++ ipack b.
  Proof.
    unfold ipack; intros.
    rewrite <- map_app; f_equal.
    eapply list_chunk_app; eauto.
    rewrite Nat.mul_comm; eauto.
  Qed.


  Lemma ipack_nil : ipack nil = nil.
  Proof.
    unfold ipack.
    rewrite list_chunk_nil; auto.
  Qed.

  Lemma ipack_one : forall l,
    length l = items_per_val ->
    ipack l = block2val l :: nil.
  Proof.
    unfold ipack, list_chunk; intros.
    rewrite H.
    rewrite divup_same by auto; simpl.
    rewrite setlen_inbound by omega.
    rewrite firstn_oob by omega; auto.
  Qed.

  Lemma iunpack_ipack_one : forall l init,
    Forall Rec.well_formed l ->
    length l = items_per_val ->
    fold_left iunpack (ipack l) init = init ++ l.
  Proof.
    intros; unfold iunpack.
    rewrite ipack_one by auto; simpl.
    autorewrite with core; split; auto.
  Qed.

  Lemma list_chunk'_app_def : forall A n z l k (def : A),
    list_chunk' (l ++ repeat def z) k def n = list_chunk' l k def n.
  Proof.
    induction n; intros; simpl; auto.
    destruct (le_gt_dec k (length l)).
    repeat rewrite setlen_inbound by (auto; rewrite app_length; omega).
    rewrite firstn_app_l, skipn_app_l by auto.
    rewrite IHn; auto.

    rewrite setlen_app_r by omega.
    unfold setlen at 2; rewrite firstn_oob by omega.
    rewrite setlen_repeat.
    f_equal.
    rewrite skipn_app_r_ge by omega.
    setoid_rewrite skipn_oob at 2; try omega.
    destruct (le_gt_dec (k - length l) z).
    rewrite skipn_repeat by auto.
    setoid_rewrite <- app_nil_l at 2.
    apply IHn.
    rewrite skipn_oob by (rewrite repeat_length; omega); auto.
  Qed.

  Lemma ipack_app_item0 : forall l n,
    n <= (roundup (length l) items_per_val - length l) ->
    ipack (l ++ repeat item0 n) = ipack l.
  Proof.
    unfold ipack, list_chunk; intros.
    f_equal.
    rewrite list_chunk'_app_def, app_length.
    rewrite divup_add_small; auto.
    rewrite repeat_length; auto.
  Qed.


  Lemma well_formed_firstn : forall A n (a : list (Rec.data A)), 
    Forall Rec.well_formed a
    -> Forall Rec.well_formed (firstn n a).
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H; eapply in_firstn_in; eauto.
  Qed.

  Lemma well_formed_skipn : forall A n (a : list (Rec.data A)), 
    Forall Rec.well_formed a
    -> Forall Rec.well_formed (skipn n a).
  Proof.
    intros.
    rewrite Forall_forall in *; intros.
    apply H; eapply in_skipn_in; eauto.
  Qed.

  Local Hint Resolve Forall_append well_formed_firstn well_formed_skipn.

  Lemma iunpack_ipack' : forall nr init items ,
    Forall Rec.well_formed items ->
    length items = nr * items_per_val ->
    fold_left iunpack (ipack items) init = init ++ items.
  Proof.
    induction nr; t.
    apply length_nil in H0; rewrite H0.
    rewrite ipack_nil; simpl; t.

    erewrite <- firstn_skipn with (n := items_per_val) (l := items).
    rewrite ipack_app with (na := 1).
    rewrite fold_left_app.
    rewrite IHnr; auto.
    rewrite app_assoc.
    f_equal.

    rewrite iunpack_ipack_one; auto.
    rewrite firstn_length_l; lia.
    rewrite skipn_length; nia.
    rewrite firstn_length; lia.
  Qed.

  Lemma iunpack_ipack : forall nr items,
    Forall Rec.well_formed items ->
    length items = nr * items_per_val ->
    fold_left iunpack (ipack items) [] = items.
  Proof.
    intros; eapply iunpack_ipack'; eauto.
  Qed.


End RADefs.



