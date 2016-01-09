Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import Array.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import AsyncDisk.

Import ListNotations.

Set Implicit Arguments.


(* RecArray on raw, async disk *)

Module Type RASig.

  Parameter xparams : Type.
  Parameter RAStart : xparams -> addr.
  Parameter RALen   : xparams -> addr.

  Parameter itemtype : Rec.type.
  Parameter items_per_val : nat.
  Parameter blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).

End RASig.



Module AsyncRecArray (RA : RASig).

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

  Lemma setlen_In : forall A n l (a def : A),
    In a (setlen l n def)
    -> a = def \/ In a l.
  Proof.
    unfold setlen; intros.
    destruct (le_dec n (length l)).
    right.
    rewrite repeat_is_nil in H by omega; rewrite app_nil_r in H.
    eapply in_firstn_in; eauto.
    apply in_app_or in H; destruct H.
    right. eapply in_firstn_in; eauto.
    left. eapply repeat_spec; eauto.
  Qed.


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

  Lemma wlt_nat2word_word2nat_lt : forall sz (w : word sz) n,
    (w < $ n)%word -> # w < n.
  Proof.
    intros; word2nat_simpl; auto.
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

  Lemma roundup_min_r : forall a b,
    b > 0 -> Nat.min ((divup a b) * b ) a = a.
  Proof.
    intros.
    apply Nat.min_r.
    apply roundup_ge; auto.
  Qed.
  Hint Rewrite roundup_min_r.

  Lemma goodSize_sub : forall sz n a,
    goodSize sz n -> goodSize sz (n - a).
  Proof.
    intros; eapply goodSize_trans with (n2 := n); eauto; omega.
  Qed.

  (** prevent eauto from unifying length ?a = length ?b *)
  Definition eqlen A B (a : list A) (b : list B) := length a = length b.
  Definition xparams_ok xp := goodSize addrlen ((RALen xp) * items_per_val).

  Lemma eqlen_nil : forall A B (a : list A),
    eqlen a (@nil B) -> a = nil.
  Proof.
    unfold eqlen; simpl; intros.
    apply length_nil; auto.
  Qed.


  Definition itemlist := list item.

  (** rep invariant *)
  Inductive state : Type :=
  | Synced : itemlist -> state
  | Unsync : itemlist -> state
  .

  Definition ipack items := map block2val (list_chunk items items_per_val item0).

  Definition iunpack (r : itemlist) (v : valu) : itemlist :=
    r ++ (val2block v).

  Definition vs_unique (vs : valuset) := snd vs = nil \/ snd vs = [ fst vs ].

  Definition tolist A (v : A) := [ v ].

  Definition nils n := @repeat (list valu) nil n.

  Definition items_valid xp start (items : itemlist) :=
    xparams_ok xp /\  start <= (RALen xp) /\
    Forall Rec.well_formed items /\
    length items <= (RALen xp - start) * items_per_val.

  Definition rep_common xp start items vl (vsl : list (list valu)) :=
    items_valid xp start items /\
    vl = ipack items /\ eqlen vl vsl.

  Definition synced_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl /\
        vsl = nils (length vl) ]] *
    arrayN ((RAStart xp ) + start) (combine vl vsl))%pred.

  Definition unsync_array xp start items :=
    (exists vl vsl, [[ rep_common xp start items vl vsl ]] *
    arrayN ((RAStart xp ) + start) (combine vl vsl))%pred.

  Definition array_rep xp start (st : state) :=
   (match st with
    | Synced items => synced_array xp start items
    | Unsync items => unsync_array xp start items
    end)%pred.

  Definition avail_rep xp start nr : rawpred :=
    (exists vsl, [[ length vsl = nr ]] *
     arrayN ((RAStart xp) + start) vsl)%pred.

  Local Hint Extern 0 (okToUnify (arrayN (RAStart ?a) _ _) (arrayN (RAStart ?a) _ _)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (arrayN (RAStart ?b + ?a) _ _) (arrayN (RAStart ?b + ?a) _ _)) 
    => constructor : okToUnify.

  Definition nr_blocks st :=
    match st with
    | Synced l => (divup (length l) items_per_val)
    | Unsync l => (divup (length l) items_per_val)
    end.

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

  Lemma synced_array_is : forall xp start items,
    synced_array xp start items =p=>
    arrayN ((RAStart xp) + start) (combine (ipack items) (nils (length (ipack items)))).
  Proof.
    unfold synced_array, rep_common; cancel; subst; auto.
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

  Lemma map_fst_combine : forall A B (a : list A) (b : list B),
    length a = length b ->
    map fst (combine a b) = a.
  Proof.
    induction a; destruct b; simpl; auto; intros.
    inversion H.
    rewrite IHa; auto.
  Qed.

  Lemma ipack_nil : ipack nil = nil.
  Proof.
    unfold ipack.
    rewrite list_chunk_nil; auto.
  Qed.

  Lemma divup_same : forall x,
    x <> 0 -> divup x x = 1.
  Proof.
    intros; erewrite <- divup_mul; eauto.
    rewrite Nat.mul_1_l; auto.
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

  Lemma array_rep_sync_nil : forall xp a l,
    array_rep xp a (Synced l) =p=> array_rep xp a (Synced nil) * array_rep xp a (Synced l).
  Proof.
    unfold array_rep, synced_array, rep_common, eqlen; intros.
    cancel; subst; repeat setoid_rewrite ipack_nil; simpl; auto;
    unfold items_valid in *; intuition.
    cancel.
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

  Hint Rewrite list_chunk_nil ipack_nil.
  Hint Rewrite Nat.add_0_r Nat.add_0_l.
  Hint Rewrite synced_array_is.
  Hint Rewrite combine_length nils_length : lists.
  Hint Rewrite ipack_length divup_mul.

  Ltac rewrite_ignore H :=
    match type of H with
    | forall _, corr2 _ _ => idtac
    | sep_star _ _ _ => idtac
    end.

  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints core)) in H); subst_evars;
      [ try simplen_rewrite H | try autorewrite with core .. ];
    match type of H with
    | context [ length (list_chunk _ _ _) ] => rewrite block_chunk_length in H
    end).

  Ltac simplen' := repeat match goal with
    | [H : @eqlen _ ?T ?a ?b |- context [length ?a] ] => setoid_replace (length a) with (length b) by auto
    | [H : context[length ?x] |- _] => progress ( first [ is_var x | rewrite_ignore H | simplen_rewrite H ] )
    | [H : length ?l = _  |- context [ length ?l ] ] => setoid_rewrite H
    | [H : ?l = _  |- context [ ?l ] ] => setoid_rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [H : @eqlen _ ?T ?l nil |- context [?l] ] => replace l with (@nil T) by eauto
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac simplen := unfold eqlen; eauto; repeat (try subst; simpl;
    auto; simplen'; autorewrite with core lists); simpl; eauto; try omega.

  Lemma array_rep_size_ok : forall m xp start st,
    array_rep xp start st m ->
    nr_blocks st <= RALen xp - start.
  Proof.
    unfold array_rep, synced_array, unsync_array, rep_common, items_valid.
    destruct st; intros; destruct_lift H; subst;
    apply divup_le; rewrite Nat.mul_comm; eauto.
  Qed.

  Lemma array_rep_size_ok_pimpl : forall xp st,
    array_rep xp 0 st =p=>
    array_rep xp 0 st * [[ nr_blocks st <= RALen xp ]].
  Proof.
    intros; unfold pimpl; intros.
    apply array_rep_size_ok in H as H1.
    pred_apply; cancel.
  Qed.

  Lemma array_rep_avail : forall xp start st,
    array_rep xp start st =p=>
    avail_rep xp start (nr_blocks st).
  Proof.
    unfold array_rep, avail_rep, synced_array, unsync_array, rep_common, eqlen, nr_blocks.
    intros; destruct st; cancel; subst; autorewrite with lists.
    rewrite ipack_length; auto.
    rewrite <- ipack_length.
    rewrite Nat.min_l; simplen.
  Qed.
  
  Lemma array_rep_avail_synced : forall xp start items,
    array_rep xp start (Synced items) =p=>
    avail_rep xp start (divup (length items) items_per_val).
  Proof.
    intros; apply array_rep_avail.
  Qed.

  Lemma avail_rep_split : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start nr =p=> avail_rep xp start n1 * avail_rep xp (start + n1) n2.
  Proof.
    unfold avail_rep; cancel.
    destruct (lt_dec n1 (length vsl)).
    
    erewrite arrayN_isolate with (i := n1) at 1 by auto.
    setoid_rewrite arrayN_isolate with (i := 0) at 4.
    instantiate (vsl1 := (skipn n1 vsl)).
    rewrite skipn_selN, skipn_skipn.
    repeat rewrite Nat.add_0_r, Nat.add_assoc; cancel.
    rewrite Nat.add_0_r; cancel.
    rewrite skipn_length; omega.
    rewrite firstn_oob, skipn_oob by omega; cancel.
    
    destruct (lt_dec n1 (length vsl)).
    rewrite firstn_length_l; omega.
    rewrite firstn_length_r; omega.
    rewrite skipn_length; omega.
    Grab Existential Variables.
    exact ($0, @nil valu).
  Qed.
  
  Lemma avail_rep_merge : forall xp start nr n1 n2,
    n1 + n2 = nr ->
    avail_rep xp start n1 * avail_rep xp (start + n1) n2 =p=> avail_rep xp start nr.
  Proof.
    unfold avail_rep; cancel.
    instantiate (vsl1 := vsl0 ++ vsl).
    destruct (lt_dec n1 (length (vsl0 ++ vsl))).
    rewrite arrayN_app, Nat.add_assoc.
    simplen; cancel.
    rewrite arrayN_app, Nat.add_assoc.
    simplen; cancel.
    simplen.
  Qed.

  Lemma helper_add_sub : forall a b c,
    b <= c -> c <= a -> a >= b + (a - c).
  Proof.
    intros; omega.
  Qed.

  Lemma helper_add_le : forall a b nb n,
    b <= nb -> n >= a + nb -> a + b <= n.
  Proof.
    intros; omega.
  Qed.

  Lemma array_rep_synced_app : forall xp start na a b,
    length a = na * items_per_val ->
    array_rep xp start (Synced a) *
    array_rep xp (start + (divup (length a) items_per_val)) (Synced b) =p=>
    array_rep xp start (Synced (a ++ b)).
  Proof.
    simpl; unfold synced_array, rep_common, nils; cancel; subst.
    erewrite ipack_app by eauto.
    rewrite app_length, Nat.add_assoc.
    rewrite <- repeat_app.
    rewrite combine_app, arrayN_app, combine_length_eq by auto.
    repeat rewrite ipack_length.
    cancel.

    unfold items_valid, roundup in *; intuition.
    rewrite app_length.
    eapply helper_add_le; eauto.
    rewrite Nat.sub_add_distr.
    setoid_rewrite Nat.mul_sub_distr_r at 2.
    apply helper_add_sub.
    apply roundup_ge; auto.
    apply Nat.mul_le_mono_r; omega.
    
    erewrite ipack_app; eauto.
    simplen.
  Qed.


  (** read count blocks starting from the beginning *)
  Definition read_all T xp count cs rx : prog T :=
    let^ (cs, r) <- BUFCACHE.read_range (RAStart xp) count iunpack nil cs;
    rx ^(cs, r).

  Theorem read_all_ok : forall xp count cs,
    {< F d items,
    PRE            BUFCACHE.rep cs d *
                   [[ length items = (count * items_per_val)%nat /\
                      Forall Rec.well_formed items /\ xparams_ok xp ]] *
                   [[ (F * array_rep xp 0 (Synced items))%pred d ]]
    POST RET:^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * array_rep xp 0 (Synced items))%pred d ]] *
                   [[ r = items ]]
    CRASH  exists cs', BUFCACHE.rep cs' d
    >} read_all xp count cs.
  Proof.
    unfold read_all.
    step.

    simplen.
    instantiate (2 := F); cancel.
    simplen.

    step; subst.
    rewrite map_fst_combine by simplen.
    rewrite firstn_oob by simplen.
    eapply iunpack_ipack; eauto.
  Qed.

  Lemma vsupd_range_unsync_array : forall xp start items old_vs,
    items_valid xp start items ->
    eqlen old_vs (ipack items) ->
    arrayN (RAStart xp + start) (vsupd_range old_vs (ipack items))
      =p=> unsync_array xp start items.
  Proof.
    intros.
    unfold vsupd_range, unsync_array, rep_common, ipack.
    cancel.
    apply arrayN_unify.
    rewrite skipn_oob.
    rewrite app_nil_r.
    f_equal.
    simplen.
    simplen.
  Qed.

  Lemma write_aligned_length_helper : forall n l,
    n <= length (map block2val (list_chunk l items_per_val item0)) ->
    n <= divup (length l) items_per_val.
  Proof.
    intros; autorewrite with lists in *.
    erewrite <- list_chunk_length; eauto.
  Qed.
  Local Hint Resolve write_aligned_length_helper.

  (** write items from a given block index, 
      slots following the items will be cleared *)
  Definition write_aligned T xp start (items: itemlist) cs rx : prog T :=
    let chunks := list_chunk items items_per_val item0 in
    cs <- BUFCACHE.write_range ((RAStart xp) + start) (map block2val chunks) cs;
    rx cs.

  Theorem write_aligned_ok : forall xp start new cs,
    {< F d,
    PRE            BUFCACHE.rep cs d *
                   [[ items_valid xp start new ]] *
                   [[ (F * avail_rep xp start (divup (length new) items_per_val))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp start (Unsync new))%pred d' ]]
    CRASH  exists cs' d',
                   BUFCACHE.rep cs' d' *
                   [[ (F * avail_rep xp start (divup (length new) items_per_val)) % pred d' ]]
    >} write_aligned xp start new cs.
  Proof.
    unfold write_aligned, avail_rep.
    step.
    instantiate (2 := F); cancel.
    simplen.
    step.
    setoid_rewrite vsupd_range_unsync_array; auto.
    simplen.

    pimpl_crash; cancel.
    rewrite vsupd_range_length; auto.
    simplen; rewrite Nat.min_l; eauto.
  Qed.


  Lemma vssync_range_sync_array : forall xp start items count vsl,
    items_valid xp start items ->
    length items = (count * items_per_val)%nat ->
    length vsl = count ->
    arrayN (RAStart xp + start) (vssync_range (combine (ipack items) vsl) count)
      =p=> synced_array xp start items.
  Proof.
    unfold synced_array, rep_common; cancel; simplen.
    unfold vssync_range.
    rewrite skipn_oob by simplen.
    rewrite app_nil_r.
    apply arrayN_unify.
    rewrite firstn_oob by simplen.
    rewrite map_fst_combine by simplen.
    auto.
  Qed.

  Lemma helper_ipack_length_eq: forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    count = length vsl.
  Proof.
    intros.
    replace (length vsl) with (length (ipack items)) by simplen.
    rewrite ipack_length; simplen.
  Qed.

  Lemma helper_ipack_length_eq': forall (vsl : list (list valu)) count items,
    eqlen (ipack items) vsl ->
    length items = count * items_per_val ->
    length vsl = count.
  Proof.
    intros; apply eq_sym; eapply helper_ipack_length_eq; eauto.
  Qed.

  Local Hint Resolve helper_ipack_length_eq helper_ipack_length_eq'.
  Hint Rewrite ipack_length.

  Lemma vssync_range_pimpl : forall xp start items vsl m,
    length items = (length vsl) * items_per_val ->
    m <= (length vsl) ->
    arrayN (RAStart xp + start) (vssync_range (combine (ipack items) vsl) m) =p=>
    arrayN (RAStart xp + start) (combine (ipack items) (repeat [] m ++ skipn m vsl)).
  Proof.
      intros.
      unfold vssync_range, ipack.
      apply arrayN_unify.
      rewrite skipn_combine by simplen.
      rewrite <- combine_app.
      f_equal.
      rewrite <- firstn_map_comm.
      rewrite map_fst_combine by simplen.
      rewrite firstn_skipn; auto.
      simplen.
      lia.
  Qed.


  (** sync count blocks starting from start *)
  Definition sync_aligned T xp start count cs rx : prog T :=
    cs <- BUFCACHE.sync_range ((RAStart xp) + start) count cs;
    rx cs.

  Theorem sync_aligned_ok : forall xp start count cs,
    {< F d items,
    PRE            BUFCACHE.rep cs d * 
                   [[ length items = (count * items_per_val)%nat ]] *
                   [[ items_valid xp start items ]] *
                   [[ (F * array_rep xp start (Unsync items))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp start (Synced items))%pred d' ]]
    CRASH  exists cs' d', BUFCACHE.rep cs' d' *
                   [[ (F * array_rep xp start (Unsync items))%pred d' ]]
    >} sync_aligned xp start count cs.
  Proof.
    unfold sync_aligned.
    prestep. norml.
    unfold unsync_array, rep_common in *; destruct_lifts.
    cancel.

    instantiate (2 := F); cancel.
    rewrite combine_length_eq by simplen.
    rewrite ipack_length; simplen.

    step.
    apply vssync_range_sync_array; eauto.
    cancel.
    apply vssync_range_pimpl; simplen.
    replace (length vsl) with count by eauto; simplen.
    simplen; replace (length vsl) with count by eauto; omega.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_all _ _ _) _) => apply read_all_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_aligned _ _ _ _) _) => apply write_aligned_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_aligned _ _ _ _) _) => apply sync_aligned_ok : prog.

End AsyncRecArray.


Module DiskLogDescSig <: RASig.

  Definition xparams := log_xparams.
  Definition RAStart := LogDescriptor.
  Definition RALen := LogDescLen.

  Definition itemtype := Rec.WordF addrlen.
  Definition items_per_val := valulen / addrlen.

  Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
  Proof.
    unfold items_per_val; simpl.
    rewrite valulen_is.
    cbv; auto.
  Qed.

End DiskLogDescSig.


Module DiskLogDataSig <: RASig.

  Definition xparams := log_xparams.
  Definition RAStart := LogData.
  Definition RALen := LogLen.

  Definition itemtype := Rec.WordF valulen.
  Definition items_per_val := 1.

  Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
  Proof.
    unfold items_per_val; simpl.
    rewrite valulen_is.
    cbv; auto.
  Qed.

End DiskLogDataSig.


Module PaddedLog.

  Module Desc := AsyncRecArray DiskLogDescSig.
  Module Data := AsyncRecArray DiskLogDataSig.


  (************* Log header *)
  Module Hdr.
    Definition header_type := Rec.RecF ([("ndesc", Rec.WordF addrlen);
                                         ("ndata", Rec.WordF addrlen)]).
    Definition header := Rec.data header_type.
    Definition hdr := (nat * nat)%type.
    Definition mk_header (len : hdr) : header := ($ (fst len), ($ (snd len), tt)).

    Theorem hdrsz_ok : Rec.len header_type <= valulen.
    Proof.
      rewrite valulen_is. apply leb_complete. compute. trivial.
    Qed.
    Local Hint Resolve hdrsz_ok.

    Lemma plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
    Proof.
      apply le_plus_minus_r; auto.
    Qed.

    Definition hdr2val (h : header) : valu.
      set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
      rewrite plus_minus_header in r.
      refine r.
    Defined.

    Definition val2hdr (v : valu) : header.
      apply Rec.of_word.
      rewrite <- plus_minus_header in v.
      refine (split1 _ _ v).
    Defined.

    Arguments hdr2val: simpl never.

    Lemma val2hdr2val : forall h,
      val2hdr (hdr2val h) = h.
    Proof.
      unfold val2hdr, hdr2val.
      unfold eq_rec_r, eq_rec.
      intros.
      rewrite <- plus_minus_header.
      unfold zext.
      autorewrite with core; auto.
      simpl; destruct h; tauto.
    Qed.

    Arguments val2hdr: simpl never.
    Opaque val2hdr.  (* for some reason "simpl never" doesn't work *)


    Definition xparams := log_xparams.
    Definition LAHdr := LogHeader.

    Inductive state : Type :=
    | Synced : hdr -> state
    | Unsync : hdr -> hdr -> state
    .

    Definition state_goodSize st :=
      match st with
      | Synced n => goodSize addrlen (fst n) /\ goodSize addrlen (snd n)
      | Unsync n o => goodSize addrlen (fst n) /\ goodSize addrlen (snd n) /\
                      goodSize addrlen (fst o) /\ goodSize addrlen (snd o)
      end.

    Definition rep xp state : @rawpred :=
      ([[ state_goodSize state ]] *
      match state with
      | Synced n =>
         (LAHdr xp) |-> (hdr2val (mk_header n), nil)
      | Unsync n o =>
         (LAHdr xp) |-> (hdr2val (mk_header n), [hdr2val (mk_header o)])
      end)%pred.

    Definition read T xp cs rx : prog T := Eval compute_rec in
      let^ (cs, v) <- BUFCACHE.read (LAHdr xp) cs;
      rx ^(cs, (# ((val2hdr v) :-> "ndesc"), # ((val2hdr v) :-> "ndata"))).

    Definition write T xp n cs rx : prog T :=
      cs <- BUFCACHE.write (LAHdr xp) (hdr2val (mk_header n)) cs;
      rx cs.

    Definition sync T xp cs rx : prog T :=
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      rx cs.

    Local Hint Unfold rep state_goodSize : hoare_unfold.

    Theorem write_ok : forall xp n cs,
    {< F d old,
    PRE            BUFCACHE.rep cs d *
                   [[ goodSize addrlen (fst n) /\ goodSize addrlen (snd n) ]] *
                   [[ (F * rep xp (Synced old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Unsync n old))%pred d' ]]
    CRASH  exists cs', BUFCACHE.rep cs' d
           \/ exists d', BUFCACHE.rep cs' d' * [[ (F * rep xp (Unsync n old))%pred d' ]]
    >} write xp n cs.
    Proof.
      unfold write.
      hoare.
      repeat cancel.
    Qed.

    Theorem read_ok : forall xp cs,
    {< F d n,
    PRE            BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]]
    POST RET: ^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * rep xp (Synced n))%pred d ]] *
                   [[ r = n ]]
    CRASH exists cs', BUFCACHE.rep cs' d
    >} read xp cs.
    Proof.
      unfold read.
      hoare.
      subst; rewrite val2hdr2val; simpl.
      unfold mk_header, Rec.recget'; simpl.
      repeat rewrite wordToNat_natToWord_idempotent'; auto.
      destruct n; auto.
    Qed.

    Theorem sync_ok : forall xp cs,
    {< F d n,
    PRE            BUFCACHE.rep cs d * exists old,
                   [[ (F * rep xp (Unsync n old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * rep xp (Synced n))%pred d' ]]
    CRASH  exists cs', BUFCACHE.rep cs' d
           \/ exists d', BUFCACHE.rep cs' d' * [[ (F * rep xp (Synced n))%pred d' ]]
    >} sync xp cs.
    Proof.
      unfold sync.
      hoare.
      repeat cancel.
    Qed.

    Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
    Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
    Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

  End Hdr.


  (****************** Log contents and states *)

  Definition entry := (addr * valu)%type.
  Definition contents := list entry.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (l: contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated (old: contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ExtendedUnsync (old: contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | Extended (old: contents) (new: contents).

  Definition ent_addr (e : entry) := addr2w (fst e).
  Definition ent_valu (e : entry) := snd e.

  Definition ndesc_log (log : contents) := (divup (length log) DiskLogDescSig.items_per_val).

  Fixpoint log_nonzero (log : contents) : list entry :=
    match log with
    | (0, _) :: rest => log_nonzero rest
    | e :: rest => e :: log_nonzero rest
    | nil => nil
    end.

  Definition vals_nonzero (log : contents) := map ent_valu (log_nonzero log).

  Fixpoint nonzero_addrs (al : list addr) : nat :=
    match al with
    | 0 :: rest => nonzero_addrs rest
    | e :: rest => S (nonzero_addrs rest)
    | nil => 0
    end.

  Fixpoint combine_nonzero (al : list addr) (vl : list valu) : contents :=
    match al, vl with
    | 0 :: al', v :: vl' => combine_nonzero al' vl
    | a :: al', v :: vl' => (a, v) :: (combine_nonzero al' vl')
    | _, _ => nil
    end.

  Definition ndata_log (log : contents) := nonzero_addrs (map fst log) .

  Definition addr_valid (e : entry) := goodSize addrlen (fst e).

  Definition rep_contents xp (log : contents) : rawpred :=
    ( [[ Forall addr_valid log ]] *
     Desc.array_rep xp 0 (Desc.Synced (map ent_addr log)) *
     Data.array_rep xp 0 (Data.Synced (vals_nonzero log)) *
     Desc.avail_rep xp (ndesc_log log) (LogDescLen xp - (ndesc_log log)) *
     Data.avail_rep xp (ndata_log log) (LogLen xp - (ndata_log log))
     )%pred.

  Definition rep_inner xp (st : state) : rawpred :=
  (match st with
  | Synced l =>
       Hdr.rep xp (Hdr.Synced (ndesc_log l, ndata_log l)) *
       rep_contents xp l

  | Truncated old =>
       Hdr.rep xp (Hdr.Unsync (0, 0) (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | ExtendedUnsync old =>
       Hdr.rep xp (Hdr.Synced (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | Extended old new =>
       Hdr.rep xp (Hdr.Unsync (ndesc_log old + ndesc_log new, ndata_log old + ndata_log new)
                              (ndesc_log old, ndata_log old)) *
       rep_contents xp old
  end)%pred.

  Definition xparams_ok xp := 
    Desc.xparams_ok xp /\ Data.xparams_ok xp.

  Definition rep xp F st cs := (exists d,
    BUFCACHE.rep cs d * [[ xparams_ok xp ]] *
    [[ (F * rep_inner xp st)%pred d ]])%pred.


  Local Hint Unfold rep rep_inner rep_contents xparams_ok: hoare_unfold.

  Definition read T xp cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    let^ (cs, wal) <- Desc.read_all xp ndesc cs;
    let al := map (@wordToNat addrlen) wal in
    let^ (cs, vl) <- Data.read_all xp ndata cs;
    rx ^(cs, combine_nonzero al vl).

  (* this is an evil hint *)
  Remove Hints Forall_nil.

  Lemma Forall_True : forall A (l : list A),
    Forall (fun _ : A => True) l.
  Proof.
    intros; rewrite Forall_forall; auto.
  Qed.
  Hint Resolve Forall_True.

  Lemma combine_nonzero_ok : forall l,
    combine_nonzero (map fst l) (vals_nonzero l) = log_nonzero l.
  Proof.
    unfold vals_nonzero.
    induction l; intros; simpl; auto.
    destruct a, n; simpl.
    case_eq (map ent_valu (log_nonzero l)); intros; simpl.
    apply map_eq_nil in H; auto.
    rewrite <- H; auto.
    rewrite IHl; auto.
  Qed.

  Definition padded_addr (al : list addr) :=
    setlen al (roundup (length al) DiskLogDescSig.items_per_val) 0.

  Definition padded_log (log : contents) :=
    setlen log (roundup (length log) DiskLogDescSig.items_per_val) (0, $0).

  Lemma combine_nonzero_nil : forall a,
    combine_nonzero a nil = nil.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.
  Local Hint Resolve combine_nonzero_nil.

  Lemma combine_nonzero_app_zero : forall a b,
    combine_nonzero (a ++ [0]) b = combine_nonzero a b.
  Proof.
    induction a; intros; simpl; auto.
    destruct b; auto.
    destruct a, b; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma combine_nonzero_app_zeros : forall n a b,
    combine_nonzero (a ++ repeat 0 n) b = combine_nonzero a b.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply combine_nonzero_app_zero.
  Qed.

  Local Hint Resolve roundup_ge Desc.items_per_val_gt_0.

  Lemma combine_nonzero_padded_addr : forall a b,
    combine_nonzero (padded_addr a) b = combine_nonzero a b.
  Proof.
    unfold padded_addr, vals_nonzero.
    induction a; intros; simpl; auto.
    unfold setlen, roundup; simpl.
    rewrite divup_0; simpl; auto.

    unfold setlen, roundup; simpl.
    destruct a, b; simpl; auto;
    rewrite firstn_oob; simpl; auto;
    rewrite combine_nonzero_app_zeros; auto.
  Qed.

  Lemma map_fst_repeat : forall A B n (a : A) (b : B),
    map fst (repeat (a, b) n) = repeat a n.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.

  Lemma map_entaddr_repeat_0 : forall n b,
    map ent_addr (repeat (0, b) n) = repeat $0 n.
  Proof.
    induction n; intros; simpl; auto.
    rewrite IHn; auto.
  Qed.

  Lemma combine_nonzero_padded_log : forall l b,
    combine_nonzero (map fst (padded_log l)) b = combine_nonzero (map fst l) b.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    induction l; simpl.
    rewrite divup_0; simpl; auto.
    
    rewrite <- IHl.
    destruct a, b, n; simpl; auto;
    repeat rewrite firstn_oob; simpl; auto;
    repeat rewrite map_app;
    setoid_rewrite map_fst_repeat;
    repeat rewrite combine_nonzero_app_zeros; auto.
  Qed.

  Lemma addr_valid_padded : forall l,
    Forall addr_valid l -> Forall addr_valid (padded_log l).
  Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob; simpl; auto.
    apply Forall_append; auto.
    rewrite Forall_forall; intros.
    apply repeat_spec in H0; subst.
    unfold addr_valid; simpl.
    apply zero_lt_pow2.
  Qed.
  Local Hint Resolve addr_valid_padded.

  Lemma map_wordToNat_ent_addr : forall l,
    Forall addr_valid l ->
    (map (@wordToNat _) (map ent_addr l)) = map fst l.
  Proof.
    unfold ent_addr, addr2w.
    induction l; intros; simpl; auto.
    rewrite IHl; f_equal.
    rewrite wordToNat_natToWord_idempotent'; auto.
    apply Forall_inv in H; unfold addr_valid in H; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma combine_nonzero_padded_wordToNat : forall l,
    Forall addr_valid l ->
    combine_nonzero (map (@wordToNat _) (map ent_addr (padded_log l))) (vals_nonzero l) = log_nonzero l.
  Proof.
    intros; unfold ent_addr, addr2w.
    rewrite <- combine_nonzero_ok.
    rewrite <- combine_nonzero_padded_log.
    f_equal.
    rewrite map_wordToNat_ent_addr; auto.
  Qed.

  Lemma vals_nonzero_addrs : forall l,
    length (vals_nonzero l) = nonzero_addrs (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.

  Lemma log_nonzero_addrs : forall l,
    length (log_nonzero l) = nonzero_addrs (map fst l).
  Proof.
    induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
  Qed.

  Lemma desc_ipack_padded : forall l,
    Desc.ipack (map ent_addr l) = Desc.ipack (map ent_addr (padded_log l)).
  Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob, map_app, map_entaddr_repeat_0 by auto.
    rewrite Desc.ipack_app_item0; auto.
    rewrite map_length; auto.
  Qed.

  Local Hint Resolve combine_nonzero_padded_wordToNat.

  Lemma desc_padding_synced_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Synced (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Synced (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.synced_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H0.
     rewrite firstn_oob, map_app in H0 by auto.
     apply Desc.items_valid_app in H0; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.

  Lemma desc_padding_unsync_piff : forall xp a l,
    Desc.array_rep xp a (Desc.Unsync (map ent_addr (padded_log l)))
    <=p=> Desc.array_rep xp a (Desc.Unsync (map ent_addr l)).
  Proof.
     unfold Desc.array_rep, Desc.unsync_array, Desc.rep_common; intros.
     split; cancel; subst.
     unfold padded_log, setlen, roundup in H.
     rewrite firstn_oob, map_app in H by auto.
     apply Desc.items_valid_app in H; intuition.
     apply eq_sym; apply desc_ipack_padded.
     unfold padded_log, setlen, roundup.
     rewrite firstn_oob, map_app by auto.
     apply Desc.items_valid_app2; auto.
     autorewrite with lists; auto.
     apply desc_ipack_padded.
  Qed.

  Lemma goodSize_ndesc : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndesc_log l).
  Proof.
    intros; unfold ndesc_log.
    eapply goodSize_trans; [ apply divup_le | eauto ].
    destruct (mult_O_le (length l) DiskLogDescSig.items_per_val); auto.
    contradict H0; apply Desc.items_per_val_not_0.
  Qed.
  Local Hint Resolve goodSize_ndesc.

  Lemma padded_log_length: forall l,
    length (padded_log l) = roundup (length l) DiskLogDescSig.items_per_val.
  Proof.
    unfold padded_log, roundup; intros.
    rewrite setlen_length; auto.
  Qed.

  Lemma nonzero_addrs_app_zero : forall a,
    nonzero_addrs (a ++ [0]) = nonzero_addrs a.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; simpl; auto.
  Qed.

  Lemma nonzero_addrs_app_zeros : forall n a,
    nonzero_addrs (a ++ repeat 0 n) = nonzero_addrs a.
  Proof.
    induction n; intros; simpl.
    rewrite app_nil_r; auto.
    rewrite <- cons_nil_app.
    rewrite IHn.
    apply nonzero_addrs_app_zero.
  Qed.

  Lemma nonzero_addrs_padded_log : forall l,
    nonzero_addrs (map fst (padded_log l)) = nonzero_addrs (map fst l).
  Proof.
    unfold padded_log; induction l; simpl; auto.
    rewrite setlen_nil, repeat_is_nil; simpl; auto.
    unfold roundup; rewrite divup_0; omega.
    
    destruct a, n; simpl;
    rewrite <- IHl;
    unfold setlen, roundup;
    repeat rewrite firstn_oob, map_app by auto;
    setoid_rewrite map_fst_repeat;
    repeat rewrite nonzero_addrs_app_zeros; simpl; auto.
  Qed.

  Lemma vals_nonzero_length : forall l,
    length (vals_nonzero l) <= length l.
  Proof.
    unfold vals_nonzero; induction l; intros; simpl; auto.
    destruct a, n; simpl; auto.
    autorewrite with lists in *; omega.
  Qed.

  Lemma ndata_log_goodSize : forall l,
    goodSize addrlen (length l) -> goodSize addrlen (ndata_log l).
  Proof.
    unfold ndata_log; intros.
    rewrite <- vals_nonzero_addrs.
    eapply goodSize_trans.
    apply vals_nonzero_length; auto.
    auto.
  Qed.
  Local Hint Resolve ndata_log_goodSize.


  Arguments Desc.array_rep : simpl never.
  Arguments Data.array_rep : simpl never.
  Arguments Desc.avail_rep : simpl never.
  Arguments Data.avail_rep : simpl never.
  Arguments divup : simpl never.
  Hint Extern 0 (okToUnify (Hdr.rep _ _) (Hdr.rep _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.array_rep _ _ _) (Desc.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.array_rep _ _ _) (Data.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Desc.avail_rep _ _ _) (Desc.avail_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.avail_rep _ _ _) (Data.avail_rep _ _ _)) => constructor : okToUnify.

  Definition read_ok : forall xp cs,
    {< F l,
    PRE            rep xp F (Synced l) cs
    POST RET: ^(cs, r)
                   rep xp F (Synced l) cs *
                   [[ r = log_nonzero l ]]
    CRASH exists cs', rep xp F (Synced l) cs'
    >} read xp cs.
  Proof.
    unfold read.
    step.
    
    safestep; subst.
    instantiate (1 := map ent_addr (padded_log l)).
    rewrite map_length, padded_log_length.
    all: auto.
    rewrite desc_padding_synced_piff; cancel.

    step.
    rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DiskLogDataSig.items_per_val with 1 by (cbv; auto); omega.

    all: hoare using (subst; eauto).
    all: cancel; rewrite desc_padding_synced_piff; cancel.
  Qed.

  Lemma goodSize_0 : forall sz, goodSize sz 0.
  Proof.
    unfold goodSize; intros.
    apply zero_lt_pow2.
  Qed.

  Lemma ndesc_log_nil : ndesc_log nil = 0.
  Proof.
    unfold ndesc_log; simpl.
    rewrite divup_0; auto.
  Qed.

  Local Hint Resolve goodSize_0.


  Definition trunc T xp cs rx : prog T :=
    cs <- Hdr.write xp (0, 0) cs;
    cs <- Hdr.sync xp cs;
    rx cs.

  Local Hint Resolve Forall_nil.

  Lemma helper_sep_star_reorder : forall (a b c d : rawpred),
    a * b * c * d =p=> (c * a) * (d * b).
  Proof.
    intros; cancel.
  Qed.

  Lemma helper_add_sub_0 : forall a b,
    a <= b -> a + (b - a) + 0 = b.
  Proof.
    intros; omega.
  Qed.

  Lemma helper_trunc_ok : forall xp l,
    Hdr.rep xp (Hdr.Synced (0, 0)) *
    Data.avail_rep xp (ndata_log l) (LogLen xp - ndata_log l) *
    Desc.avail_rep xp (ndesc_log l) (LogDescLen xp - ndesc_log l) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero l)) *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr l))
    =p=>
    Hdr.rep xp (Hdr.Synced (ndesc_log [], ndata_log [])) *
    Desc.array_rep xp 0 (Desc.Synced []) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero [])) *
    Desc.avail_rep xp (ndesc_log []) (LogDescLen xp - ndesc_log []) *
    Data.avail_rep xp (ndata_log []) (LogLen xp - ndata_log []).
  Proof.
    intros.
    unfold ndesc_log, vals_nonzero; simpl; rewrite divup_0.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil; auto.
    cancel.
    unfold ndata_log; simpl; repeat rewrite Nat.sub_0_r.
    rewrite <- log_nonzero_addrs.
    rewrite Data.array_rep_size_ok_pimpl, Desc.array_rep_size_ok_pimpl.
    rewrite Data.array_rep_avail, Desc.array_rep_avail.
    simpl; rewrite divup_1; autorewrite with lists.
    cancel.
    rewrite helper_sep_star_reorder.
    rewrite Desc.avail_rep_merge by auto.
    rewrite Data.avail_rep_merge by auto.
    repeat rewrite helper_add_sub_0 by auto.
    cancel.
  Qed.

  Definition trunc_ok : forall xp cs,
    {< F l,
    PRE            rep xp F (Synced l) cs
    POST RET: cs   rep xp F (Synced nil) cs
    CRASH exists cs', 
       rep xp F (Synced l) cs' \/
       rep xp F (Truncated l) cs' \/
       rep xp F (Synced nil) cs'
    >} trunc xp cs.
  Proof.
    unfold trunc.
    step.
    step.
    step.
    apply helper_trunc_ok.

    (* crash conditions *)
    cancel.
    or_r; cancel.
    or_r; or_r; cancel.
    apply helper_trunc_ok.

    cancel.
    or_l; cancel.
    or_r; cancel.
  Qed.

  Definition loglen_valid xp ndesc ndata :=
    ndesc <= LogDescLen xp  /\ ndata <= LogLen xp.

  Definition loglen_invalid xp ndesc ndata :=
    ndesc > LogDescLen xp \/ ndata > LogLen xp.

  Theorem loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.
  Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec (LogDescLen xp) ndesc);
    destruct (lt_dec (LogLen xp) ndata); simpl; auto.
    left; intuition.
  Qed.

  Remove Hints goodSize_0.

  Definition entry_valid (ent : entry) := fst ent <> 0 /\ addr_valid ent.

  Definition entry_valid_ndata : forall l,
    Forall entry_valid l -> ndata_log l = length l.
  Proof.
    unfold ndata_log; induction l; rewrite Forall_forall; intuition.
    destruct a, n; simpl.
    exfalso; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    rewrite Forall_forall; intros.
    apply H; simpl; intuition.
  Qed.

  Lemma loglen_valid_desc_valid : forall xp old new,
    Desc.xparams_ok xp ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Desc.items_valid xp (ndesc_log old) (map ent_addr new).
  Proof.
    unfold Desc.items_valid, loglen_valid.
    intuition.
    unfold DiskLogDescSig.RALen; omega.
    autorewrite with lists; unfold DiskLogDescSig.RALen.
    apply divup_ge; auto.
    unfold ndesc_log in *; omega.
  Qed.
  Local Hint Resolve loglen_valid_desc_valid.


  Lemma loglen_valid_data_valid : forall xp old new,
    Data.xparams_ok xp ->
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    Data.items_valid xp (ndata_log old) (map ent_valu new).
  Proof.
    unfold Data.items_valid, loglen_valid.
    intuition.
    unfold DiskLogDataSig.RALen; omega.
    autorewrite with lists; unfold DiskLogDataSig.RALen.
    apply divup_ge; auto.
    rewrite divup_1; rewrite <- entry_valid_ndata by auto.
    unfold ndata_log in *; omega.
  Qed.
  Local Hint Resolve loglen_valid_data_valid.
  
  Lemma helper_loglen_desc_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndesc_log new + (LogDescLen xp - ndesc_log old - ndesc_log new) 
      = LogDescLen xp - ndesc_log old.
  Proof.
    unfold loglen_valid, ndesc_log; intros.
    omega.
  Qed.

  Lemma helper_loglen_data_valid_extend : forall xp new old,
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    ndata_log new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
  Proof.
    unfold loglen_valid, ndata_log; intros.
    omega.
  Qed.

  Lemma helper_loglen_data_valid_extend_entry_valid : forall xp new old,
    Forall entry_valid new ->
    loglen_valid xp (ndesc_log old + ndesc_log new) (ndata_log old + ndata_log new) ->
    length new + (LogLen xp - ndata_log old - ndata_log new) 
      = LogLen xp - ndata_log old.
  Proof.
    intros.
    rewrite <- entry_valid_ndata by auto.
    apply helper_loglen_data_valid_extend; auto.
  Qed.

  Lemma padded_desc_valid : forall xp st l,
    Desc.items_valid xp st (map ent_addr l)
    -> Desc.items_valid xp st (map ent_addr (padded_log l)).
  Proof.
    unfold Desc.items_valid; intuition.
    autorewrite with lists in *.
    rewrite padded_log_length; unfold roundup.
    apply Nat.mul_le_mono_pos_r.
    apply Desc.items_per_val_gt_0.
    apply divup_le; lia.
  Qed.

  Lemma mul_le_mono_helper : forall a b,
    b > 0 -> a <= a * b.
  Proof.
    intros. nia.
  Qed.

  Lemma loglen_valid_goodSize_l : forall xp a b,
    loglen_valid xp a b -> Desc.xparams_ok xp -> Data.xparams_ok xp ->
    goodSize addrlen a.
  Proof.
    unfold loglen_valid, Desc.xparams_ok, Data.xparams_ok; intuition.
    eapply goodSize_trans; eauto.
    eapply goodSize_trans.
    apply mul_le_mono_helper.
    apply Desc.items_per_val_gt_0.
    auto.
  Qed.

  Lemma loglen_valid_goodSize_r : forall xp a b,
    loglen_valid xp a b -> Desc.xparams_ok xp -> Data.xparams_ok xp ->
    goodSize addrlen b.
  Proof.
    unfold loglen_valid, Desc.xparams_ok, Data.xparams_ok; intuition.
    eapply goodSize_trans; eauto.
    eapply goodSize_trans.
    apply mul_le_mono_helper.
    apply Data.items_per_val_gt_0.
    auto.
  Qed.

  Lemma ent_valid_addr_valid : forall l,
    Forall entry_valid l -> Forall addr_valid l.
  Proof.
    intros; rewrite Forall_forall in *; intros.
    apply H; auto.
  Qed.
  Local Hint Resolve ent_valid_addr_valid.
  Local Hint Resolve Forall_append Desc.items_per_val_not_0.

  Lemma helper_add_sub : forall a b,
    a <= b -> a + (b - a) = b.
  Proof.
    intros; omega.
  Qed.

  Lemma ndesc_log_padded_app : forall a b,
    ndesc_log (padded_log a ++ b) = ndesc_log a + ndesc_log b.
  Proof.
    unfold ndesc_log, padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    repeat rewrite app_length; rewrite repeat_length; simpl.
    rewrite helper_add_sub by (apply divup_ge; auto).
    rewrite Nat.add_comm, Nat.mul_comm.
    rewrite divup_add by auto.
    omega.
  Qed.

  Lemma nonzero_addrs_app : forall a b,
    nonzero_addrs (a ++ b) = nonzero_addrs a + nonzero_addrs b.
  Proof.
    induction a; intros; simpl; auto.
    destruct a; auto.
    rewrite IHa; omega.
  Qed.

  Lemma ndata_log_padded_app : forall a b,
    ndata_log (padded_log a ++ b) = ndata_log a + ndata_log b.
  Proof.
    unfold ndata_log, padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    repeat rewrite map_app.
    rewrite repeat_map; simpl.
    rewrite nonzero_addrs_app.
    rewrite nonzero_addrs_app_zeros; auto.
  Qed.

  Lemma vals_nonzero_app : forall a b,
    vals_nonzero (a ++ b) = vals_nonzero a ++ vals_nonzero b.
  Proof.
    unfold vals_nonzero; induction a; intros; simpl; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma log_nonzero_repeat_0 : forall n,
    log_nonzero (repeat (0, $0) n) = nil.
  Proof.
    induction n; simpl; auto.
  Qed.

  Lemma log_nonzero_app : forall a b,
    log_nonzero (a ++ b) = log_nonzero a ++ log_nonzero b.
  Proof.
    induction a; simpl; intros; auto.
    destruct a, n; simpl; auto.
    rewrite IHa; auto.
  Qed.

  Lemma vals_nonzero_padded_log : forall l,
    vals_nonzero (padded_log l) = vals_nonzero l.
  Proof.
    unfold vals_nonzero, padded_log, setlen, roundup; simpl.
    induction l; intros; simpl; auto.
    rewrite firstn_oob; simpl; auto.
    rewrite log_nonzero_repeat_0; auto.

    destruct a, n.
    rewrite <- IHl.
    repeat rewrite firstn_oob; simpl; auto.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.

    repeat rewrite firstn_oob; simpl; auto.
    f_equal.
    repeat rewrite log_nonzero_app, map_app.
    repeat rewrite log_nonzero_repeat_0; auto.
    simpl; rewrite app_nil_r; auto.
  Qed.

  Lemma entry_valid_vals_nonzero : forall l,
    Forall entry_valid l ->
    log_nonzero l = l.
  Proof.
    unfold entry_valid; induction l; simpl; auto.
    destruct a, n; simpl; auto; intros.
    exfalso.
    rewrite Forall_forall in H; intuition.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma nonzero_addrs_entry_valid : forall l,
    Forall entry_valid l ->
    nonzero_addrs (map fst l) = length l.
  Proof.
    induction l; simpl; intros; auto.
    destruct a, n; simpl.
    exfalso.
    rewrite Forall_forall in H.
    apply (H (0, w)); simpl; auto.
    rewrite IHl; auto.
    eapply Forall_cons2; eauto.
  Qed.

  Lemma extend_ok_helper : forall xp old new,
    Forall entry_valid new ->
    Hdr.rep xp (Hdr.Synced (ndesc_log old + ndesc_log new, ndata_log old + ndata_log new)) *
    Data.array_rep xp (ndata_log old) (Data.Synced (map ent_valu new)) *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr old)) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero old)) *
    Desc.avail_rep xp (ndesc_log old + divup (length (map ent_addr new)) DiskLogDescSig.items_per_val)
      (LogDescLen xp - ndesc_log old - ndesc_log new) *
    Data.avail_rep xp (ndata_log old + divup (length (map ent_valu new)) DiskLogDataSig.items_per_val)
      (LogLen xp - ndata_log old - ndata_log new) *
    Desc.array_rep xp (ndesc_log old) (Desc.Synced (map ent_addr (padded_log new)))
    =p=>
    Hdr.rep xp (Hdr.Synced (ndesc_log (padded_log old ++ padded_log new),
                            ndata_log (padded_log old ++ padded_log new))) *
    Desc.array_rep xp 0 (Desc.Synced (map ent_addr (padded_log old ++ padded_log new))) *
    Data.array_rep xp 0 (Data.Synced (vals_nonzero (padded_log old ++ padded_log new))) *
    Desc.avail_rep xp (ndesc_log (padded_log old ++ padded_log new))
                      (LogDescLen xp - ndesc_log (padded_log old ++ padded_log new)) *
    Data.avail_rep xp (ndata_log (padded_log old ++ padded_log new)) 
                      (LogLen xp - ndata_log (padded_log old ++ padded_log new)).
  Proof.
    intros.
    repeat rewrite ndesc_log_padded_app, ndata_log_padded_app.
    setoid_rewrite Nat.sub_add_distr.
    unfold ndesc_log.
    rewrite divup_1.
    rewrite entry_valid_ndata with (l := new); auto.
    repeat rewrite map_length.
    rewrite map_app, vals_nonzero_app.
    rewrite <- Desc.array_rep_synced_app.
    rewrite <- Data.array_rep_synced_app.
    repeat rewrite Nat.add_0_l.
    repeat rewrite desc_padding_synced_piff.
    repeat rewrite map_length.
    repeat rewrite vals_nonzero_padded_log.
    rewrite divup_1, padded_log_length.
    unfold roundup; rewrite divup_mul; auto.
    unfold ndata_log; rewrite vals_nonzero_addrs.
    rewrite nonzero_addrs_padded_log.
    rewrite nonzero_addrs_entry_valid with (l := new); auto.
    unfold vals_nonzero; rewrite entry_valid_vals_nonzero with (l := new); auto.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_divup by auto.
    cancel.

    rewrite Nat.mul_1_r; auto.
    rewrite map_length, padded_log_length.
    unfold roundup; auto.
  Qed.

  Lemma ndesc_log_padded_log : forall l,
    ndesc_log (padded_log l) = ndesc_log l.
  Proof.
    unfold ndesc_log; intros.
    rewrite padded_log_length.
    unfold roundup; rewrite divup_divup; auto.
  Qed.

  Hint Rewrite Desc.array_rep_avail Data.array_rep_avail
     padded_log_length divup_mul divup_1 map_length
     ndesc_log_padded_log nonzero_addrs_padded_log using auto: extend_crash.
  Hint Unfold roundup ndata_log : extend_crash.

  Ltac extend_crash :=
     repeat (autorewrite with extend_crash; autounfold with extend_crash; simpl);
     setoid_rewrite <- Desc.avail_rep_merge at 3;
     [ setoid_rewrite <- Data.avail_rep_merge at 3 | ];
     [ cancel
     | apply helper_loglen_data_valid_extend_entry_valid; auto
     | apply helper_loglen_desc_valid_extend; auto ].


  Definition extend T xp log cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndesc, ndata) := nr in
    let '(nndesc, nndata) := ((ndesc_log log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;
      cs <- Desc.sync_aligned xp ndesc nndesc cs;
      cs <- Data.sync_aligned xp ndata nndata cs;
      cs <- Hdr.write xp (ndesc + nndesc, ndata + nndata) cs;
      cs <- Hdr.sync xp cs;
      rx ^(cs, true)
    } else {
      rx ^(cs, false)
    }.


  Definition extend_ok : forall xp new cs,
    {< F old,
    PRE   [[ Forall entry_valid new ]] *
          rep xp F (Synced old) cs
    POST RET: ^(cs, r)
          ([[ r = true ]] * rep xp F (Synced ((padded_log old) ++ (padded_log new))) cs) \/
          ([[ r = false ]] * rep xp F (Synced old) cs)
    CRASH exists cs',
          rep xp F (Synced old) cs' \/
          rep xp F (ExtendedUnsync old) cs' \/
          rep xp F (Extended old (padded_log new)) cs' \/
          rep xp F (Synced ((padded_log old) ++ (padded_log new))) cs'
    >} extend xp new cs.
  Proof.
    unfold extend.
    step.
    step.

    (* true case *)
    - (* write content *)
      step.
      rewrite Desc.avail_rep_split. cancel.
      autorewrite with lists; apply helper_loglen_desc_valid_extend; auto.

      step.
      rewrite Data.avail_rep_split. cancel.
      autorewrite with lists.
      rewrite divup_1; rewrite <- entry_valid_ndata by auto.
      apply helper_loglen_data_valid_extend; auto.

      (* sync content *)
      safestep.
      instantiate ( 1 := map ent_addr (padded_log new) ).
      rewrite map_length, padded_log_length; auto.
      apply padded_desc_valid.
      apply loglen_valid_desc_valid; auto.
      rewrite desc_padding_unsync_piff.
      cancel.

      step.
      autorewrite with lists.
      rewrite entry_valid_ndata, Nat.mul_1_r; auto.

      (* write header *)
      step.
      eapply loglen_valid_goodSize_l; eauto.
      eapply loglen_valid_goodSize_r; eauto.

      (* sync header *)
      step.

      (* post condition *)
      step.
      or_l; cancel.
      apply extend_ok_helper; auto.

      (* crash conditons *)
      (* after header write : Extended *)
      cancel. or_r; or_r; or_l.  cancel. extend_crash.

      (* after header sync : Synced new *)
      or_r; or_r; or_r.  cancel.
      apply extend_ok_helper; auto.

      (* before header write : ExtendedUnsync *)
      cancel. or_r; or_l. cancel. extend_crash.

      (* after sync data : Extended *)
      or_r; or_r; or_l.    cancel. extend_crash.

      (* after sync desc : ExtendedUnsync *)
      cancel. or_r; or_l.  cancel. extend_crash.

      (* after write data : ExtendedUnsync *)
      cancel. or_r; or_l.  cancel. extend_crash.

      (* after write desc : ExtendedUnsync *)
      cancel. or_r; or_l.  cancel. extend_crash.

      (* before write desc : Synced old *)
      cancel. or_l. cancel.
      rewrite Desc.avail_rep_merge. cancel.
      rewrite map_length.
      apply helper_loglen_desc_valid_extend; auto.

    (* false case *)
    - hoare.

    (* crash for the false case *)
    - cancel; hoare.
  Qed.


  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _) _) => apply extend_ok : prog.

  Lemma log_nonzero_padded_log : forall l,
    log_nonzero (padded_log l) = log_nonzero l.
  Proof.
    unfold padded_log, setlen, roundup; intros.
    rewrite firstn_oob by auto.
    rewrite log_nonzero_app.
    rewrite log_nonzero_repeat_0, app_nil_r; auto.
  Qed.

  Lemma log_nonzero_padded_app : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (padded_log l ++ padded_log new).
  Proof.
    intros.
    rewrite log_nonzero_app.
    repeat rewrite log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.

  Lemma log_nonzero_app_padded : forall l new,
    Forall entry_valid new ->
    log_nonzero l ++ new = log_nonzero (l ++ padded_log new).
  Proof.
    intros.
    rewrite log_nonzero_app, log_nonzero_padded_log.
    f_equal.
    rewrite entry_valid_vals_nonzero; auto.
  Qed.

  Theorem entry_valid_dec : forall ent,
    {entry_valid ent} + {~ entry_valid ent}.
  Proof.
    unfold entry_valid, addr_valid, goodSize; intuition.
    destruct (addr_eq_dec (fst ent) 0); destruct (lt_dec (fst ent) (pow2 addrlen)).
    right; tauto.
    right; tauto.
    left; tauto.
    right; tauto.
  Qed.

End PaddedLog.


Module DLog.

  Definition entry := (addr * valu)%type.
  Definition contents := list entry.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (l: contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated  (old: contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ExtendedUnsync (old: contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | Extended  (old: contents) (new: contents).

  Definition rep_common l padded : rawpred :=
      ([[ l = PaddedLog.log_nonzero padded /\
         length padded = roundup (length padded) DiskLogDescSig.items_per_val ]])%pred.

  Definition rep xp F st cs :=
    (match st with
    | Synced l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp F (PaddedLog.Synced padded) cs
    | Truncated l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp F (PaddedLog.Truncated padded) cs
    | ExtendedUnsync l =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp F (PaddedLog.ExtendedUnsync padded) cs
    | Extended l new =>
          exists padded, rep_common l padded *
          PaddedLog.rep xp F (PaddedLog.Extended padded (PaddedLog.padded_log new)) cs
    end)%pred.

  Local Hint Unfold rep rep_common : hoare_unfold.
  Hint Extern 0 (okToUnify (PaddedLog.rep _ _ _ _) (PaddedLog.rep _ _ _ _)) => constructor : okToUnify.

  Ltac or_r := apply pimpl_or_r; right.
  Ltac or_l := apply pimpl_or_r; left.


  Definition read T xp cs rx : prog T :=
    r <- PaddedLog.read xp cs;
    rx r.

  Definition read_ok : forall xp cs,
    {< F l,
    PRE            rep xp F (Synced l) cs
    POST RET: ^(cs, r)
                   rep xp F (Synced l) cs *
                   [[ r = l ]]
    CRASH exists cs', rep xp F (Synced l) cs'
    >} read xp cs.
  Proof.
    unfold read.
    hoare.
  Qed.

  Definition trunc T xp cs rx : prog T :=
    cs <- PaddedLog.trunc xp cs;
    rx cs.

  Definition trunc_ok : forall xp cs,
    {< F l,
    PRE            rep xp F (Synced l) cs
    POST RET: cs   rep xp F (Synced nil) cs
    CRASH exists cs', 
       rep xp F (Synced l) cs' \/
       rep xp F (Truncated l) cs' \/
       rep xp F (Synced nil) cs'
    >} trunc xp cs.
  Proof.
    unfold trunc.
    hoare.
    unfold roundup; rewrite divup_0; omega.
    (* crashes *)
    cancel.
    or_l. cancel.
    or_r; or_l. cancel.
    or_r; or_r. cancel.
    unfold roundup; rewrite divup_0; omega.
  Qed.

  Local Hint Resolve PaddedLog.Desc.items_per_val_gt_0.

  Lemma extend_length_ok' : forall l new,
    length l = roundup (length l) DiskLogDescSig.items_per_val ->
    length (l ++ PaddedLog.padded_log new)
      = roundup (length (l ++ PaddedLog.padded_log new)) DiskLogDescSig.items_per_val.
  Proof.
    intros.
    repeat rewrite app_length.
    repeat rewrite PaddedLog.padded_log_length.
    rewrite H.
    rewrite roundup_roundup_add, roundup_roundup; auto.
  Qed.

  Lemma extend_length_ok : forall l new,
    length l = roundup (length l) DiskLogDescSig.items_per_val ->
    length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)
      = roundup (length (PaddedLog.padded_log l ++ PaddedLog.padded_log new)) DiskLogDescSig.items_per_val.
  Proof.
    intros.
    apply extend_length_ok'.
    rewrite PaddedLog.padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.

  Local Hint Resolve extend_length_ok PaddedLog.log_nonzero_padded_app.

  Definition extend T xp new cs rx : prog T :=
    If (Forall_dec PaddedLog.entry_valid PaddedLog.entry_valid_dec new) {
      r <- PaddedLog.extend xp new cs;
      rx r
    } else {
      rx ^(cs, false)
    }.

  Definition extend_ok : forall xp new cs,
    {< F old,
    PRE   rep xp F (Synced old) cs
    POST RET: ^(cs, r)
          ([[ r = true ]] * rep xp F (Synced (old ++ new)) cs) \/
          ([[ r = false ]] * rep xp F (Synced old) cs)
    CRASH exists cs',
          rep xp F (Synced old) cs' \/
          rep xp F (ExtendedUnsync old) cs' \/
          rep xp F (Extended old new) cs' \/
          rep xp F (Synced (old ++ new)) cs'
    >} extend xp new cs.
  Proof.
    unfold extend.
    hoare.

    (* crashes *)
    cancel.
    or_l; cancel.
    or_r; or_l; cancel.
    or_r; or_r; or_l; cancel.
    or_r; or_r; or_r; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_}} progseq (extend _ _ _) _) => apply extend_ok : prog.

End DLog.

