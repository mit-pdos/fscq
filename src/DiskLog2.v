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
    xparams_ok xp /\  start < (RALen xp) /\
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

  Local Hint Extern 0 (okToUnify (arrayN (RAStart ?a) _ _) (arrayN (RAStart ?a) _ _)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (arrayN (RAStart ?b + ?a) _ _) (arrayN (RAStart ?b + ?a) _ _)) 
    => constructor : okToUnify.

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


  Lemma ipack_app_item0 : forall l n,
    n <= (roundup (length l) items_per_val - length l) ->
    ipack (l ++ repeat item0 n) = ipack l.
  Proof.
    unfold ipack, list_chunk; intros.
    f_equal.
    admit.
  Admitted.

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


  (** write items from a given block index, 
      slots following the items will be cleared *)
  Definition write_aligned T xp start (items: itemlist) cs rx : prog T :=
    let chunks := list_chunk items items_per_val item0 in
    cs <- BUFCACHE.write_range ((RAStart xp) + start) (map block2val chunks) cs;
    rx cs.

  Theorem write_aligned_ok : forall xp start new cs,
    {< F d,
    PRE            exists old, BUFCACHE.rep cs d *
                   [[ eqlen old new /\ items_valid xp start new ]] *
                   [[ (F * array_rep xp start (Synced old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp start (Unsync new))%pred d' ]]
    CRASH  exists cs' d' F', BUFCACHE.rep cs' d' * [[ (F * F') % pred d' ]]
    >} write_aligned xp start new cs.
  Proof.
    unfold write_aligned.
    step.

    simplen.
    instantiate (2 := F); cancel.
    simplen.

    step.
    setoid_rewrite vsupd_range_unsync_array; auto.
    simplen.
    step.
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


Module DISKLOG.

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

    Definition rep xp state : @rawpred :=
      match state with
      | Synced n =>   ((LAHdr xp) |-> (hdr2val (mk_header n), nil)) %pred
      | Unsync n o => ((LAHdr xp) |-> (hdr2val (mk_header n), [hdr2val (mk_header o)])) %pred
      end.

    Definition read T xp cs rx : prog T := Eval compute_rec in
      let^ (cs, v) <- BUFCACHE.read (LAHdr xp) cs;
      rx ^(cs, (# ((val2hdr v) :-> "ndesc"), # ((val2hdr v) :-> "ndata"))).

    Definition write T xp n cs rx : prog T :=
      cs <- BUFCACHE.write (LAHdr xp) (hdr2val (mk_header n)) cs;
      rx cs.

    Definition sync T xp cs rx : prog T :=
      cs <- BUFCACHE.sync (LAHdr xp) cs;
      rx cs.

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
    Qed.

    Theorem read_ok : forall xp cs,
    {< F d n,
    PRE            BUFCACHE.rep cs d *
                   [[ goodSize addrlen (fst n) /\ goodSize addrlen (snd n) ]] *
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
    Qed.

    Theorem sync_ok : forall xp cs,
    {< F d n,
    PRE            BUFCACHE.rep cs d * exists old,
                   [[ goodSize addrlen (fst n) /\ goodSize addrlen (snd n)  ]] *
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
     Data.array_rep xp 0 (Data.Synced (vals_nonzero log)))%pred.

  Definition rep_inner xp (st : state) : rawpred :=
  (match st with
  | Synced l =>
       [[ goodSize addrlen (length l) ]] *
       Hdr.rep xp (Hdr.Synced (ndesc_log l, ndata_log l)) *
       rep_contents xp l

  | Truncated old =>
       [[ goodSize addrlen (length old) ]] *
       Hdr.rep xp (Hdr.Unsync (0, 0) (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | ExtendedUnsync old =>
       [[ goodSize addrlen (length old) ]] *
       Hdr.rep xp (Hdr.Synced (ndesc_log old, ndata_log old)) *
       rep_contents xp old

  | Extended old new =>
       [[ goodSize addrlen (length (old ++ new)) ]] *
       Hdr.rep xp (Hdr.Unsync (ndesc_log (old ++ new), ndata_log (old ++ new))
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

  Lemma desc_ipack_padded : forall l,
    Desc.ipack (map ent_addr l) = Desc.ipack (map ent_addr (padded_log l)).
  Proof.
    unfold padded_log, setlen; intros.
    rewrite firstn_oob, map_app, map_entaddr_repeat_0 by auto.
    rewrite Desc.ipack_app_item0; auto.
    rewrite map_length; auto.
  Qed.

  Local Hint Resolve combine_nonzero_padded_wordToNat.

  Lemma desc_padding_piff : forall xp a l,
    Desc.synced_array xp a (map ent_addr (padded_log l))
    <=p=> Desc.synced_array xp a (map ent_addr l).
  Proof.
     unfold Desc.synced_array, Desc.rep_common; intros.
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
    hoare using (subst; eauto).
    all: try cancel; try (rewrite desc_padding_piff; cancel).
    rewrite map_length, padded_log_length; auto.
    rewrite vals_nonzero_addrs; unfold ndata_log.
    replace DiskLogDataSig.items_per_val with 1 by (cbv; auto); omega.
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

  Arguments Desc.array_rep : simpl never.
  Arguments Data.array_rep : simpl never.
  Hint Extern 0 (okToUnify (Desc.array_rep _ _ _) (Desc.array_rep _ _ _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (Data.array_rep _ _ _) (Data.array_rep _ _ _)) => constructor : okToUnify.
  Local Hint Resolve Forall_nil.

  Definition trunc_ok : forall xp cs,
    {< F l,
    PRE            rep xp F (Synced l) cs
    POST RET: cs   exists F',
                   rep xp (F * F') (Synced nil) cs
    CRASH exists cs', 
       rep xp F (Synced l) cs' \/
       rep xp F (Truncated l) cs' \/
       exists F', rep xp (F * F') (Synced nil) cs'
    >} trunc xp cs.
  Proof.
    unfold trunc.
    step.
    step.
    step.
    unfold ndesc_log, vals_nonzero; simpl; rewrite divup_0.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil; auto.
    cancel.
    cancel.

    (* crash conditions *)
    apply pimpl_or_r; right; cancel.
    apply pimpl_or_r; right.
    apply pimpl_or_r; right. cancel.
    rewrite Desc.array_rep_sync_nil, Data.array_rep_sync_nil, ndesc_log_nil; auto.
    cancel.
    cancel.
    apply pimpl_or_r; left; cancel.
    apply pimpl_or_r; right; cancel.
  Qed.

  Definition loglen_valid xp ndesc ndata :=
    LogDescLen xp <= ndesc /\ LogLen xp <= ndata.

  Definition loglen_invalid xp ndesc ndata :=
    LogDescLen xp > ndesc \/ LogLen xp > ndata.

  Theorem loglen_valid_dec xp ndesc ndata :
    {loglen_valid xp ndesc ndata} + {loglen_invalid xp ndesc ndata }.
  Proof.
    unfold loglen_valid, loglen_invalid.
    destruct (lt_dec ndesc (LogDescLen xp));
    destruct (lt_dec ndata (LogLen xp)); simpl; auto.
    left; intuition.
  Qed.

  Definition extend T xp log cs rx : prog T :=
    let^ (cs, nr) <- Hdr.read xp cs;
    let '(ndata, ndesc) := nr in
    let '(nndesc, nndata) := ((ndesc_log log), (ndata_log log)) in
    If (loglen_valid_dec xp (ndesc + nndesc) (ndata + nndata)) {
      cs <- Desc.write_aligned xp ndesc (map ent_addr log) cs;
      cs <- Data.write_aligned xp ndata (map ent_valu log) cs;
      cs <- Desc.sync_aligned xp ndata nndesc cs;
      cs <- Data.sync_aligned xp ndesc nndata cs;
      cs <- Hdr.write xp (ndesc + nndesc, ndata + nndata) cs;
      cs <- Hdr.sync xp cs;
      rx ^(cs, true)
    } else {
      rx ^(cs, false)
    }.

  Remove Hints goodSize_0.

  Ltac safestep :=
      prestep; norm; [ cancel | ];
      repeat match goal with 
      | [ |- _ /\ _ ] => split 
      | [ |- True ] => auto
      end; try pred_apply.

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
    step.
    step.

    (* return true *)
    - safestep.
      Search Desc.array_rep.
      
    (* false *)
    - hoare.

    (* crash *)
    - cancel.
  Qed.




  Definition valid_xp xp :=
    # (LogLen xp) <= nr_desc xp /\
    (* The log shouldn't overflow past the end of disk *)
    goodSize addrlen (# (LogData xp) + # (LogLen xp)).

  Definition avail_region start len : @pred addr (@weq addrlen) valuset :=
    (exists l, [[ length l = len ]] * array start l $1)%pred.

  Theorem avail_region_shrink_one : forall start len,
    len > 0
    -> avail_region start len =p=>
       start |->? * avail_region (start ^+ $1) (len - 1).
  Proof.
    destruct len; intros; try omega.
    unfold avail_region.
    norm'l; unfold stars; simpl.
    destruct l; simpl in *; try congruence.
    cancel.
  Qed.

  Definition synced_list m: list valuset := combine m (repeat nil (length m)).

  Lemma length_synced_list : forall l,
    length (synced_list l) = length l.
  Proof.
    unfold synced_list; intros.
    rewrite combine_length. autorewrite with core. auto.
  Qed.

  Definition loglen_valid xp (l: log_contents) :=
    length l <= wordToNat (LogLen xp).

  (** On-disk representation of the log *)
  Definition log_rep_synced xp (l: log_contents) : @pred addr (@weq addrlen) valuset :=
     ([[ loglen_valid xp l ]] *
      (exists rest, descrep xp (lfst (l ++ rest))) *
      (array (LogData xp) (synced_list (lsnd l)) $1) *
      avail_region (LogData xp ^+ $ (length l))
                         (wordToNat (LogLen xp) - length l))%pred.

  Definition log_rep_extended_descriptor xp (l: log_contents) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_size xp l ]] *
      exists rest rest2,
      (LogDescriptor xp) |-> (descriptor_to_valu (map fst l ++ rest), [descriptor_to_valu (map fst l ++ rest2)]) *
      [[ @Rec.well_formed descriptor_type (map fst l ++ rest) ]] *
      [[ @Rec.well_formed descriptor_type (map fst l ++ rest2) ]] *
      array (LogData xp) (synced_list (map snd l)) $1 *
      avail_region (LogData xp ^+ $ (length l))
                         (wordToNat (LogLen xp) - length l))%pred.

  Definition rep_inner xp (st: state) :=
    (* For now, support just one descriptor block, at the start of the log. *)
    ([[ valid_xp xp ]] *
    match st with
    | Synced l =>
      (LogHeader xp) |=> hdr2valu (mk_header (length l))
    * log_rep_synced xp l

    | Shortened old len =>
      [[ len <= length old ]]
    * (LogHeader xp) |-> (hdr2valu (mk_header len), hdr2valu (mk_header (length old)) :: [])
    * log_rep_synced xp old

    | ExtendedDescriptor old =>
      (LogHeader xp) |=> hdr2valu (mk_header (length old))
    * log_rep_extended_descriptor xp old

    | Extended old new =>
      (LogHeader xp) |-> (hdr2valu (mk_header (length old + length new)), hdr2valu (mk_header (length old)) :: [])
    * log_rep_synced xp (old ++ new)

    end)%pred.

  Definition rep xp F st cs := (exists d,
    BUFCACHE.rep cs d * [[ (F * rep_inner xp st)%pred d ]])%pred.

  Ltac disklog_unfold := unfold rep, rep_inner, valid_xp, log_rep_synced, log_rep_extended_descriptor, valid_size, synced_list.

  Ltac word2nat_clear := try clear_norm_goal; repeat match goal with
    | [ H : forall _, {{ _ }} _ |- _ ] => clear H
    | [ H : _ =p=> _ |- _ ] => clear H
    | [ H: ?a ?b |- _ ] =>
      match type of a with
      | pred => clear H
      end
    end.

  Lemma skipn_1_length': forall T (l: list T),
    length (match l with [] => [] | _ :: l' => l' end) = length l - 1.
  Proof.
    destruct l; simpl; omega.
  Qed.

  Hint Rewrite app_length firstn_length skipn_length combine_length map_length repeat_length length_upd
    skipn_1_length' : lengths.

  Ltac solve_lengths' :=
    repeat (progress (autorewrite with lengths; repeat rewrite Nat.min_l by solve_lengths'; repeat rewrite Nat.min_r by solve_lengths'));
    simpl; try word2nat_solve.

  Ltac solve_lengths_prepare :=
    intros; word2nat_clear; simpl;
    (* Stupidly, this is like 5x faster than [rewrite Map.cardinal_1 in *] ... *)
    repeat match goal with
    | [ H : context[Map.cardinal] |- _ ] => rewrite Map.cardinal_1 in H
    | [ |- context[Map.cardinal] ] => rewrite Map.cardinal_1
    end.

  Ltac solve_lengths_prepped :=
    try (match goal with
      | [ |- context[{{ _ }} _] ] => fail 1
      | [ |- _ =p=> _ ] => fail 1
      | _ => idtac
      end;
      word2nat_clear; word2nat_simpl; word2nat_rewrites; solve_lengths').

  Ltac solve_lengths := solve_lengths_prepare; solve_lengths_prepped.

  Theorem firstn_map : forall A B n l (f: A -> B),
    firstn n (map f l) = map f (firstn n l).
  Proof.
    induction n; simpl; intros.
    reflexivity.
    destruct l; simpl.
    reflexivity.
    f_equal.
    eauto.
  Qed.

  Lemma combine_one: forall A B (a: A) (b: B), [(a, b)] = List.combine [a] [b].
  Proof.
    intros; auto.
  Qed.

  Lemma cons_combine : forall A B (a: A) (b: B) x y,
    (a, b) :: List.combine x y = List.combine (a :: x) (b :: y).
    trivial.
  Qed.

  Definition emp_star_r' : forall V AT AEQ P, P * (emp (V:=V) (AT:=AT) (AEQ:=AEQ)) =p=> P.
  Proof.
    cancel.
  Qed.


  Definition unifiable_array := @array valuset.

  Hint Extern 0 (okToUnify (unifiable_array _ _ _) (unifiable_array _ _ _)) => constructor : okToUnify.

  Lemma make_unifiable: forall a l s,
    array a l s <=p=> unifiable_array a l s.
  Proof.
    split; cancel.
  Qed.


  Ltac word_assert P := let H := fresh in assert P as H by
      (word2nat_simpl; repeat rewrite wordToNat_natToWord_idempotent'; word2nat_solve); clear H.

  Ltac array_sort' :=
    eapply pimpl_trans; rewrite emp_star; [ apply pimpl_refl |];
    set_evars;
    repeat rewrite <- sep_star_assoc;
    subst_evars;
    match goal with
    | [ |- ?p =p=> ?p ] => fail 1
    | _ => idtac
    end;
    repeat match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      word_assert (a2 <= a1)%word;
      first [
        (* if two arrays start in the same place, try to prove one of them is empty and eliminate it *)
        word_assert (a1 = a2)%word;
        first [
          let H := fresh in assert (length l1 = 0) by solve_lengths;
          apply length_nil in H; try rewrite H; clear H; simpl; rewrite emp_star_r'
        | let H := fresh in assert (length l2 = 0) by solve_lengths;
          apply length_nil in H; try rewrite H; clear H; simpl; rewrite emp_star_r'
        | fail 2
        ]
      | (* otherwise, just swap *)
        rewrite (sep_star_assoc p (array a1 l1 s));
        rewrite (sep_star_comm (array a1 l1 s)); rewrite <- (sep_star_assoc p (array a2 l2 s))
      ]
    end;
    (* make sure we can prove it's sorted *)
    match goal with
    | [ |- context[(?p * array ?a1 ?l1 ?s * array ?a2 ?l2 ?s)%pred] ] =>
      (word_assert (a1 <= a2)%word; fail 1) || fail 2
    | _ => idtac
    end;
    eapply pimpl_trans; rewrite <- emp_star; [ apply pimpl_refl |].

  Ltac array_sort :=
    word2nat_clear; word2nat_auto; [ array_sort' | .. ].

  Lemma singular_array: forall T a (v: T),
    a |-> v <=p=> array a [v] $1.
  Proof.
    intros. split; cancel.
  Qed.

  Lemma equal_arrays: forall T (l1 l2: list T) a1 a2,
    a1 = a2 -> l1 = l2 -> array a1 l1 $1 =p=> array a2 l2 $1.
  Proof.
    cancel.
  Qed.

  Ltac rewrite_singular_array :=
    repeat match goal with
    | [ |- context[@ptsto addr (@weq addrlen) ?V ?a ?v] ] =>
      setoid_replace (@ptsto addr (@weq addrlen) V a v)%pred
      with (array a [v] $1) by (apply singular_array)
    end.

  Ltac array_cancel_trivial :=
    fold unifiable_array;
    match goal with
    | [ |- _ =p=> ?x * unifiable_array ?a ?l ?s ] => first [ is_evar x | is_var x ]; unfold unifiable_array; rewrite (make_unifiable a l s)
    | [ |- _ =p=> unifiable_array ?a ?l ?s * ?x ] => first [ is_evar x | is_var x ]; unfold unifiable_array; rewrite (make_unifiable a l s)
    end;
    solve [ cancel ].


  (* Slightly different from CPDT [equate] *)
  Ltac equate x y :=
    let tx := type of x in
    let ty := type of y in
    let H := fresh in
    assert (x = y) as H by reflexivity; clear H.

  Ltac split_pair_list_evar :=
    match goal with
    | [ |- context [ ?l ] ] =>
      is_evar l;
      match type of l with
      | list (?A * ?B) =>
        let l0 := fresh in
        let l1 := fresh in
        evar (l0 : list A); evar (l1 : list B);
        let l0' := eval unfold l0 in l0 in
        let l1' := eval unfold l1 in l1 in
        equate l (@List.combine A B l0' l1');
        clear l0; clear l1
      end
    end.

  Theorem combine_upd: forall A B i a b (va: A) (vb: B),
    List.combine (upd a i va) (upd b i vb) = upd (List.combine a b) i (va, vb).
  Proof.
    unfold upd; intros.
    apply combine_updN.
  Qed.



  Lemma cons_app: forall A l (a: A),
    a :: l = [a] ++ l.
  Proof.
    auto.
  Qed.

  Lemma firstn_app_l: forall A (al ar: list A) n,
    n <= length al ->
    firstn n (al ++ ar) = firstn n al.
  Proof.
    induction al.
    intros; simpl in *. inversion H. auto.
    intros; destruct n; simpl in *; auto.
    rewrite IHal by omega; auto.
  Qed.

  Lemma combine_map_fst_snd: forall A B (l: list (A * B)),
    List.combine (map fst l) (map snd l) = l.
  Proof.
    induction l.
    auto.
    simpl; rewrite IHl; rewrite <- surjective_pairing; auto.
  Qed.

  Lemma map_fst_combine: forall A B (a: list A) (b: list B),
    length a = length b -> map fst (List.combine a b) = a.
  Proof.
    unfold map, List.combine; induction a; intros; auto.
    destruct b; try discriminate; simpl in *.
    rewrite IHa; [ auto | congruence ].
  Qed.

  Lemma map_snd_combine: forall A B (a: list A) (b: list B),
    length a = length b -> map snd (List.combine a b) = b.
  Proof.
    unfold map, List.combine.
    induction a; destruct b; simpl; auto; try discriminate.
    intros; rewrite IHa; eauto.
  Qed.

  Hint Rewrite firstn_combine_comm skipn_combine_comm selN_combine map_fst_combine map_snd_combine
    removeN_combine List.combine_split combine_nth combine_one cons_combine updN_0_skip_1 skipn_selN : lists.
  Hint Rewrite <- combine_updN combine_upd combine_app : lists.

  Ltac split_pair_list_vars :=
    set_evars;
    repeat match goal with
    | [ H : list (?A * ?B) |- _ ] =>
      match goal with
      | |- context[ List.combine (map fst H) (map snd H) ] => fail 1
      | _ => idtac
      end;
      rewrite <- combine_map_fst_snd with (l := H)
    end;
    subst_evars.

  Ltac split_lists :=
    unfold upd_prepend, upd_sync, valuset_list;
    unfold sel, upd;
    repeat split_pair_list_evar;
    split_pair_list_vars;
    autorewrite with lists; [
      match goal with
      | [ |- ?f _ = ?f _ ] => set_evars; f_equal; subst_evars
      | [ |- ?f _ _ = ?f _ _ ] => set_evars; f_equal; subst_evars
      | _ => idtac
      end | solve_lengths .. ].

  Ltac lists_eq :=
    subst; autorewrite with core; rec_simpl;
    word2nat_clear; word2nat_auto;
    autorewrite with lengths in *;
    solve_lengths_prepare;
    split_lists;
    repeat rewrite firstn_oob by solve_lengths_prepped;
    repeat erewrite firstn_plusone_selN by solve_lengths_prepped;
    unfold sel; repeat rewrite selN_app1 by solve_lengths_prepped; repeat rewrite selN_app2 by solve_lengths_prepped.
    (* intuition. *) (* XXX sadly, sometimes evars are instantiated the wrong way *)

  Ltac log_simp :=
    repeat rewrite descriptor_valu_id by (hnf; intuition; solve_lengths).

  Ltac chop_arrays a1 l1 a2 l2 s := idtac;
    match type of l2 with
     | list ?T =>
       let l1a := fresh in evar (l1a : list T);
       let l1b := fresh in evar (l1b : list T);
       let H := fresh in
       cut (l1 = l1a ++ l1b); [
         intro H; replace (array a1 l1 s) with (array a1 (l1a ++ l1b) s) by (rewrite H; trivial); clear H;
         rewrite <- (@array_app T l1a l1b a1 a2); [
           rewrite <- sep_star_assoc; apply pimpl_sep_star; [ | apply equal_arrays ]
         | ]
       | eauto ]
     end.

  Lemma cons_app1 : forall T (x: T) xs, x :: xs = [x] ++ xs. trivial. Qed.

  Ltac chop_shortest_suffix := idtac;
    match goal with
    | [ |- _ * array ?a1 ?l1 ?s =p=> _ * array ?a2 ?l2 ?s ] =>
      (let H := fresh in assert (a1 = a2)%word as H by
        (word2nat_simpl; repeat rewrite wordToNat_natToWord_idempotent'; word2nat_solve);
       apply pimpl_sep_star; [ | apply equal_arrays; [ try rewrite H; trivial | eauto ] ]) ||
      (word_assert (a1 <= a2)%word; chop_arrays a1 l1 a2 l2 s) ||
      (word_assert (a2 <= a1)%word; chop_arrays a2 l2 a1 l1 s)
    end.

  Ltac array_match_prepare :=
    unfold unifiable_array in *;
    match goal with (* early out *)
    | [ |- _ =p=> _ * array _ _ _ ] => idtac
    | [ |- _ =p=> _ * _ |-> _ ] => idtac
    | [ |- _ =p=> array _ _ _ ] => idtac
    end;
    solve_lengths_prepare;
    rewrite_singular_array;
    array_sort;
    eapply pimpl_trans; rewrite emp_star; [ apply pimpl_refl |];
    set_evars; repeat rewrite <- sep_star_assoc.

  Ltac array_match' :=
    array_match_prepare;
    repeat (progress chop_shortest_suffix);
    subst_evars; [ apply pimpl_refl | .. ].

  Ltac array_match_goal :=
      match goal with
      | [ |- @eq ?T ?a ?b ] =>
        match T with
        | list ?X =>
          (is_evar a; is_evar b; fail 1) || (* XXX this works around a Coq anomaly... *)
          lists_eq; auto; repeat match goal with
          | [ |- context[?a :: ?b] ] => match b with | nil => fail 1 | _ => idtac end; rewrite (cons_app1 a b); auto
          end
        | _ => idtac
        end
      | _ => idtac
      end.

  Ltac array_match :=
    array_match'; array_match_goal; array_match_goal; solve_lengths.

  Ltac or_r := apply pimpl_or_r; right.
  Ltac or_l := apply pimpl_or_r; left.


  Definition read_log T (xp : log_xparams) cs rx : prog T :=
    let^ (cs, d) <- BUFCACHE.read (LogDescriptor xp) cs;
    let desc := valu_to_descriptor d in
    let^ (cs, h) <- BUFCACHE.read (LogHeader xp) cs;
    let len := (valu2hdr h) :-> "length" in
    let^ (cs, log) <- For i < len
    Ghost [ cur log_on_disk F ]
    Loopvar [ cs log_prefix ]
    Continuation lrx
    Invariant
      rep xp F (Synced log_on_disk) cs
    * [[ log_prefix = firstn (# i) log_on_disk ]]
    OnCrash
      exists cs, rep xp F (Synced cur) cs
    Begin
      let^ (cs, v) <- BUFCACHE.read_array (LogData xp) i cs;
      lrx ^(cs, log_prefix ++ [(sel desc i $0, v)])
    Rof ^(cs, []);
    rx ^(log, cs).


  Theorem read_log_ok: forall xp cs,
    {< l F,
    PRE
      rep xp F (Synced l) cs
    POST RET:^(r,cs)
      [[ r = l ]] * rep xp F (Synced l) cs
    CRASH
      exists cs', rep xp F (Synced l) cs'
    >} read_log xp cs.
  Proof.
    unfold read_log; disklog_unfold.
    intros. (* XXX this hangs: autorewrite_fast_goal *)
    eapply pimpl_ok2; [ eauto with prog | ].
    unfold valid_size.
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    unfold valid_size.
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    unfold valid_size.
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    unfold valid_size.
    subst.
    rewrite header_valu_id in *.
    rec_simpl.
    cancel.
    fold unifiable_array; cancel_with solve_lengths.
    solve_lengths.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    unfold log_contents in *.
    log_simp.
    lists_eq; reflexivity.
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    lists_eq; reflexivity.
    cancel.
    cancel.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_log _ _) _) => apply read_log_ok : prog.


  Definition extend_unsync T xp (cs: cachestate) (old: log_contents) (oldlen: addr) (new: log_contents) rx : prog T :=
    cs <- BUFCACHE.write (LogDescriptor xp)
      (descriptor_to_valu (map fst (old ++ new))) cs;
    let^ (cs) <- For i < $ (length new)
    Ghost [ crash F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * exists l', [[ length l' = # i ]]
          * array (LogData xp ^+ $ (length old)) (List.combine (firstn (# i) (map snd new)) l') $1
          * avail_region (LogData xp ^+ $ (length old) ^+ i) (# (LogLen xp) - length old - # i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.write_array (LogData xp ^+ oldlen ^+ i) $0
        (sel (map snd new) i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx ^(cs).

  Definition extend_sync T xp (cs: cachestate) (old: log_contents) (oldlen: addr) (new: log_contents) rx : prog T :=
    cs <- BUFCACHE.sync (LogDescriptor xp) cs;
    let^ (cs) <- For i < $ (length new)
    Ghost [ crash F ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', BUFCACHE.rep cs d' *
      [[ (F
          * array (LogData xp ^+ $ (length old)) (firstn (# i) (synced_list (map snd new))) $1
          * exists l', [[ length l' = length new - # i ]]
          * array (LogData xp ^+ $ (length old) ^+ i) (List.combine (skipn (# i) (map snd new)) l') $1
          * avail_region (LogData xp ^+ $ (length old) ^+ $ (length new)) (# (LogLen xp) - length old - length new))%pred d' ]]
    OnCrash crash
    Begin
      cs <- BUFCACHE.sync_array (LogData xp ^+ oldlen ^+ i) $0 cs;
      lrx ^(cs)
    Rof ^(cs);
    cs <- BUFCACHE.write (LogHeader xp) (hdr2valu (mk_header (length old + length new))) cs;
    cs <- BUFCACHE.sync (LogHeader xp) cs;
    rx ^(cs).

  Definition extend T xp (cs: cachestate) (old: log_contents) (oldlen: addr) (new: log_contents) rx : prog T :=
    If (lt_dec (wordToNat (LogLen xp)) (length old + length new)) {
      rx ^(^(cs), false)
    } else {
      (* Write... *)
      let^ (cs) <- extend_unsync xp cs old oldlen new;
      (* ... and sync *)
      let^ (cs) <- extend_sync xp cs old oldlen new;
      rx ^(^(cs), true)
    }.

  Definition extended_unsynced xp (old: log_contents) (new: log_contents) : @pred addr (@weq addrlen) valuset :=
     ([[ valid_size xp (old ++ new) ]] *
      (LogHeader xp) |=> (hdr2valu (mk_header (length old))) *
      exists rest rest2,
      (LogDescriptor xp) |-> (descriptor_to_valu (map fst (old ++ new) ++ rest),
                              [descriptor_to_valu (map fst old ++ rest2)]) *
      [[ @Rec.well_formed descriptor_type (map fst (old ++ new) ++ rest) ]] *
      [[ @Rec.well_formed descriptor_type (map fst old ++ rest2) ]] *
      array (LogData xp) (synced_list (map snd old)) $1 *
      exists unsynced, (* XXX unsynced is the wrong word for the old values *)
      [[ length unsynced = length new ]] *
      array (LogData xp ^+ $ (length old)) (List.combine (map snd new) unsynced) $1 *
      avail_region (LogData xp ^+ $ (length old) ^+ $ (length new))
                         (# (LogLen xp) - length old - length new))%pred.

  Lemma in_1 : forall T (x y: T), In x [y] -> x = y.
    intros.
    inversion H.
    congruence.
    inversion H0.
  Qed.


  Theorem extend_unsync_ok : forall xp cs old oldlen new,
    {< F,
    PRE
      [[ # oldlen = length old ]] *
      [[ valid_size xp (old ++ new) ]] *
      rep xp F (Synced old) cs
    POST RET:^(cs)
      exists d, BUFCACHE.rep cs d *
      [[ (F * extended_unsynced xp old new)%pred d ]]
    CRASH
      exists cs' : cachestate,
      rep xp F (Synced old) cs' \/ rep xp F (ExtendedDescriptor old) cs'
    >} extend_unsync xp cs old oldlen new.
  Proof.
    unfold extend_unsync; disklog_unfold; unfold avail_region, extended_unsynced.
    intros.
    solve_lengths_prepare.
    (* step. (* XXX takes a very long time *) *)
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    word2nat_clear.
    autorewrite with lengths in *.
    word2nat_auto.
    rewrite Nat.add_0_r.
    fold unifiable_array.
    cancel.
    instantiate (1 := nil); auto.
    solve_lengths.
    autorewrite with lengths in *.
    (* step. *)
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    word2nat_clear; word2nat_auto.
    fold unifiable_array; cancel.
    solve_lengths.
    (* step. *)
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    word2nat_clear; word2nat_auto.
    cancel.
    array_match.
    solve_lengths.
    solve_lengths.
    cancel.
    or_r; cancel.
    unfold valuset_list; simpl; rewrite map_app.
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - length old - length new).
    rewrite <- app_assoc.
    word2nat_clear.
    cancel.
    array_match.
    solve_lengths.
    rewrite Forall_forall; intuition.
    solve_lengths.
    rewrite Forall_forall; intuition.
    solve_lengths.

    or_r; cancel.
    unfold valuset_list; simpl; rewrite map_app.
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - length old - length new).
    rewrite <- app_assoc.
    cancel.
    (* unpack [array_match] due to "variable H4 unbound" anomaly *)
    array_match_prepare.
    chop_shortest_suffix.
    chop_shortest_suffix.
    chop_shortest_suffix.
    apply pimpl_refl.
    all: subst_evars.
    array_match_goal.
    2: array_match_goal.
    3: reflexivity.
    solve_lengths.
    solve_lengths.
    solve_lengths.
    rewrite Forall_forall; intuition.
    unfold upd_prepend.
    solve_lengths.
    rewrite Forall_forall; intuition.
    unfold upd_prepend.
    solve_lengths.

    (* step. *)
    eapply pimpl_ok2; [ eauto with prog | ].
    word2nat_clear.
    autorewrite with lengths in *.
    word2nat_auto.
    (* XXX once again we have to unpack [cancel] because otherwise [Forall_nil] gets incorrectly applied *)
    intros. norm. cancel'.
    unfold avail_region.
    intuition. pred_apply.
    norm. cancel'. unfold stars; simpl; eapply pimpl_trans; [ apply star_emp_pimpl |].
    unfold valuset_list.
    simpl.
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - length old - length new).
    cancel.
    unfold synced_list.
    array_match.
    intuition.
    unfold valid_size; solve_lengths.
    solve_lengths.
    rewrite Forall_forall; intuition.
    solve_lengths.
    congruence.
    congruence.
    autorewrite with lengths in *.
    cancel.
    or_r; cancel. (* this is a strange goal *)
    instantiate (m := d').
    pred_apply.
    cancel.
    unfold valuset_list.
    simpl.
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - length old - length new).
    rewrite map_app; rewrite <- app_assoc.
    cancel.
    solve_lengths.
    rewrite Forall_forall; intuition.
    solve_lengths.
    rewrite Forall_forall; intuition.
    solve_lengths.
    cancel.
    cancel.
    or_r; cancel.
    unfold valuset_list.
    simpl.
    rewrite <- descriptor_to_valu_zeroes with (n := addr_per_block - length old - length new).
    rewrite map_app; rewrite <- app_assoc.
    cancel.
    word2nat_clear; autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    word2nat_clear; autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    solve_lengths.

    Unshelve.
    all: eauto; constructor.
  Qed.

  Hint Extern 1 ({{_}} progseq (extend_unsync _ _ _ _ _) _) => apply extend_unsync_ok : prog.


  Theorem extend_sync_ok : forall xp cs old oldlen new,
    {< F,
    PRE
      [[ # oldlen = length old ]] *
      [[ valid_xp xp ]] *
      [[ valid_size xp (old ++ new) ]] *
      exists d, BUFCACHE.rep cs d *
      [[ (F * extended_unsynced xp old new)%pred d ]]
    POST RET:^(cs')
      rep xp F (Synced (old ++ new)) cs'
    CRASH
      exists cs' : cachestate,
      rep xp F (ExtendedDescriptor old) cs' \/ rep xp F (Synced old) cs' \/ rep xp F (Extended old new) cs' \/ rep xp F (Synced (old ++ new)) cs'
    >} extend_sync xp cs old oldlen new.
  Proof.
    unfold extend_sync; disklog_unfold; unfold avail_region, extended_unsynced.
    intros.
    solve_lengths_prepare.
    (* step. (* XXX takes a very long time *) *)
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    unfold avail_region.
    cancel.
    word2nat_clear; word2nat_auto.
    rewrite Nat.add_0_r.
    fold unifiable_array; cancel.
    solve_lengths.
    solve_lengths.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    word2nat_clear; word2nat_auto.
    fold unifiable_array; cancel.
    solve_lengths.
    unfold valid_size in *.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    word2nat_clear.
    autorewrite with lengths in *.
    word2nat_auto.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    (* subst_evars here would cause an anomaly trying to instantiate H14 *)
    subst H14.
    reflexivity.
    auto.
    subst_evars; reflexivity.
    subst H14.
    solve_lengths.
    (* XXX revise once the anomalies are fixed *)
    subst H14 H19.
    erewrite firstn_plusone_selN by solve_lengths.
    trivial.
    trivial.
    subst H12; trivial.
    subst H11.
    solve_lengths.
    unfold upd_sync.
    subst H11 H12.
    unfold sel, upd; simpl.
    instantiate (l'0 := skipn 1 l').
    subst H4.
    repeat rewrite selN_combine.
    lists_eq.
    subst H6.
    trivial.
    solve_lengths.
    autorewrite with lengths in *.
    solve_lengths.
    solve_lengths.
    cancel.
    or_r; or_l. norm. cancel'.
    repeat constructor. pred_apply.

    rewrite map_app.
    rewrite <- app_assoc.
    cancel.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    array_match.
    unfold synced_list. autorewrite with lengths. trivial.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    solve_lengths.

    or_r; or_l; cancel.
    rewrite map_app.
    rewrite <- app_assoc.
    cancel.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    array_match.
    unfold synced_list. autorewrite with lengths. trivial.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.
    unfold upd_sync.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.

    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    word2nat_clear.
    autorewrite with lengths in *.
    rewrite map_app.
    cancel.
    unfold synced_list.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    subst_evars.
    reflexivity.
    reflexivity.
    subst H6. (* subst_evars here leads to an anomaly *)
    reflexivity.
    subst H4.
    solve_lengths.
    subst H4 H6.
    unfold valid_size in *.
    autorewrite with lengths in *.
    lists_eq.
    trivial.
    rewrite app_repeat.
    trivial.
    subst_evars.
    trivial.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.

    cancel.
    or_r; or_r; or_l; cancel.
    word2nat_clear. unfold valid_size in *. autorewrite with lengths in *.
    unfold synced_list.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    subst_evars. reflexivity.
    reflexivity.
    (* subst_evars here gives an anomaly *) subst H6. reflexivity.
    subst H4. solve_lengths.
    subst H4 H6. lists_eq.
    trivial.
    rewrite app_repeat. trivial.
    subst H1. reflexivity.
    word2nat_clear. unfold valid_size in *. autorewrite with lengths in *.
    solve_lengths.

    or_r; or_r; or_r; cancel.
    word2nat_clear. unfold valid_size in *. autorewrite with lengths in *.
    unfold synced_list.
    cancel.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    subst_evars. reflexivity.
    reflexivity.
    (* subst_evars here gives an anomaly *) subst H6. reflexivity.
    subst H4. solve_lengths.
    subst H4 H6. lists_eq.
    trivial.
    rewrite app_repeat. trivial.
    subst H1. reflexivity.
    word2nat_clear. unfold valid_size in *. autorewrite with lengths in *.
    solve_lengths.

    cancel.
    or_r; or_l; cancel.
    rewrite map_app.
    rewrite <- app_assoc.
    cancel.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    array_match.
    unfold synced_list. autorewrite with lengths. trivial.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.
    unfold upd_sync.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.

    cancel.
    or_r; or_r; or_l; cancel.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold synced_list.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    subst_evars. reflexivity.
    reflexivity.
    (* subst_evars here gives an anomaly *) subst H6. reflexivity.
    subst H4. solve_lengths.
    subst H4 H6. lists_eq.
    trivial.
    rewrite app_repeat. trivial.
    subst H1. reflexivity.
    word2nat_clear. unfold valid_size in *. autorewrite with lengths in *.
    solve_lengths.

    cancel.
    or_r; or_l; cancel.
    instantiate (1 := d').
    pred_apply. cancel.
    rewrite map_app.
    rewrite <- app_assoc.
    cancel.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    array_match.
    unfold synced_list. autorewrite with lengths. trivial.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.
    unfold upd_sync.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.

    cancel.
    rewrite map_app.
    rewrite <- app_assoc.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    cancel.
    array_match.
    unfold synced_list. autorewrite with lengths. trivial.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.
    unfold upd_sync.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    solve_lengths.
    rewrite Forall_forall; intuition.
    word2nat_clear.
    unfold valid_size in *.
    autorewrite with lengths in *.
    unfold upd_sync.
    solve_lengths.

    Unshelve.
    all: auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (extend_sync _ _ _ _ _) _) => apply extend_sync_ok : prog.

  Theorem extend_ok : forall xp cs old new rx,
    {< F,
    PRE
      rep xp F (Synced old) cs
    POST RET:^(cs,r)
      ([[ r = true ]] * rep xp F (Synced new) cs \/
      ([[ r = false ]] * rep xp F (Synced old) cs
    CRASH
      exists cs' : cachestate,
      rep xp F (ExtendedDescriptor old) cs' \/ rep xp F (Synced old) cs' \/ rep xp F (Extended old new) cs' \/ rep xp F (Synced (old ++ new)) cs'
    >} extend xp old new cs.
  Proof.
    unfold extend.
    step.
    step.
    step.
    step.
    step.
    or_l. cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (extend _ _ _ _) _) => apply extend_ok : prog.


  Definition shorten T xp newlen cs rx : prog T :=
    cs <- BUFCACHE.write (LogHeader xp) (hdr2valu (mk_header newlen)) cs;
    cs <- BUFCACHE.sync (LogHeader xp) cs;
    rx ^(cs).

  Theorem shorten_ok: forall xp newlen cs,
    {< F old,
    PRE
      [[ newlen <= length old ]] *
      rep xp F (Synced old) cs
    POST RET:^(cs)
      exists new cut,
      [[ old = new ++ cut ]] *
      [[ length new = newlen ]] *
      rep xp F (Synced new) cs
    CRASH
      exists cs' : cachestate,
      rep xp F (Synced old) cs' \/ rep xp F (Shortened old newlen) cs' \/
      exists new cut,
      [[ old = new ++ cut ]] *
      [[ length new = newlen ]] *
      rep xp F (Synced new) cs'
    >} shorten xp newlen cs.
  Proof.
    unfold shorten; disklog_unfold; unfold avail_region, valid_size.
    intros.
    solve_lengths_prepare.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    cancel.
    eapply pimpl_ok2; [ eauto with prog | ].
    intros. norm.
    cancel'. repeat constructor.
    (* XXX this looks rather hard to automate *)
    rewrite (firstn_skipn newlen).
    trivial.
    solve_lengths.
    pred_apply.
    cancel.
    (* XXX this is also hard to automate *)
    replace (map fst old) with (map fst (firstn newlen old ++ skipn newlen old)).
    rewrite map_app. rewrite <- app_assoc.
    autorewrite with lengths.
    rewrite Nat.min_l by auto.
    cancel.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    subst_evars. reflexivity.
    reflexivity.
    subst_evars. reflexivity.
    subst H3. solve_lengths.
    subst H3 H4. lists_eq. rewrite firstn_skipn. trivial.
    rewrite app_repeat. (* XXX solve_lengths here gives an anomaly *)
    autorewrite with lengths. rewrite Nat.min_r by auto.
    (* XXX also not sure how to automate this *)
    instantiate (1 := length old - newlen).
    rewrite le_plus_minus_r by auto.
    trivial.
    trivial.
    subst_evars. trivial.
    subst_evars. solve_lengths.
    subst H1. solve_lengths.
    subst H1. solve_lengths.
    subst H0 H1 H2. trivial.
    rewrite firstn_skipn. trivial.
    solve_lengths.
    word2nat_clear. autorewrite with lengths in *.
    solve_lengths.
    trivial.
    rewrite Forall_forall; intuition.
    word2nat_clear. autorewrite with lengths in *.
    solve_lengths.
    solve_lengths.
    congruence.
    congruence.

    cancel.
    or_r; or_l; cancel.
    or_r; or_r.
    norm. cancel'.
    constructor. (* [intuition] screws up here... *)
    word2nat_clear. unfold valid_size in *. autorewrite with lengths in *.
    constructor.
    rewrite (firstn_skipn newlen).
    trivial.
    solve_lengths.
    intuition.
    pred_apply.
    cancel.
    replace (map fst old) with (map fst (firstn newlen old ++ skipn newlen old)).
    rewrite map_app. rewrite <- app_assoc.
    autorewrite with lengths.
    rewrite Nat.min_l by auto.
    cancel.
    array_match_prepare.
    repeat chop_shortest_suffix.
    auto.
    subst_evars. reflexivity.
    reflexivity.
    subst_evars. reflexivity.
    subst H3. solve_lengths.
    subst H3 H4. lists_eq. rewrite firstn_skipn. trivial.
    rewrite app_repeat. (* XXX solve_lengths here gives an anomaly *)
    autorewrite with lengths. rewrite Nat.min_r by auto.
    (* XXX also not sure how to automate this *)
    instantiate (1 := length old - newlen).
    rewrite le_plus_minus_r by auto.
    trivial.
    trivial.
    subst_evars. trivial.
    subst_evars. solve_lengths.
    subst H1. solve_lengths.
    subst H1. solve_lengths.
    subst H0 H1 H2. trivial.
    rewrite firstn_skipn. trivial.
    solve_lengths.
    word2nat_clear. autorewrite with lengths in *.
    solve_lengths.
    trivial.
    rewrite Forall_forall; intuition.
    word2nat_clear. autorewrite with lengths in *.
    solve_lengths.
    solve_lengths.

    cancel.
    or_l; cancel.
    or_r; or_l; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (shorten _ _ _ _) _) => apply shorten_ok : prog.


  Lemma crash_invariant_synced_array: forall l start stride,
    crash_xform (array start (List.combine l (repeat nil (length l))) stride) =p=>
    array start (List.combine l (repeat nil (length l))) stride.
  Proof.
    unfold array.
    induction l; intros; simpl; auto.
    autorewrite with crash_xform.
    cancel.
    auto.
  Qed.
  Hint Rewrite crash_invariant_synced_array : crash_xform.

  Definition possible_crash_list (l: list valuset) (l': list valu) :=
    length l = length l' /\ forall i, i < length l -> In (selN l' i $0) (valuset_list (selN l i ($0, nil))).

  Lemma crash_xform_array: forall l start stride,
    crash_xform (array start l stride) =p=>
      exists l', [[ possible_crash_list l l' ]] * array start (List.combine l' (repeat nil (length l'))) stride.
  Proof.
    unfold array, possible_crash_list.
    induction l; intros.
    cancel.
    instantiate (1 := nil).
    simpl; auto.
    auto.
    autorewrite with crash_xform.
    rewrite IHl.
    cancel.
    instantiate (1 := v' :: l').
    all: simpl; auto; fold repeat; try cancel;
      destruct i; simpl; auto;
      destruct (H4 i); try omega; simpl; auto.
  Qed.

  Lemma crash_invariant_avail_region: forall start len,
    crash_xform (avail_region start len) =p=> avail_region start len.
  Proof.
    unfold avail_region.
    intros.
    autorewrite with crash_xform.
    norm'l.
    unfold stars; simpl.
    autorewrite with crash_xform.
    rewrite crash_xform_array.
    unfold possible_crash_list.
    cancel.
    solve_lengths.
  Qed.
  Hint Rewrite crash_invariant_avail_region : crash_xform.

  Definition would_recover_either' xp old cur :=
   (rep_inner xp (Synced old) \/
    (exists cut, [[ old = cur ++ cut ]] * rep_inner xp (Shortened old (length cur))) \/
    (exists new, [[ cur = old ++ new ]] * rep_inner xp (Extended old new)) \/
    rep_inner xp (Synced cur))%pred.

  Definition after_crash' xp old cur :=
   (rep_inner xp (Synced old) \/
    rep_inner xp (Synced cur))%pred.

  Lemma sep_star_or_distr_r: forall AT AEQ V (a b c: @pred AT AEQ V),
    (a \/ b) * c <=p=> a * c \/ b * c.
  Proof.
    intros.
    rewrite sep_star_comm.
    rewrite sep_star_or_distr.
    split; cancel.
  Qed.

  Lemma or_exists_distr : forall T AT AEQ V (P Q: T -> @pred AT AEQ V),
    (exists t: T, P t \/ Q t) =p=> (exists t: T, P t) \/ (exists t: T, Q t).
  Proof.
    firstorder.
  Qed.

  Lemma lift_or : forall AT AEQ V P Q,
    @lift_empty AT AEQ V (P \/ Q) =p=> [[ P ]] \/ [[ Q ]].
  Proof.
    firstorder.
  Qed.

  Lemma crash_xform_would_recover_either' : forall fsxp old cur,
    crash_xform (would_recover_either' fsxp old cur) =p=>
    after_crash' fsxp old cur.
  Proof.
    unfold would_recover_either', after_crash'; disklog_unfold; unfold avail_region, valid_size.
    intros.
    autorewrite with crash_xform.
(* XXX this hangs:
    setoid_rewrite crash_xform_sep_star_dist. *)
    repeat setoid_rewrite crash_xform_sep_star_dist at 1.
    setoid_rewrite crash_invariant_avail_region.
    setoid_rewrite crash_xform_exists_comm.
    setoid_rewrite crash_invariant_synced_array.
    repeat setoid_rewrite crash_xform_sep_star_dist at 1.
    setoid_rewrite crash_invariant_avail_region.
    setoid_rewrite crash_invariant_synced_array.
    cancel; autorewrite with crash_xform.
    + unfold avail_region; cancel_with solve_lengths.
    + cancel.
      or_r. subst. unfold avail_region. cancel_with solve_lengths.
      repeat rewrite map_app.
      rewrite <- app_assoc.
      cancel.
      autorewrite with lengths in *.
      array_match_prepare.
      repeat chop_shortest_suffix.
      auto.
      all: subst_evars.
      all: try reflexivity.
      solve_lengths.
      lists_eq.
      reflexivity.
      rewrite repeat_app.
      reflexivity.
      solve_lengths.
      autorewrite with lengths in *.
      solve_lengths.
      autorewrite with lengths in *.
      solve_lengths.
      rewrite Forall_forall; intuition.
      autorewrite with lengths in *.
      solve_lengths.
      exact (fun x => None).
      or_l. subst. unfold avail_region. unfold valid_size in *. cancel.
    + or_l. unfold avail_region. unfold valid_size in *.
      simpl.
      setoid_rewrite lift_or.
      repeat setoid_rewrite sep_star_or_distr_r.
      setoid_rewrite or_exists_distr.
      cancel.
      subst; cancel.
      all: trivial.
      subst; cancel.
      all: trivial.
    + cancel; subst.
      or_r. autorewrite with lengths. unfold avail_region. cancel.
      autorewrite with lengths in *. trivial.
      or_l. unfold avail_region. cancel.
      repeat rewrite map_app.
      rewrite <- app_assoc.
      cancel.
      autorewrite with lengths in *.
      array_match_prepare.
      repeat chop_shortest_suffix.
      auto.
      all: subst_evars.
      all: try reflexivity.
      solve_lengths.
      lists_eq.
      reflexivity.
      rewrite repeat_app.
      reflexivity.
      solve_lengths.
      autorewrite with lengths in *.
      solve_lengths.
      autorewrite with lengths in *.
      solve_lengths.
      rewrite Forall_forall; intuition.
      autorewrite with lengths in *.
      solve_lengths.
    + cancel.
      or_r. subst. unfold avail_region. unfold valid_size in *. cancel.
  Qed.

End DISKLOG.