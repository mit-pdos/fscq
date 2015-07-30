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
Require Import GenSep.
Require Import WordAuto.
Require Import Cache.
Require Import FSLayout.
Require Import Rounding.
Require Import List.

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

  Local Hint Resolve items_per_val_not_0 items_per_val_gt_0.

  Hint Rewrite firstn_nil : core.

  Lemma setlen_nil : forall A n (def : A),
    setlen nil n def = repeat def n.
  Proof.
    unfold setlen; t.
  Qed.
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


  Definition itemlist := list item.

  Definition val_upd_rec rec item : nat * valu := 
    let '(off, v) := rec in
    (S off, word2val (Rec.word_updN off (val2word v) item)).

  Definition val_upd_range (v : valu) (off : nat) (items : itemlist) : valu :=
    let '(_ , v) := fold_left val_upd_rec (map Rec.to_word items) (off, v) in v.


  Fixpoint list_chunk' {A} (l : list A) (sz : nat) (def : A) (nr : nat) : list (list A) :=
    match nr with
    | S n => setlen l sz def :: (list_chunk' (skipn sz l) sz def n)
    | O => []
    end.

  (** cut list l into chunks of lists of length sz, pad the tailing list with default value def *)
  Definition list_chunk {A} l sz def : list (list A) :=
    list_chunk' l sz def (divup (length l) sz).

  Inductive state : Type :=
  | Synced : itemlist -> state
  | Unsync : itemlist -> state
  .

  (** a variant of array where only the latest valu in the valuset is defined *)
  Definition unsync_array start l: @pred addr (@weq _) valuset :=
    (exists vs, [[ length vs = length l ]] *
     array start (combine l vs) $1 )%pred.

  Definition synced_array start l: @pred addr (@weq _) valuset :=
    (array start (combine l (repeat nil (length l))) $1 )%pred.

  (** rep invariant *)
  Definition rep_common xp items vlist := 
       Forall Rec.well_formed items
    /\ length items <= #(RALen xp) * items_per_val
    /\ vlist = map block2val (list_chunk items items_per_val item0).

  Definition array_rep xp (st : state) :=
   (match st with
    | Synced items => exists vlist,
        [[ rep_common xp items vlist ]] *
        synced_array (RAStart xp) vlist
    | Unsync items => exists vlist,
        [[ rep_common xp items vlist ]] * 
        unsync_array (RAStart xp) vlist
    end)%pred.

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

  Lemma forall_skipn: forall A n (l : list A) p,
    Forall p l -> Forall p (skipn n l).
  Proof.
    induction n; t.
    destruct l; t.
    apply IHn.
    eapply Forall_cons2; eauto.
  Qed.
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

  Lemma list_chunk_spec : forall l i,
    selN (list_chunk l items_per_val item0) i block0 
    = setlen (skipn (i * items_per_val) l) items_per_val item0.
  Proof.
    unfold list_chunk; intros.
    destruct (lt_dec i (divup (length l) items_per_val)).
    apply list_chunk'_spec; auto.
    rewrite selN_oob by t.
    rewrite skipn_oob; t.
  Qed.

  Lemma setlen_inbound : forall A n (l : list A) def,
    n <= length l ->
    setlen l n def = firstn n l.
  Proof.
    unfold setlen; intros.
    replace (n - length l) with 0 by omega; t.
  Qed.

  Lemma list_chunk_app : forall l i pre,
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
  Definition xparams_ok xp := goodSize addrlen (#(RALen xp) * items_per_val).

  Local Hint Unfold array_rep rep_common synced_array unsync_array sel upd item xparams_ok: hoare_unfold.

  Local Hint Extern 0 (okToUnify (list_chunk ?a ?b _) (list_chunk ?a ?b _)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (list_chunk _ ?b ?c) (list_chunk _ ?b ?c)) => constructor : okToUnify.
  Local Hint Extern 0 (okToUnify (array (RAStart _) _ _) (array (RAStart _) _ _)) => constructor : okToUnify.

  Ltac prestep := intros; eapply pimpl_ok2; eauto with prog; intros.

  (** Fast 'autorewrite with core' in a given hypothesis *)
  Ltac simplen_rewrite H := try progress (
    set_evars_in H; (rewrite_strat (topdown (hints core)) in H); subst_evars;
      [ try autorewrite_fast | try autorewrite_fast_goal .. ];
    match type of H with
    | context [ length (list_chunk _ _ _) ] => rewrite block_chunk_length in H
    end).

  Ltac simplen' := repeat match goal with
    | [H : context[length ?x] |- _] => (is_var x || (progress simplen_rewrite H))
    | [H : ?l = _  |- context [ ?l ] ] => rewrite H
    | [H : ?l = _ , H2 : context [ ?l ] |- _ ] => rewrite H in H2
    | [H : (_ < $ _)%word |- _ ] => apply wlt_nat2word_word2nat_lt in H
    | [ H : @length ?T ?l = 0 |- context [?l] ] => replace l with (@nil T) by eauto
    | [ |- # ($ _) < _ ] => apply wordToNat_natToWord_lt
    | [ |- _ < _ ] => try solve [eapply lt_le_trans; eauto; try omega ]
    end.

  Ltac elimwrt' :=
    repeat (repeat match goal with
    | [ |- goodSize _ (_ - _) ] => apply goodSize_sub
    | [H: goodSize _ ?a |- goodSize _ ?b ] => ((constr_eq a b; eauto) ||
      (eapply goodSize_trans; [ | eauto] ) )
    | [H: ?a < divup ?b ?c |- context [?a] ] =>
      match goal with
      | [H2: divup ?b ?c <= ?b |- _ ] => idtac
      | _ =>  pose proof (divup_lt_arg b c)
      end
    | [ |- divup _ _ <= _ ] => eapply le_trans; [ apply divup_lt_arg | ]
    end; simpl; eauto; try omega).

  (* eliminate word round trip *)
  Ltac elimwrt := match goal with
    | [ |- context [ wordToNat (natToWord _ ?x) ] ] => 
      rewrite wordToNat_natToWord_idempotent' by elimwrt'
  end.

  Ltac simplen := unfold eqlen; eauto; repeat (try subst; simpl;
    try elimwrt; simplen'; auto; autorewrite with core); simpl; eauto; try omega.

  Hint Rewrite selN_combine using simplen : core.
  Local Hint Resolve tt : core.

  Lemma read_all_progress : forall i count pre items,
    firstn (Nat.min (i * items_per_val) count) pre = firstn (Nat.min (i * items_per_val) count) items
    -> count <= length items
    -> length pre = i * items_per_val
    -> firstn (Nat.min ((S i) * items_per_val) count)
              (pre ++ selN (list_chunk items items_per_val item0) i block0 ) =
       firstn (Nat.min ((S i) * items_per_val) count) items.
  Proof.
    intros.
    destruct (Min.min_spec (i * items_per_val) count); intuition; simplen.
    destruct (Min.min_spec ((S i) * items_per_val) count); intuition; simpl in *; simplen.

    rewrite Nat.add_comm; rewrite firstn_sum_app by auto.
    erewrite list_chunk_app; [ | simplen | eauto ].
    repeat rewrite firstn_oob by simplen; auto.

    rewrite firstn_app_le; simplen.
    replace count with (i * items_per_val + (count - i * items_per_val)) at 2 by omega.
    rewrite firstn_sum_split; f_equal.
    rewrite <- H; rewrite firstn_oob; simplen.
    rewrite list_chunk_spec.
    apply firstn_setlen_firstn; simplen.

    destruct (Min.min_spec ((S i) * items_per_val) count); intuition; simpl in *; simplen.
    generalize items_per_val_not_0; simpl in *; simplen.
    rewrite firstn_app_l; simplen.
  Qed.


  (** read count items starting from the beginning *)
  Definition read_all T xp count cs rx : prog T :=
    let nr := divup count items_per_val in
    let^ (cs, log) <- ForN i < nr
    Ghost [ crash F items d ]
    Loopvar [ cs pf ]
    Continuation lrx
    Invariant
      BUFCACHE.rep cs d *
      [[ (F * array_rep xp (Synced items))%pred d ]] *
      [[ let n := Nat.min (i * items_per_val)%nat count in
         firstn n pf = firstn n items /\ length pf = (i * items_per_val)%nat ]]
    OnCrash   crash
    Begin
      let^ (cs, v) <- BUFCACHE.read_array (RAStart xp) ($ i) cs;
      lrx ^(cs, pf ++ (val2block v))
    Rof ^(cs, []);
    rx ^(cs, firstn count log).


  Theorem read_all_ok : forall xp count cs,
    {< F d items,
    PRE            BUFCACHE.rep cs d *
                   [[ count <= length items /\ xparams_ok xp ]] *
                   [[ (F * array_rep xp (Synced items))%pred d ]]
    POST RET:^(cs, r)
                   BUFCACHE.rep cs d *
                   [[ (F * array_rep xp (Synced items))%pred d ]] *
                   [[ r = firstn count items ]]
    CRASH  exists cs', BUFCACHE.rep cs' d
    >} read_all xp count cs.
  Proof.
    unfold read_all.
    prestep; norm. cancel. intuition; eauto.
    step; simplen.
    step; simplen.
    apply read_all_progress; simplen.
    step; simplen.
    Unshelve. eauto.
  Qed.





  Hint Rewrite list_chunk_nil app_nil_l app_nil_r firstn_length Nat.sub_diag Nat.sub_0_r: core.

  Lemma S_minus_S : forall a b,
    a > b -> S (a - S b) = a - b.
  Proof.
    intros; omega.
  Qed.

  Lemma helper_list_chunk_app_length_gt : forall A a b sz pf e (def : A),
    list_chunk a sz def = pf ++ e :: b
    -> divup (length a) sz > length b.
  Proof.
    intros.
    erewrite <- list_chunk_length with (def := def).
    simplen.
  Qed.

  Local Hint Resolve S_minus_S helper_list_chunk_app_length_gt.

  Lemma eqlen_skipn_1: forall A (a b : list A),
    length a = S (length b) -> eqlen (skipn 1 a) b.
  Proof.
    unfold eqlen; intros.
    rewrite skipn_length; omega.
  Qed.
  Local Hint Resolve eqlen_skipn_1 : core.

  Lemma min_sub_l : forall a b,
    b > 0 -> Nat.min (a - b) a = a - b.
  Proof.
    intros; apply Nat.min_l; omega.
  Qed.

  Local Hint Resolve Nat.lt_add_pos_r Nat.lt_0_succ Nat.le_sub_l.
  Local Hint Resolve length_nil length_nil'.
  Hint Rewrite min_sub_l using omega.
  Hint Rewrite combine_updN minus_diag app_length : core.

  Lemma upd_prepend_combine : forall a b i v,
    length a = length b ->
    upd_prepend (combine a b) i v = combine (upd a i v) (upd b i (sel a i $0 :: sel b i nil)).
  Proof.
    unfold upd_prepend, valuset_list, sel, upd; t.
  Qed.

  Lemma updN_firstn_app : forall A tl hd i (v : A),
    i <= length hd
    -> updN (firstn i hd ++ tl) i v = firstn i hd ++ updN tl 0 v.
  Proof.
    destruct tl; t.
    rewrite updN_oob; t.
    rewrite updN_app2; t.
    rewrite Nat.min_l; t.
  Qed.

  Lemma updN_firstn_app_cons : forall A tl hd i (v : A),
    length tl > 0 -> i <= length hd
    -> updN (firstn i hd ++ tl) i v = firstn i hd ++ v :: skipn 1 tl.
  Proof.
    intros.
    rewrite <- updN_0_skip_1 by auto.
    apply updN_firstn_app; auto.
  Qed.

  Lemma list_updN_isolate : forall A hd tl i l (x v : A),
    l = hd ++ x :: tl
    -> i = length l - S (length tl)
    -> updN l i v = hd ++ v :: tl.
  Proof.
    induction hd; t; t.
    replace (length hd + S (length tl) - length tl) with (S (length hd)) by omega.
    erewrite IHhd; eauto.
    rewrite list_isloate_len; omega.
  Qed.

  Lemma firstn_app_elem_eq' : forall A hd x tl (a : A) l,
      hd ++ x :: tl = a :: l
   -> firstn (length hd) (a :: l) ++ [x] = a :: firstn (length hd) l.
  Proof.
    induction hd; t; inversion H; auto.
    case_eq (hd ++ x :: tl); intros.
    apply eq_sym in H0; contradict H0.
    apply app_cons_not_nil.
    erewrite IHhd; eauto.
  Qed.

  Lemma firstn_app_elem_eq : forall A l i tl hd (x : A),
    l = hd ++ x :: tl
    -> i = length l - S (length tl)
    -> firstn i l ++ [x] = firstn (S i) l.
  Proof.
    t; t.
    replace (length hd + S (length tl) - S (length tl)) with (length hd) by omega.
    case_eq (hd ++ x :: tl); intros.
    apply eq_sym in H; contradict H.
    apply app_cons_not_nil.
    eapply firstn_app_elem_eq'; eauto.
  Qed.


  Lemma helper_list_chunk_isolate_len : forall prefix lst' new elem,
    prefix ++ elem :: lst' = list_chunk new items_per_val item0
    -> divup (length new) items_per_val > length lst'.
  Proof.
    intros.
    erewrite <- list_chunk_length.
    rewrite <- H.
    rewrite list_isloate_len.
    omega.
  Qed.
  Local Hint Resolve helper_list_chunk_isolate_len.

  Lemma write_all_progress_length : forall A (a b c: list A) n,
    length a = n
    -> length a > length b
    -> length c = S (length b)
    -> n - S (length b) + S (length b) = length (firstn (S (n - S (length b))) a) + length (skipn 1 c).
  Proof.
    intros.
    rewrite firstn_length.
    rewrite Nat.min_l by omega.
    rewrite skipn_length; omega.
  Qed.

  Lemma array_unify : forall A (a b : list A) s k,
    a = b -> array s a k =p=> array s b k.
  Proof.
    intros; subst; auto.
  Qed.

  Lemma write_all_progress : forall ix xp chunks tail prefix new lst' vs blocks elem,
   length new ≤ # (RALen xp) * items_per_val
   -> goodSize addrlen (# (RALen xp) * items_per_val)
   -> length tail = S (length lst')
   -> length vs = length (firstn ix chunks ++ tail)
   -> chunks = list_chunk new items_per_val item0
   -> prefix ++ elem :: lst' = chunks
   -> ix = divup (length new) items_per_val - S (length lst')
   -> blocks = (map block2val (firstn ix chunks ++ tail))
   -> upd_prepend (combine blocks vs) $ (ix) (block2val elem)
       = combine (map block2val ((firstn (S ix) chunks) ++ (skipn 1 tail)))
                 (upd vs ($ ix) ((sel blocks ($ ix) $0) :: (sel vs ($ ix) nil))).
  Proof.
    intros.
    rewrite upd_prepend_combine by simplen.
    f_equal; eauto.
    unfold upd, sel; simplen.
    rewrite <- map_updN.
    f_equal.
    rewrite updN_firstn_app_cons by simplen.
    rewrite <- cons_nil_app.
    f_equal.
    erewrite firstn_app_elem_eq; simplen.
  Qed.
  
  
  (** write items from the beginning, 
      slots following the items will be cleared *)
  Definition write_all T xp (items: itemlist) cs rx : prog T :=
    let chunks := list_chunk items items_per_val item0 in
    let^ (cs, _) <- ForEach ck rest chunks
      Ghost [ crash F ]
      Loopvar [ cs ix ]
      Continuation lrx
      Invariant
        exists d' tail, BUFCACHE.rep cs d' *
        [[ ix = length chunks - length rest /\ eqlen tail rest  ]] *
        [[ (F * unsync_array (RAStart xp) 
                (map block2val ((firstn ix chunks) ++ tail)))%pred d' ]]
      OnCrash crash
      Begin
        cs <- BUFCACHE.write_array (RAStart xp) ($ ix) (block2val ck) cs;
        lrx ^(cs, S ix)
      Rof ^(cs, 0);
    rx cs.


  Theorem write_all_ok : forall xp new cs,
    {< F d,
    PRE            exists old, BUFCACHE.rep cs d *
                   [[ length old = length new /\ xparams_ok xp ]] *
                   [[ length new <= # (RALen xp) * items_per_val ]] *
                   [[ Forall Rec.well_formed new ]] *
                   [[ (F * array_rep xp (Synced old))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp (Unsync new))%pred d' ]]
    CRASH  exists cs d, BUFCACHE.rep cs d
    >} write_all xp new cs.
  Proof.
    unfold write_all.
    step; simplen.
    step; simplen.
    step; simplen.
    apply array_unify; eapply write_all_progress; eauto.
    simplen; apply write_all_progress_length; simplen.
    step; rewrite firstn_oob; simplen.
    Unshelve. eauto.
  Qed.


  (** sync all items *)
  Definition sync_all T xp count cs rx : prog T :=
    let nr := divup count items_per_val in
    let^ (cs) <- ForN i < nr
    Ghost [ crash F blocks ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d' vs, BUFCACHE.rep cs d' *
      [[ (F * array (RAStart xp) (combine blocks vs) $1  )%pred d' ]] *
      [[ length blocks = nr /\ length vs = nr ]] *
      [[ forall k, k < i -> selN vs k nil = nil ]]
    OnCrash   crash
    Begin
      cs <- BUFCACHE.sync_array (RAStart xp) ($ i) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.


  Lemma wplus_unit_r : forall a : addr, a ^+ $0 = a.
  Proof.
    intros; ring.
  Qed.
  Hint Rewrite wplus_unit_r : core.


  Lemma selN_repeat_eq : forall A n l def (v : A),
    length l = n
    -> (forall i, i < n -> selN l i def = v)
    -> l = repeat v n.
  Proof.
    induction n; t.
    destruct l.
    inversion H.
    pose proof (H0 0 (Nat.lt_0_succ n)) as Hx.
    simpl in Hx; subst.
    erewrite <- IHn; t.
    apply (H0 (S i)); omega.
  Qed.
  Local Hint Resolve selN_repeat_eq.

  Lemma sync_all_progress : forall F blocks vs m st,
    length vs = length blocks
    -> F * array st (upd_sync (combine blocks vs) m ($ 0, nil)) $1
     =p=> F * array st (combine blocks (upd vs m nil)) $1.
  Proof.
    intros; cancel.
    apply array_unify.
    unfold upd_sync, sel, upd; intros.
    rewrite selN_combine by auto; simpl.
    rewrite <- combine_updN.
    rewrite updN_selN_eq; simplen.
  Qed.

  Lemma sync_all_progress_length: forall k m (vs : list (list valu)),
    k < S m  -> m < length vs
    -> (forall i, i < m -> selN vs i nil = nil)
    -> (selN (updN vs m nil) k nil) = nil.
  Proof.
    intros.
    destruct (Nat.eq_dec k m); simplen.
    rewrite selN_updN_ne; simplen.
    apply H1; omega.
  Qed.


  Theorem sync_all_ok : forall xp count cs,
    {< F d items,
    PRE            BUFCACHE.rep cs d * [[ xparams_ok xp ]] *
                   [[ length items = count ]] *
                   [[ (F * array_rep xp (Unsync items))%pred d ]]
    POST RET: cs
                   exists d', BUFCACHE.rep cs d' *
                   [[ (F * array_rep xp (Synced items))%pred d' ]]
    CRASH  exists cs d, BUFCACHE.rep cs d
    >} sync_all xp count cs.
  Proof.
    unfold sync_all.
    prestep; norm'l.
    autounfold with hoare_unfold in *; simpl.
    destruct_lifts; cancel.
    simplen. simplen. simplen.
    step; simplen.

    prestep; norm. cancel. intuition; subst; auto.
    pred_apply; apply sync_all_progress; simplen.
    simplen.
    apply sync_all_progress_length; simplen.

    step.
    apply array_unify; f_equal; simplen.
    cancel.
    Unshelve. all: eauto.
  Qed.


End AsyncRecArray.


Module DISKLOG.

  (************* Log descriptors *)
  
  Definition desctype := Rec.WordF addrlen.
  Definition descblk := Rec.data desctype.
  Definition desc0 := @Rec.of_word desctype $0.

  Definition desc_per_block := Eval compute in valulen_real / addrlen.
  Definition wdesc_per_block : addr := natToWord addrlen desc_per_block.
  Definition descsz := Rec.len desctype.

  Theorem descsz_ok : valulen = wordToNat wdesc_per_block * descsz.
  Proof.
    unfold wdesc_per_block, desc_per_block, descsz, desctype.
    rewrite valulen_is.
    rewrite wordToNat_natToWord_idempotent; compute; auto.
  Qed.

  Definition descxp xp := RecArray.Build_xparams (LogDescriptor xp) (LogDescLen xp).

  Definition nr_desc xp := desc_per_block * #(LogDescLen xp).
  Definition wnr_desc xp := (natToWord addrlen desc_per_block) ^* (LogDescLen xp).

  Definition descrep xp (dlist : list addr) :=
    ([[ length dlist = nr_desc xp ]] *
     RecArray.array_item desctype wdesc_per_block descsz_ok (descxp xp) dlist)%pred.

  Definition descget T xp off mscs rx : prog T :=
    let^ (mscs, v) <- RecArray.get desctype wdesc_per_block descsz_ok
         xp (descxp xp) off mscs;
    rx ^(mscs, v).

  Definition descput T xp off v mscs rx : prog T :=
    mscs <- RecArray.put desctype wdesc_per_block descsz_ok
           xp (descxp xp) off v mscs;
    rx mscs.


  (************* Log header *)

  Definition header_type := Rec.RecF ([("length", Rec.WordF addrlen)]).
  Definition header := Rec.data header_type.
  Definition mk_header (len : nat) : header := ($ len, tt).

  Theorem header_sz_ok : Rec.len header_type <= valulen.
  Proof.
    rewrite valulen_is. apply leb_complete. compute. trivial.
  Qed.

  Lemma plus_minus_header : Rec.len header_type + (valulen - Rec.len header_type) = valulen.
  Proof.
    apply le_plus_minus_r; apply header_sz_ok.
  Qed.

  Definition hdr2valu (h : header) : valu.
    set (zext (Rec.to_word h) (valulen - Rec.len header_type)) as r.
    rewrite plus_minus_header in r.
    refine r.
  Defined.
  Arguments hdr2valu : simpl never.

  Definition valu2hdr (v : valu) : header.
    apply Rec.of_word.
    rewrite <- plus_minus_header in v.
    refine (split1 _ _ v).
  Defined.

  Lemma header_valu_id : forall h,
    valu2hdr (hdr2valu h) = h.
  Proof.
    unfold valu2hdr, hdr2valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- plus_minus_header.
    unfold zext.
    autorewrite with core.
    apply Rec.of_to_id.
    simpl; destruct h; tauto.
  Qed.
  Hint Rewrite header_valu_id.


  (****************** Log contents and states *)

  Definition log_contents := pairlist addr valu.

  Inductive state :=
  (* The log is synced on disk *)
  | Synced (l: log_contents)
  (* The log has been truncated; but the length (0) is unsynced *)
  | Truncated (old: log_contents)
  (* The log is being extended; only the content has been updated (unsynced) *)
  | ContentUpdated (old: log_contents)
  (* The log has been extended; the new contents are synced but the length is unsynced *)
  | ContentSynced (old: log_contents) (app: log_contents).


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