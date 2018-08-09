Require Import Arith.
Require Import Pred.
Require Import Mem Word.
Require Import Omega.
Require Import List ListUtils.
Require Import Bool.
Require Import Nomega.
Require Import Psatz.
Require Import Rec.
Require Import NArith.
Require Import FSLayout.
Require Import WordAuto.
Require Import Rounding Rec.
Require Export ListPred Log LogRecArray.


Import ListUtils.

Import ListNotations.

Set Implicit Arguments.


(* Bitmap allocator *)

Module Type AllocSig.

  Parameter xparams : Type.
  Parameter BMPStart : xparams -> addr.
  Parameter BMPLen   : xparams -> addr.
  Parameter xparams_ok : xparams -> Prop.

End AllocSig.

Module Type WordBMapSig.
  Parameter word_size : addr.
  Parameter word_size_ok : Nat.divide word_size valulen.
  Theorem word_size_nonzero : word_size <> 0.
  Proof.
    intro H.
    apply valulen_nonzero.
    apply Nat.divide_0_l.
    rewrite <- H.
    apply word_size_ok.
  Qed.
End WordBMapSig.

Module BmpWordSig (Sig : AllocSig) (WBSig : WordBMapSig) <: RASig.
  Import Sig.
  Definition xparams := xparams.
  Definition RAStart := BMPStart.
  Definition RALen := BMPLen.
  Definition xparams_ok := xparams_ok.
  Definition itemtype := Rec.WordF WBSig.word_size.
  Definition items_per_val := valulen / WBSig.word_size.

  Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
  Proof.
    unfold items_per_val. simpl.
    pose proof WBSig.word_size_nonzero.
    rewrite Rounding.mul_div; try omega.
    apply Nat.mod_divide; auto.
    apply WBSig.word_size_ok.
  Qed.
End BmpWordSig.

Module BmpWord (Sig : AllocSig) (WBSig : WordBMapSig).
  Module BmpSig := BmpWordSig Sig WBSig.
  Module Bmp := LogRecArray BmpSig.
  Module Defs := Bmp.Defs.

  Import Sig.

  Definition state := word Defs.itemsz.
  Definition full := wones Defs.itemsz.
  Definition state_dec := weq full.
  Definition bit := word 1.
  Definition avail : bit := $0.
  Definition inuse : bit := $1.

  Definition Avail (b : bit) : Prop := b = avail.
  Definition HasAvail (s : state) : Prop := s <> full.

  Definition bits {sz} (s : word sz) : list bit.
    apply (@Rec.of_word (Rec.ArrayF (Rec.WordF 1) sz)).
    cbn. rewrite Nat.mul_1_r.
    exact s.
  Defined.

  Lemma bits_length : forall sz (w : word sz), length (bits w) = sz.
  Proof.
    intros.
    unfold bits.
    pose proof (Rec.array_of_word_length (Rec.WordF 1)) as H.
    simpl in H.
    rewrite H.
    reflexivity.
  Qed.

  Lemma bits_cons : forall sz b (w : word sz),
    bits (WS b w) = (WS b WO) :: bits w.
  Proof.
    unfold bits, Rec.of_word. simpl. intros.
      eq_rect_simpl; repeat f_equal;
      erewrite ?whd_eq_rect_mul, ?wtl_eq_rect_mul;
      reflexivity.
  Qed.

  Definition has_avail (s : state) := if state_dec s then false else true.
  Definition avail_nonzero s i := if (addr_eq_dec i 0) then (has_avail (s ^| wone _)) else has_avail s.

  Definition ifind_byte (s : state) : option (addr * bit) :=
    ifind_list (fun (b : bit) (_ : addr) => if weq b avail then true else false) (bits s) 0.

  Definition set_bit {sz} (s : word sz) (b : bit) (index : nat) : word sz.
    set (f := @Rec.word_updN (Rec.WordF 1) sz index).
    cbn in *.
    refine (eq_rect (sz * 1) word _ sz (Nat.mul_1_r _)).
    refine (f _ b).
    rewrite Nat.mul_1_r.
    exact s.
  Defined.

  Lemma bits_of_word : forall sz (w : word sz),
    w = eq_rect _ word (@Rec.to_word (Rec.ArrayF (Rec.WordF 1) sz) (bits w)) sz (Nat.mul_1_r sz).
  Proof.
    intros.
    unfold bits.
    eq_rect_simpl.
    rewrite Rec.to_of_id.
    eq_rect_simpl.
    reflexivity.
  Qed.

  Lemma bits_set_avail : forall sz (s : word sz) v n, n < sz ->
    bits (set_bit s v n) = updN (bits s) n v.
  Proof.
    unfold set_bit, bits, bit.
    intros.
    rewrite (bits_of_word s).
    eq_rect_simpl.
    pose proof (Rec.word_updN_equiv (Rec.WordF 1)) as Ha.
    simpl in Ha.
    specialize (Ha sz n (@Rec.to_word (Rec.ArrayF (Rec.WordF 1) sz) (@bits sz s))).
    change v with (@Rec.to_word (Rec.WordF 1) v) at 1.
    rewrite Ha by auto.
    rewrite Rec.of_to_id; auto.
    unfold Rec.well_formed. split; auto.
    rewrite length_updN.
    rewrite Rec.of_to_id.
    auto using bits_length.
    apply Rec.of_word_well_formed.
  Qed.

  Definition free lxp xp bn ms :=
    let index := (bn / Defs.itemsz) in
    let^ (ms, s) <- Bmp.get lxp xp index ms;;
    let s' := set_bit s avail (bn mod Defs.itemsz) in
    ms <- Bmp.put lxp xp index s' ms;;
    Ret ms.

  (* Get the index of a byte with an available block *)
  Definition ifind_avail_nonzero lxp xp ms :=
    let^ (ms, r) <- Bmp.ifind lxp xp avail_nonzero ms;;
    match r with
    | None => Ret ^(ms, None)
    | Some (bn, nonfull) =>
      match ifind_byte (if addr_eq_dec bn 0 then (nonfull ^| wone _) else nonfull) with
      | None =>
        (* won't happen *) Ret ^(ms, None)
      | Some (i, _) =>
        Ret ^(ms, Some (bn, i, nonfull))
      end
    end.

  Definition alloc lxp xp ms :=
    let^ (ms, r) <- ifind_avail_nonzero lxp xp ms;;
    match r with
    | None =>
        Ret ^(ms, None)
    | Some (bn, index, s) =>
      let s' := set_bit s inuse index in
        ms <- Bmp.put lxp xp bn s' ms;;
        Ret ^(ms, Some (bn * Defs.itemsz + index))
    end.

  Fixpoint bits_to_freelist (l : list bit) (start : addr) : list addr :=
    match l with
    | nil => nil
    | b :: l' =>
      let freelist' := bits_to_freelist l' (S start) in
      if (weq b inuse) then freelist' else
      if (addr_eq_dec start 0) then freelist' else start :: freelist'
    end.

  Definition word_to_freelist {sz} (b : word sz) (start : addr) : list addr :=
    bits_to_freelist (bits b) start.

  Fixpoint itemlist_to_freelist' {sz} (bs : list (word sz)) (start : addr) : list addr :=
    match bs with
    | nil => nil
    | b :: bs' => (word_to_freelist b start) ++ (itemlist_to_freelist' bs' (start + sz))
    end.

  Definition itemlist_to_freelist {sz} bs := @itemlist_to_freelist' sz bs 0.

  Definition get_free_blocks lxp xp ms :=
    let^ (ms, r) <- Bmp.read lxp xp (BMPLen xp) ms;;
    Ret ^(ms, itemlist_to_freelist r).

  Definition steal lxp xp bn ms :=
    let index := (bn / Defs.itemsz) in
    let^ (ms, s) <- Bmp.get lxp xp index ms;;
    let s' := set_bit s inuse (bn mod Defs.itemsz) in
    ms <- Bmp.put lxp xp index s' ms;;
    Ret ms.

  Definition init lxp xp ms :=
    ms <- Bmp.init lxp xp ms;;
    Ret ms.

  (* init with no free objects *)
  Definition init_nofree lxp xp ms :=
    ms <- Bmp.init lxp xp ms;;
    ms <- Bmp.write lxp xp (repeat full ((BMPLen xp) * BmpSig.items_per_val)) ms;;
    Ret ms.

  Definition to_bits {sz} (l : list (word sz)) : list bit :=
    concat (map (@bits sz) l).

  Lemma to_bits_length : forall sz (l : list (word sz)),
    length (to_bits l) = length l * sz.
  Proof.
    unfold to_bits. intros.
    erewrite concat_hom_length, map_length.
    reflexivity.
    apply Forall_forall; intros.
    rewrite in_map_iff in *.
    deex. auto using bits_length.
  Qed.

  Opaque Nat.div Nat.modulo.
  Local Hint Resolve WBSig.word_size_nonzero.
  Local Hint Extern 1 (0 < _) => apply Nat.neq_0_lt_0.

  Definition freelist_bmap_equiv freelist (bmap : list bit) :=
    Forall (fun a => a < length bmap) freelist /\
    forall a, (In a freelist <-> Avail (selN bmap a inuse)).

  Definition rep V FP xp (freelist : list addr) (freepred : @pred _ addr_eq_dec V) :=
    (exists blist, Bmp.rep xp blist *
     [[ NoDup freelist ]] *
     [[ freelist_bmap_equiv freelist (to_bits blist) ]] *
     [[ freepred <=p=> listpred (fun a => exists v, a |-> v * [[ FP v ]]) freelist ]] )%pred.

  Lemma freelist_bmap_equiv_remove_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (remove addr_eq_dec a freelist) (updN bmap a inuse).
  Proof.
    unfold freelist_bmap_equiv; split; intros.
    eapply Forall_remove; intuition eauto.
    eapply Forall_impl; try eassumption.
    simpl; intros.
    rewrite length_updN; eauto.

    split; intuition; intros.

    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    exfalso; eapply remove_In; eauto.
    rewrite selN_updN_ne by auto.
    apply H3.
    eapply remove_still_In; eauto.

    destruct (addr_eq_dec a a0); subst.
    contradict H1.
    rewrite selN_updN_eq by auto.
    discriminate.
    apply remove_other_In; auto.
    apply H3.
    erewrite <- selN_updN_ne; eauto.
  Qed.

  Lemma to_bits_updN_set_avail : forall (l : list state) bn v d,
    bn / Defs.itemsz < length l ->
    to_bits (updN l (bn / Defs.itemsz) (set_bit (selN l (bn / Defs.itemsz) d) v (bn mod Defs.itemsz))) =
    updN (to_bits l) bn v.
  Proof.
    unfold to_bits.
    intros.
    pose proof (Nat.div_mod bn Defs.itemsz) as Hbn.
    rewrite Hbn at 4 by auto.
    rewrite plus_comm, mult_comm.
    rewrite updN_concat; f_equal.
    rewrite map_updN; f_equal.
    rewrite bits_set_avail.
    f_equal.
    erewrite selN_map; auto.
    apply Nat.mod_upper_bound; auto.
    apply Nat.mod_upper_bound; auto.
    apply Forall_forall; intros.
    rewrite in_map_iff in H0. deex.
    rewrite bits_length. auto.
  Qed.

  Lemma freelist_bmap_equiv_add_ok : forall bmap freelist a,
    freelist_bmap_equiv freelist bmap ->
    a < length bmap ->
    freelist_bmap_equiv (a :: freelist) (updN bmap a avail).
  Proof.
    unfold freelist_bmap_equiv; split; intuition; intros.

    constructor.
    rewrite length_updN; eauto.

    eapply Forall_impl; try eassumption.
    simpl; intros.
    rewrite length_updN; eauto.

    destruct (addr_eq_dec a a0); subst.
    rewrite selN_updN_eq by auto.
    unfold Avail; auto.
    rewrite selN_updN_ne by auto.
    apply H2.
    inversion H; congruence.

    destruct (addr_eq_dec a a0); subst; simpl; auto.
    right; apply H2.
    erewrite <- selN_updN_ne; eauto.
  Qed.

  Lemma is_avail_in_freelist : forall a bmap freelist,
    freelist_bmap_equiv freelist bmap ->
    Avail (selN bmap a inuse) ->
    a < length bmap ->
    In a freelist.
  Proof.
    unfold freelist_bmap_equiv, Avail.
    intros; apply H; auto.
  Qed.

  Lemma bits_len_rewrite : forall xp, BmpSig.RALen xp * BmpSig.items_per_val * Defs.itemsz = BMPLen xp * valulen.
  Proof.
    intros.
    unfold BmpSig.RALen.
    rewrite BmpSig.blocksz_ok.
    cbn [Rec.len BmpSig.itemtype].
    auto using mult_assoc.
  Qed.

  Lemma bmap_rep_length_ok1 : forall F xp blist d a,
    a < length (to_bits blist) ->
    (F * Bmp.rep xp blist)%pred d ->
    a < BMPLen xp * valulen.
  Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H0.
    eapply lt_le_trans; eauto.
    rewrite to_bits_length.
    setoid_rewrite H6.
    rewrite bits_len_rewrite; auto.
  Qed.

  Lemma bmap_rep_length_ok2 : forall F xp bmap d a,
    (F * Bmp.rep xp bmap)%pred d ->
    a < BMPLen xp * valulen ->
    a / Defs.itemsz < length bmap.
  Proof.
    unfold Bmp.rep, Bmp.items_valid; intros.
    destruct_lift H.
    apply Nat.div_lt_upper_bound; auto.
    setoid_rewrite H6.
    rewrite mult_comm.
    rewrite bits_len_rewrite.
    auto.
  Qed.

  Lemma bits_rep_bit : forall n x, bits (rep_bit n x) = repeat x n.
  Proof.
    induction n; intros; simpl.
    reflexivity.
    rewrite bits_cons.
    shatter_word x.
    simpl.
    congruence.
  Qed.

  Lemma to_bits_set_bit : forall sz i ii (bytes : list (word sz)) v d,
    i < length bytes ->
    ii < sz ->
    to_bits (updN bytes i (set_bit (selN bytes i d) v ii)) =
    updN (to_bits bytes) (i * sz + ii) v.
  Proof.
    intros.
    unfold to_bits.
    rewrite plus_comm.
    rewrite updN_concat; auto.
    rewrite map_updN.
    erewrite selN_map by auto.
    rewrite bits_set_avail by auto.
    reflexivity.
    apply Forall_forall.
    intros.
    rewrite in_map_iff in *.
    deex; subst.
    apply bits_length.
  Qed.

  Lemma bound_offset : forall a b c n,
    a < b -> c < n ->
    a * n + c < b * n.
  Proof.
    intros.
    apply Rounding.div_lt_mul_lt.
    omega.
    rewrite Nat.div_add_l by omega.
    rewrite Nat.div_small by omega.
    omega.
  Qed.

  Theorem selN_to_bits : forall sz n l d,
    sz <> 0 ->
    selN (to_bits l) n d = selN (bits (selN l (n / sz) (rep_bit sz d))) (n mod sz) d.
  Proof.
    intros.
    destruct (lt_dec n (sz * length l)).
    unfold to_bits.
    erewrite <- selN_selN_hom; try (rewrite ?map_length, ?wbits_length; eauto).
    erewrite selN_map; auto.
    apply Nat.div_lt_upper_bound; auto.
    apply Forall_map, Forall_forall; intros.
    rewrite bits_length; auto.
    rewrite selN_oob.
    rewrite selN_oob with (n := _ / _).
    rewrite bits_rep_bit.
    rewrite repeat_selN'; auto.
    apply Nat.div_le_lower_bound; solve [auto | omega].
    rewrite to_bits_length, mult_comm. omega.
  Qed.

  Lemma avail_nonzero_is_avail : forall bmap i ii b d d',
    i < length bmap ->
    ifind_byte (selN bmap i d') = Some (ii, b) ->
    Avail (selN (to_bits bmap) (i * Defs.itemsz + ii) d).
  Proof.
    unfold avail_nonzero; intros.
    unfold Avail.
    apply ifind_list_ok_bound in H0 as H1; simpl in H1.
    rewrite bits_length in *.
    rewrite selN_to_bits by auto.
    rewrite Nat.div_add_l by auto.
    rewrite Nat.div_small by auto.
    rewrite Nat.add_0_r.
    rewrite plus_comm.
    rewrite Nat.mod_add by auto.
    rewrite Nat.mod_small by auto.
    apply ifind_list_ok_cond in H0 as H2.
    simpl in *.
    destruct weq; subst; try congruence.
    eapply ifind_list_ok_item in H0.
    simpl in *.
    rewrite Nat.sub_0_r in *.
    erewrite selN_inb with (d1 := d') in H0.
    apply H0.
    auto.
  Qed.

  Lemma bits_wor_wone : forall sz (w : word (S sz)),
    bits (w ^| wone _) = inuse :: bits (wtl w).
  Proof.
    intros.
    destruct (shatter_word_S w); repeat deex.
    rewrite wor_wone.
    rewrite bits_cons.
    reflexivity.
  Qed.

  Lemma avail_nonzero_first_is_avail : forall bmap ii b d d',
    length bmap > 0 ->
    ifind_byte (selN bmap 0 d' ^| wone _) = Some (ii, b) ->
    Avail (selN (to_bits bmap) ii d).
  Proof.
    unfold ifind_byte.
    unfold Defs.itemsz. simpl.
    generalize (WBSig.word_size_nonzero).
    generalize WBSig.word_size.
    unfold avail_nonzero; intros.
    unfold Avail.
    denote (ifind_list _ _ _ = _) as Hl.
    apply ifind_list_ok_bound in Hl as ?; simpl in *.
    rewrite bits_length in *.
    rewrite selN_to_bits by auto.
    rewrite Nat.div_small by auto.
    rewrite Nat.mod_small by auto.
    apply ifind_list_ok_cond in Hl as ?.
    simpl in *.
    destruct weq; subst; try congruence.
    eapply ifind_list_ok_item in Hl as ?.
    simpl in *.
    rewrite Nat.sub_0_r in *.
    destruct n; try congruence.
    rewrite bits_wor_wone in *.
    destruct ii; simpl in H0.
    compute [selN inuse avail natToWord mod2] in *. congruence.
    match goal with |- context [selN ?l 0 ?d] =>
      rewrite selN_inb with (d1 := d') (d2 := d) in H3;
      pose proof (shatter_word_S (selN l 0 d)); repeat deex
    end.
    denote (selN _ _ _ = _) as Hx.
    rewrite Hx in *.
    rewrite bits_cons.
    simpl in *.
    erewrite selN_inb by (rewrite bits_length; omega). eauto.
    Unshelve.
    all : eauto; solve [exact nil | exact None].
  Qed.

  Lemma ifind_byte_first_not_zero : forall (w : state) b,
    ifind_byte (w ^| wone _) = Some (0, b) -> False.
  Proof.
    unfold ifind_byte, state.
    generalize (WBSig.word_size_nonzero).
    unfold Defs.itemsz. simpl.
    generalize WBSig.word_size.
    intros n H' w b H.
    eapply ifind_list_ok_cond in H as Ha.
    eapply ifind_list_ok_item in H as Hb.
    cbn in *.
    destruct n; try congruence.
    rewrite bits_wor_wone in *.
    simpl in *.
    destruct weq; compute in *; congruence.
    Unshelve. eauto.
  Qed.

  Local Hint Resolve avail_nonzero_is_avail avail_nonzero_first_is_avail ifind_byte_first_not_zero.

  Lemma avail_item0 : forall n d, n < Defs.itemsz -> Avail (selN (bits Bmp.Defs.item0) n d).
  Proof.
    unfold Bmp.Defs.item0, Defs.itemsz, BmpSig.itemtype.
    simpl.
    generalize WBSig.word_size.
    induction n; simpl.
    intros. inversion H.
    intros.
    unfold Rec.of_word.
    fold Nat.mul.
    eq_rect_simpl.
    rewrite whd_eq_rect_mul.
    compute [natToWord].
    erewrite wtl_eq_rect_mul.
    destruct n0; [reflexivity | apply IHn].
    omega.
  Qed.

  Lemma freelist_bmap_equiv_init_ok : forall xp,
    freelist_bmap_equiv (seq 0 (BMPLen xp * valulen))
      (to_bits (repeat Bmp.Defs.item0 (BmpSig.RALen xp * BmpSig.items_per_val))).
  Proof.
    unfold freelist_bmap_equiv; intuition; intros.
    - eapply Forall_forall.
      intros.
      eapply in_seq in H.
      rewrite to_bits_length.
      rewrite repeat_length.
      rewrite bits_len_rewrite. omega.
    - rewrite selN_to_bits by auto.
      rewrite repeat_selN; auto.
      rewrite avail_item0.
      unfold Avail; auto.
      apply Nat.mod_upper_bound; auto.
      eapply in_seq in H.
      apply Nat.div_lt_upper_bound; auto.
      rewrite mult_comm, bits_len_rewrite.
      intuition idtac.
    - apply in_seq; intuition.
      destruct (lt_dec a (BMPLen xp * valulen)); try omega.
      rewrite selN_oob in *.
      cbv in *; congruence.
      rewrite to_bits_length.
      rewrite repeat_length.
      rewrite bits_len_rewrite.
      omega.
  Qed.

  Lemma bits_to_freelist_bound: forall l start,
    let freelist := bits_to_freelist l start in
    forall x, In x freelist -> start <= x < start + (length l).
  Proof.
    split; generalize dependent start;
      induction l; cbn; intuition.
    all: repeat match goal with
    | _ => omega
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
  Qed.

  Lemma bits_to_freelist_nodup : forall l start,
    NoDup (bits_to_freelist l start).
  Proof.
    induction l; cbn; intros.
    constructor.
    repeat match goal with
    |- context [if ?x then _ else _] => destruct x; subst
    end; auto.
    constructor; auto.
    intro.
    apply bits_to_freelist_bound in H. omega.
  Qed.

  Lemma bits_to_freelist_no_zero : forall l start,
    let freelist := bits_to_freelist l start in
    ~In 0 freelist.
  Proof.
    induction l; cbn; intuition.
    repeat match goal with
    | _ => omega
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
  Qed.

  Lemma bits_to_freelist_spec : forall l start,
    let freelist := bits_to_freelist l start in
    forall i, (start + i <> 0) -> In (start + i) freelist <-> selN l i inuse = avail.
  Proof.
    unfold bit in *.
    induction l; cbn; intuition.
    cbv in *; congruence.
    destruct i;
    repeat match goal with
    | _ => omega
    | _ => solve [auto]
    | [H: context [_ + S _] |- _] => rewrite <- plus_Snm_nSm in H
    | [H: context [if ?x then _ else _] |- _ ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [H: In _ _ |- _] => apply IHl in H
    end.
    apply bits_to_freelist_bound in H0. omega.
    shatter_word a. destruct x; cbv in *; congruence.
    shatter_word a. destruct x; cbv in *; congruence.
    destruct i;
    repeat match goal with
    | _ => omega
    | _ => solve [auto | cbv in *; congruence]
    | _ => rewrite <- plus_Snm_nSm
    | [|- context [if ?x then _ else _] ] => destruct x; subst
    | [H: In _ (_ :: _) |- _] => destruct H; subst
    | [|- In _ _ ] => apply IHl
    end.
    autorewrite with core. intuition.
    right. rewrite IHl; auto. omega.
  Qed.

  Lemma itemlist_to_freelist'_bound: forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    forall x, In x freelist -> start <= x < start + length (to_bits bs) /\ x > 0.
  Proof.
    induction bs; rewrite ?to_bits_length in *; cbn; intuition.
    apply in_app_or in H. destruct H.
    apply bits_to_freelist_bound in H. omega.
    apply IHbs in H. omega.
    apply in_app_or in H. destruct H.
    apply bits_to_freelist_bound in H.
    rewrite bits_length in *. enough (length bs * sz >= 0). omega.
    apply Nat.mul_nonneg_nonneg; omega.
    apply IHbs in H. omega.
    apply in_app_or in H. destruct H.
    destruct x; try omega.
    apply bits_to_freelist_no_zero in H. intuition.
    apply IHbs in H. omega.
  Qed.

  Lemma itemlist_to_freelist'_spec: forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    forall i, (start + i <> 0) -> In (start + i) freelist <-> selN (to_bits bs) i inuse = avail.
  Proof.
    induction bs; cbn; intuition.
    cbv in *; congruence.
    destruct (in_dec addr_eq_dec (start + i) (word_to_freelist a start)) as [H' | H'].
    apply bits_to_freelist_bound in H' as ?.
    apply bits_to_freelist_spec in H'; auto.
    rewrite selN_app1; auto; omega.
    apply in_app_or in H0 as Ha. destruct Ha as [Ha | Ha]; intuition.
    apply itemlist_to_freelist'_bound in Ha as ?.
    replace (start + i) with ((start + sz) + (i - sz)) in H by omega.
    apply IHbs in H.
    rewrite selN_app2; rewrite bits_length.
    rewrite <- H in *.
    replace (start + sz + (i - sz)) with (start + i) in * by omega; auto.
    omega.
    destruct (lt_dec i (length (bits a))).
    rewrite selN_app1 in * by omega.
    rewrite <- bits_to_freelist_spec in *; eauto.
    eapply in_app_iff. right.
    rewrite selN_app2 in * by omega.
    rewrite bits_length in *.
    replace (start + i) with ((start + sz) + (i - sz)) in * by omega.
    rewrite IHbs; eauto.
  Qed.
(* TODO move this *)
  Lemma nodup_app: forall T (l1 l2 : list T),
    NoDup l1 -> NoDup l2 ->
    (forall x, In x l1 -> ~In x l2) ->
    (forall x, In x l2 -> ~In x l1) ->
    NoDup (l1 ++ l2).
  Proof.
    induction l1; cbn; intros; auto.
    inversion H; subst.
    constructor.
    rewrite in_app_iff.
    specialize (H1 a) as ?. intuition.
    apply IHl1; intuition eauto.
  Qed.

  Lemma itemlist_to_freelist'_nodup : forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    NoDup freelist.
  Proof.
    induction bs; cbn; intros.
    constructor.
    apply nodup_app; intuition eauto using bits_to_freelist_nodup.
    apply itemlist_to_freelist'_bound in H0.
    apply bits_to_freelist_bound in H.
    rewrite bits_length in *. omega.
    apply itemlist_to_freelist'_bound in H.
    apply bits_to_freelist_bound in H0.
    rewrite bits_length in *. omega.
  Qed.

  Lemma itemlist_to_freelist'_no_zero : forall sz (bs : list (word sz)) start,
    let freelist := itemlist_to_freelist' bs start in
    ~In 0 freelist.
  Proof.
    induction bs; cbn; intuition.
    apply in_app_or in H. intuition eauto.
    eapply bits_to_freelist_no_zero; eauto.
  Qed.

  Lemma itemlist_to_freelist_bound: forall sz (bs : list (word sz)),
    let freelist := itemlist_to_freelist bs in
    forall x, In x freelist -> x < length (to_bits bs).
  Proof.
    cbn; unfold itemlist_to_freelist; intros.
    replace x with (0 + x) in H by omega.
    eapply itemlist_to_freelist'_bound in H. omega.
  Qed.

  Lemma itemlist_to_freelist_spec: forall sz (bs : list (word sz)),
    let freelist := itemlist_to_freelist bs in
    forall i, i <> 0 -> In i freelist <-> selN (to_bits bs) i inuse = avail.
  Proof.
    cbn; unfold itemlist_to_freelist; intros.
    replace i with (0 + i) in * by omega.
    auto using itemlist_to_freelist'_spec.
  Qed.

  Lemma itemlist_to_freelist_nodup: forall sz bs,
    let freelist := @itemlist_to_freelist sz bs in
    NoDup freelist.
  Proof.
    intros.
    apply itemlist_to_freelist'_nodup.
  Qed.

  Lemma itemlist_to_freelist_no_zero: forall sz bs,
    let freelist := @itemlist_to_freelist sz bs in
    ~In 0 freelist.
  Proof.
    intros.
    apply itemlist_to_freelist'_no_zero.
  Qed.

  Lemma freelist_bmap_equiv_itemlist_to_freelist_spec: forall sz (bs : list (word sz)) freelist,
    NoDup freelist ->
    freelist_bmap_equiv freelist (to_bits bs) ->
    permutation addr_eq_dec (itemlist_to_freelist bs) (remove addr_eq_dec 0 freelist).
  Proof.
    cbv [permutation freelist_bmap_equiv Avail]; intuition.
    pose proof (itemlist_to_freelist_nodup bs).
    rewrite (NoDup_count_occ addr_eq_dec) in *.
    pose proof count_occ_In as Hc. unfold gt in Hc.
    repeat match goal with
    | H: context [count_occ] |- _ => specialize (H x)
    end.
    destruct (in_dec addr_eq_dec 0 freelist).
    - destruct (addr_eq_dec 0 x); subst.
      rewrite count_occ_remove_eq.
      apply count_occ_not_In.
      apply itemlist_to_freelist_no_zero.
      repeat rewrite count_occ_remove_ne by auto.
      destruct (zerop (count_occ addr_eq_dec freelist x)) as [Ha | Ha];
      destruct (zerop (count_occ addr_eq_dec (itemlist_to_freelist bs) x)) as [Hb | Hb]; try omega.
      all: rewrite <- count_occ_not_In, <- Hc in *.
      apply itemlist_to_freelist_spec in Hb.
      rewrite <- H2 in *. congruence.
      intro; subst.
      eapply itemlist_to_freelist_no_zero; eauto.
      destruct (addr_eq_dec x 0); subst; intuition.
      rewrite H2 in *.
      rewrite <- itemlist_to_freelist_spec in Ha by auto.
      intuition.
    - rewrite remove_not_In by auto.
      destruct (zerop (count_occ addr_eq_dec freelist x)) as [Ha | Ha];
      destruct (zerop (count_occ addr_eq_dec (itemlist_to_freelist bs) x)) as [Hb | Hb]; try omega.
      all: rewrite <- count_occ_not_In, <- Hc in *.
      apply itemlist_to_freelist_spec in Hb.
      rewrite <- H2 in *. congruence.
      intro; subst.
      eapply itemlist_to_freelist_no_zero; eauto.
      destruct (addr_eq_dec x 0); subst; intuition.
      rewrite H2 in *.
      rewrite <- itemlist_to_freelist_spec in Ha by auto.
      intuition.
  Qed.

  Hint Extern 0 (okToUnify (listpred ?prd _ ) (listpred ?prd _)) => constructor : okToUnify.

  Theorem init_ok :
    forall V FP lxp xp ms pr,
    {< F Fm m0 sm m bl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:bm', hm', RET:ms exists m' freelist freepred,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ forall bn, bn < (BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep; intros.
    step.
    step.
    safestep.

    eapply seq_NoDup.
    apply freelist_bmap_equiv_init_ok.
    eauto.
    apply in_seq; intuition.
    apply arrayN_listpred_seq_fp; auto.
    solve_hashmap_subset.
  Qed.

  Lemma full_eq_repeat : full = rep_bit Defs.itemsz inuse.
  Proof.
    unfold full.
    generalize Defs.itemsz.
    induction n; simpl; f_equal; auto.
  Qed.

  Lemma ifind_byte_inb : forall x n b,
    ifind_byte x = Some (n, b) ->
    n < Defs.itemsz.
  Proof.
    unfold ifind_byte.
    intros.
    apply ifind_list_ok_bound in H.
    rewrite bits_length in *.
    simpl in *. auto.
  Qed.

  

   Hint Resolve Forall_can_access_public Defs.items_per_val_not_0. 
  
  Theorem init_nofree_ok :
    forall V FP lxp xp ms pr,
    {< F Fm m0 sm m bl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BMPStart xp) bl) ]]] *
          [[ xparams_ok xp /\ BMPStart xp <> 0 /\ length bl = BMPLen xp ]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp) ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init_nofree lxp xp ms.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
    unfold Bmp.items_valid; intuition.
    rewrite repeat_length; auto.

    step.
    step.

    constructor.
    unfold freelist_bmap_equiv; intuition; intros.
    denote (Avail _) as Hx; unfold Avail in Hx.
    rewrite selN_to_bits in * by auto.
    rewrite full_eq_repeat, repeat_selN', bits_rep_bit, repeat_selN' in Hx.
    cbv in Hx. congruence.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    
    Unshelve.
    all: try exact avail; try exact tt.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem get_free_blocks_ok :
    forall V FP lxp xp ms pr,
    {<F Fm m0 sm m freelist freepred,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:bm', hm', RET:^(ms, r)
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm' *
          [[ ~In 0 r ]] * [[ NoDup r ]] *
          [[ permutation addr_eq_dec r (remove addr_eq_dec 0 freelist) ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} get_free_blocks lxp xp ms.
  Proof.
    unfold get_free_blocks, rep.
    step.
    step.
    step.

    eapply itemlist_to_freelist_no_zero; eauto.
    rewrite firstn_oob by (erewrite Bmp.items_length_ok; eauto).
    apply itemlist_to_freelist_nodup.
    rewrite firstn_oob by (erewrite Bmp.items_length_ok; eauto).
    apply freelist_bmap_equiv_itemlist_to_freelist_spec; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    auto.
    solve_hashmap_subset.
  Qed.   
    
Hint Resolve can_access_repeat_public_selN.

    
  Theorem steal_ok :
    forall V FP lxp xp bn ms pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ In bn freelist ]]
    POST:bm', hm', RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep. intros.
    step.

    unfold freelist_bmap_equiv in *; intuition.
    denote! (Forall _ _) as Hf; eapply Forall_forall in Hf; eauto.
    denote (Bmp.rep _ dummy) as Hr; eapply Bmp.items_length_ok in Hr.
    rewrite to_bits_length in *.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm; auto.

    assert (bn / Defs.itemsz < length dummy).
    unfold freelist_bmap_equiv in *; intuition.
    denote! (Forall _ _) as Hf; eapply Forall_forall in Hf; eauto.
    denote (Bmp.rep _ dummy) as Hr; eapply Bmp.items_length_ok in Hr.
    rewrite to_bits_length in *.
    apply Nat.div_lt_upper_bound; auto.
    rewrite mult_comm; auto.

    step.
    step.
    safestep.
   
    eapply NoDup_remove; eauto.
    rewrite to_bits_updN_set_avail by auto.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    rewrite to_bits_length.
    apply Rounding.div_lt_mul_lt; auto.

    apply piff_refl.
    denote freepred as Hp; rewrite Hp, listpred_remove.
    eassign bn; cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.
    auto.
    solve_hashmap_subset.
    solve_blockmem_subset.
    
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.
    
    rewrite <- H1; cancel.
    auto.
    solve_hashmap_subset.

  Unshelve.
    all: try exact unit.
    all: eauto.
    all: try exact nil.
    all: intros; try exact True.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem alloc_ok :
    forall V FP lxp xp ms pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]]
    POST:bm', hm', RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred') ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, ifind_avail_nonzero, rep.
    step.
    step.
    destruct a.
    destruct p, p.    
    safestep.
    
    subst; eauto.
    cancel.

    step.
    step.
    or_r; cancel.

    eapply NoDup_remove; eauto.
    rewrite to_bits_set_bit; auto.
    eapply freelist_bmap_equiv_remove_ok; eauto.
    rewrite to_bits_length; apply bound_offset; auto.
    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as Hc; auto.
    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as Hc; auto.
    apply piff_refl.
    denote freepred as Hp. rewrite Hp, listpred_remove.
    cancel.

    intros.
    assert (~ (y |->? * y |->?)%pred m'0) as Hc by apply ptsto_conflict.
    contradict Hc; pred_apply; cancel.

    eapply is_avail_in_freelist; eauto.
    destruct addr_eq_dec; subst; eauto.
    rewrite to_bits_length; apply bound_offset; auto.
    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as Hc; auto.
    rewrite Nat.eq_add_0, Nat.eq_mul_0 in *.
    intuition (subst; exfalso; try destruct addr_eq_dec; eauto).
    eapply bmap_rep_length_ok1; eauto.
    rewrite to_bits_length, length_updN.
    apply bound_offset; auto.
    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as Hc; auto.
    eapply is_avail_in_freelist; eauto.
    destruct addr_eq_dec; subst; eauto.
    rewrite to_bits_length; apply bound_offset; auto.
    denote (ifind_byte _ = Some _) as Hb.
    apply ifind_byte_inb in Hb as Hc; auto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    step.
    step.
    step.

    solve_hashmap_subset.

    step.
    step.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    auto.
    solve_hashmap_subset.
    
    Unshelve.
    all : try solve [auto | exact full].
    all : unfold EqDec; apply handle_eq_dec.
  Qed.


  Theorem free_ok :
    forall V FP lxp xp bn ms pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[ bn < (BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred) ]]] *
          [[ exists mx Fx, (Fx * freepred * bn |->?)%pred mx ]]
    POST:bm', hm', RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred') ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep.
    hoare.

    eapply bmap_rep_length_ok2; eauto.
    eapply bmap_rep_length_ok2; eauto.

    constructor; eauto.
    intro Hin.
    denote (freepred <=p=> _) as Hfp.
    denote (Fx) as Hx.
    rewrite Hfp in Hx.
    erewrite listpred_pick in Hx by eauto.
    destruct_lift Hx.
    eapply ptsto_conflict_F with (m := mx) (a := bn).
    pred_apply; cancel.

    rewrite to_bits_updN_set_avail; auto.
    apply freelist_bmap_equiv_add_ok; auto.
    rewrite to_bits_length.
    apply Rounding.div_lt_mul_lt; auto.
    eapply bmap_rep_length_ok2; eauto.
    eapply bmap_rep_length_ok2; eauto.
    eauto.
    denote (freepred <=p=> _) as Hfp. rewrite Hfp.
    cancel.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    rewrite <- H1; cancel.
    auto.
    solve_hashmap_subset.

    Unshelve.
    all: eauto.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (get_free_blocks _ _ _) _) => apply get_free_blocks_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.


  Lemma rep_impl_bn_ok: forall F V FP xp freelist freepred m bn,
    (F * @rep V FP xp freelist freepred)%pred (list2nmem m) ->
    In bn freelist -> 
    bn < (Sig.BMPLen xp) * valulen.
  Proof.
    intros.
    unfold rep in H.
    destruct_lift H.
    unfold freelist_bmap_equiv in *. intuition.
    eapply Forall_forall in H1; eauto.
    rewrite Bmp.items_length_ok_pimpl in H.
    rewrite BmpSig.blocksz_ok.
    simpl in *.
    destruct_lifts.
    rewrite to_bits_length in *.
    unfold state in *.
    cbn in *.
    rewrite H5 in *.
    rewrite mult_assoc.
    assumption.
  Qed.

  Lemma rep_impl_NoDup: forall F V FP xp freelist freepred m,
    (F * @rep V FP xp freelist freepred)%pred (list2nmem m) ->
    NoDup freelist.
  Proof.
    intros.
    unfold rep in *.
    destruct_lift H.
    unfold freelist_bmap_equiv in *; eauto.
  Qed.


  Lemma xform_rep : forall V FP xp l p,
    crash_xform (@rep V FP xp l p) <=p=> @rep V FP xp l p.
  Proof.
    unfold rep; intros; split.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    cancel.
    xform_normr.
    rewrite Bmp.xform_rep; cancel.
  Qed.

  Lemma xform_rep_rawpred : forall V xp FP l p,
    (forall a, @crash_xform addr addr_eq_dec V (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p) =p=> rep FP xp l p * [[ crash_xform p =p=> p ]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Bmp.xform_rep; cancel.
    rewrite H2.
    rewrite xform_listpred_ptsto_fp; auto.
  Qed.


End BmpWord.

Module ByteBmap <: WordBMapSig.
  Import Rec.

  Definition word_size := 8.
  Definition type := ArrayF (WordF 1) word_size.

  Theorem word_size_ok : Nat.divide word_size valulen.
  Proof.
    rewrite valulen_is.
    apply Nat.mod_divide; auto.
    unfold word_size.
    congruence.
  Qed.

  Theorem word_size_nonzero : word_size <> 0.
  Proof.
    compute; congruence.
  Qed.

End ByteBmap.



(**)
Module BmapAlloc (Sig : AllocSig) := BmpWord Sig ByteBmap.

(* BmapAlloc with a list of free items to speed up allocation *)

Module BmapAllocCache (Sig : AllocSig).

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := option (list addr).

  Record memstate := mk_memstate {
    MSLog  : LOG.memstate;
    MSCache   : BmapCacheType; 
  }.

  Definition freelist0 : BmapCacheType := None.

  Definition init lxp xp fms : prog memstate :=
    fms <- Alloc.init lxp xp fms;;
    Ret (mk_memstate fms freelist0 ).

  (* init with no free objects *)
  Definition init_nofree lxp xp ms :=
    fms <- Alloc.init_nofree lxp xp ms;;
    Ret (mk_memstate fms freelist0).

  Definition get_free_blocks lxp xp ms :=
    match (MSCache ms) with
    | Some x => Ret ^(ms, x)
    | None =>
      let^ (fms, freelist) <- Alloc.get_free_blocks lxp xp (MSLog ms);;
      Ret ^((mk_memstate fms (Some freelist)), freelist)
    end.

  Definition cache_free_block a ms :=
    match (MSCache ms) with
    | Some x => Some (a :: x)
    | None => None
    end.

  Definition alloc lxp xp (ms : memstate) :=
    let^ (ms, freelist) <- get_free_blocks lxp xp ms;;
    match freelist with
    | nil =>
      Ret ^(ms, None)
    | bn :: freelist' =>
      fms <- Alloc.steal lxp xp bn (MSLog ms);;
      Ret ^((mk_memstate fms (Some freelist')), Some bn)
    end.

  Definition free lxp xp bn ms :=
    fms <- Alloc.free lxp xp bn (MSLog ms);;
    let cache := cache_free_block bn ms in
    Ret (mk_memstate fms cache).

  Definition steal lxp xp bn (ms:memstate) :=
    fms <- Alloc.steal lxp xp bn (MSLog ms) ;;
    Ret (mk_memstate fms freelist0).

  Definition cache_rep (freelist : list addr) cache :=
    forall cfreelist, cache = Some cfreelist ->
    ~In 0 cfreelist /\ NoDup cfreelist /\
    permutation addr_eq_dec (remove addr_eq_dec 0 freelist) cfreelist.

  Definition rep V FP xp freelist (freepred : @pred _ addr_eq_dec V) ms :=
    (Alloc.rep FP xp freelist freepred *
    [[ cache_rep freelist (MSCache ms) ]])%pred.

  Fact cache_rep_freelist0: forall freelist, cache_rep freelist freelist0.
  Proof.
    cbv. congruence.
  Qed.

  Hint Resolve cache_rep_freelist0.

  Lemma cache_rep_remove_cons: forall freelist n cache',
    cache_rep freelist (Some (n :: cache')) ->
    cache_rep (remove addr_eq_dec n freelist) (Some cache').
  Proof.
    unfold cache_rep. intros.
    inversion H0; subst.
    specialize (H _ (eq_refl)). intuition.
    inversion H; auto.
    destruct (addr_eq_dec 0 n); subst.
    cbn in *; intuition auto.
    rewrite remove_comm.
    erewrite <- remove_not_In with (l := cfreelist) (a := n).
    erewrite <- remove_cons with (l := cfreelist).
    apply permutation_remove; auto.
    inversion H; auto.
  Qed.

  Lemma cache_rep_add_cons: forall freelist x cache,
    cache_rep freelist (Some cache) ->
    x <> 0 -> ~In x cache ->
    cache_rep (x :: freelist) (Some (x :: cache)).
  Proof.
    unfold cache_rep. intros.
    specialize (H _ eq_refl).
    inversion H2; subst.
    intuition.
    destruct H4; auto.
    constructor; auto.
    rewrite remove_cons_neq by auto.
    auto using permutation_cons.
  Qed.

  Lemma cache_rep_in: forall bn freelist cache,
    cache_rep freelist (Some cache) ->
    bn <> 0 ->
    In bn freelist <-> In bn cache.
  Proof.
    unfold cache_rep. intros.
    specialize (H _ eq_refl). intuition.
    rewrite count_occ_In.
    rewrite <- H3.
    rewrite count_occ_remove_ne by auto.
    rewrite <- count_occ_In. auto.
    rewrite count_occ_In.
    erewrite <- count_occ_remove_ne by eauto.
    rewrite H3.
    rewrite <- count_occ_In. auto.
  Qed.

  Lemma cache_rep_none: forall freelist,
    cache_rep freelist None.
  Proof.
    cbv [cache_rep]. intros. congruence.
  Qed.

  Hint Resolve cache_rep_none.

  Ltac apply_cache_rep := match goal with
    | Hm: MSCache _ = _, H: cache_rep _ _ |- _ =>
      rewrite ?Hm in *; specialize (H _ eq_refl) as ?; intuition
    end.

  Theorem init_ok :
    forall V FP lxp xp ms pr,
    {< F Fm m0 sm m bl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:bm', hm', RET:ms exists m' freepred freelist,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp freelist freepred ms) ]]] *
          [[ forall bn, bn < (Sig.BMPLen xp) * valulen -> In bn freelist ]] *
          [[ forall dl, length dl = ((Sig.BMPLen xp) * valulen)%nat ->
               Forall FP dl ->
               arrayN (@ptsto _ _ _) 0 dl =p=> freepred ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep; intros.
    step.
    step.
    safestep.
    auto.
    eauto.
    solve_hashmap_subset.
  Qed.

  Theorem init_nofree_ok :
    forall V FP lxp xp ms pr,
    {< F Fm m0 sm m bl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (Sig.BMPStart xp) bl) ]]] *
          [[ Sig.xparams_ok xp /\ Sig.BMPStart xp <> 0 /\ length bl = Sig.BMPLen xp ]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp nil emp ms) ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init_nofree lxp xp ms.
  Proof.
    unfold init_nofree, rep; intros.
    safestep.
    step.
    step.
    solve_hashmap_subset.
  Qed.

  Theorem get_free_blocks_ok :
    forall V FP lxp xp (ms:memstate) pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    POST:bm', hm', RET:^(ms, r)
          [[ MSCache ms = Some r ]] *
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm' hm' *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} get_free_blocks lxp xp ms.
  Proof.
    unfold get_free_blocks, rep.
    hoare.

    rewrite Heqb. auto.

    unfold cache_rep.
    intros ? Hs. inversion Hs; intuition subst; auto.
    auto using permutation_comm.
    solve_hashmap_subset.
  Qed.

  Hint Extern 0 ({{_|_}} Bind (get_free_blocks _ _ _) _) => apply get_free_blocks_ok : prog.

  Theorem alloc_ok :
    forall V FP lxp xp ms pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]]
    POST:bm', hm', RET:^(ms,r)
          [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm' hm'
       \/ exists bn m' freepred',
          [[ r = Some bn ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred' ms) ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]] *
          [[ bn <> 0 /\ bn < (Sig.BMPLen xp) * valulen ]] *
          [[ In bn freelist ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc.
    step.
    unfold rep in *.
    safestep.
    safestep.
    or_l; cancel.

    solve_hashmap_subset.
    cancel.
    eassign Fm; cancel.
    apply_cache_rep.
    destruct (addr_eq_dec n 0); subst; cbn in *; intuition.
    rewrite cache_rep_in by eauto.
    cbn; auto.
    
    step.
    step.
    or_r. cancel; apply_cache_rep.

    eauto using cache_rep_remove_cons.
    subst; cbn in *; intuition.
    eapply Alloc.rep_impl_bn_ok with (freelist := freelist); eauto.
    eapply remove_still_In.
    eapply permutation_in; eauto using permutation_comm.
    cbn; auto.
    eapply remove_still_In.
    eapply permutation_in; eauto using permutation_comm.
    cbn; auto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Theorem free_ok :
    forall V FP lxp xp bn ms pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
          [[ bn <> 0 ]] *
          [[ bn < (Sig.BMPLen xp) * valulen ]] *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms) ]]] *
          [[ exists mx Fx, (Fx * freepred * bn |->?)%pred mx ]]
    POST:bm', hm', RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp (bn :: freelist) freepred' ms) ]]] *
          [[ forall v, FP v -> bn |-> v * freepred =p=> freepred' ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep; intros.
    safestep.
    eassign Fm; cancel.
    eauto.
    step.
    step.

    unfold cache_free_block.
    destruct MSCache eqn:?; auto.
    eapply cache_rep_add_cons; eauto.
    assert (NoDup (bn :: freelist)) as Hd by (eauto using Alloc.rep_impl_NoDup).
    inversion Hd; subst.
    erewrite <- cache_rep_in by eauto. auto.
    solve_hashmap_subset.
  Qed.

  Theorem steal_ok :
    forall V FP lxp xp bn (ms:memstate) pr,
    {< F Fm m0 sm m freelist freepred,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
          [[[ m ::: (Fm * @rep V FP xp freelist freepred ms)]]] *
          [[ In bn freelist /\ bn < (Sig.BMPLen xp) * valulen ]]
    POST:bm', hm', RET:ms exists m' freepred',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * @rep V FP xp (remove addr_eq_dec bn freelist) freepred' ms) ]]] *
          [[ freepred =p=> freepred' * (exists v, bn |-> v * [[ FP v ]]) ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep; intros.
    Opaque corr2.
    safelightstep.
    eauto.
    eauto.
    eauto.
    step.
    step.

    solve_hashmap_subset.
    eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _ _) (rep _ _ _ _ _)) => constructor : okToUnify.

  Lemma xform_rep : forall V FP xp l ms p,
    crash_xform (@rep V FP xp l ms p) <=p=> @rep V FP xp l ms p.
  Proof.
    unfold rep, Alloc.rep; intros; split.
    xform_norm.
    rewrite Alloc.Bmp.xform_rep; cancel.
    cancel.
    xform_normr.
    cancel.
    xform_normr.
    rewrite Alloc.Bmp.xform_rep; cancel.
  Qed.

  Lemma xform_rep_rawpred : forall V xp FP l ms p,
    (forall a, @crash_xform addr addr_eq_dec V (exists v, a |-> v * [[ FP v ]]) =p=> exists v, a |-> v * [[ FP v ]]) ->
    crash_xform (rep FP xp l p ms) =p=> (rep FP xp l p ms) * [[ crash_xform p =p=> p ]].
  Proof.
    unfold rep, Alloc.rep; intros.
    xform_norm.
    cancel.
    rewrite Alloc.Bmp.xform_rep; cancel.
    assumption.
    denote (_ <=p=> _) as Hp. rewrite Hp.
    rewrite xform_listpred_ptsto_fp; auto.
  Unshelve.
    all: eauto.
  Qed.

  Lemma rep_clear_mscache_ok : forall V FP bxps frees freepred lms cm,
    @rep V FP bxps frees freepred (mk_memstate lms cm) =p=>
    @rep V FP bxps frees freepred (mk_memstate lms freelist0).
  Proof.
    unfold rep; intros.
    cancel.
  Qed.

  Lemma rep_ignore_mslog_ok: forall V (FP : V -> _) xp freelist freepred log log' cache,
    rep FP xp freelist freepred (mk_memstate log cache) =
    rep FP xp freelist freepred (mk_memstate log' cache).
  Proof.
    cbv; auto.
  Qed.

  Lemma rep_clear_cache: forall V FP xp freelist freepred ms mslog,
    @rep V FP xp freelist freepred ms =p=>
    rep FP xp freelist freepred (mk_memstate mslog freelist0).
  Proof.
    unfold rep, Alloc.rep.
    cancel.
  Qed.

  Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) (rep _ ?xp _ _ _)) => apply rep_ignore_mslog_ok : okToUnify.

End BmapAllocCache.

(**)
(* Specialize for actual on-disk-block allocation *)

Module BALLOC.

  Module Sig <: AllocSig.
    Definition xparams := balloc_xparams.
    Definition BMPStart := BmapStart.
    Definition BMPLen := BmapNBlocks.

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 bytes of disk space *)
    Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAlloc Sig.
  Module Defs := Alloc.Defs.

  Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;;
    Ret r.

  Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;;
    Ret r.

  Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;;
    Ret r.

  Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;;
    Ret r.

  Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;;
    Ret r.

  Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Definition FP (x : valuset) := True.

  Definition rep xp (freeblocks : list addr) :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred)%pred.

  Definition smrep {T} (freeblocks : list addr) : @pred _ addr_eq_dec T :=
    (listpred (fun a => a |->?) freeblocks)%pred.

  Lemma listpred_seq_smrep: forall T F xp fp m l freelist,
    (F * Alloc.rep FP xp freelist fp)%pred m ->
    (LOG.arrayP 0 l =p=> fp) ->
    listpred (fun a => a |->?) (seq 0 (length l)) =p=> @smrep T freelist.
  Proof.
    unfold smrep, Alloc.rep in *.
    intros.
    destruct_lifts.
    rewrite H4 in *.

    eapply arrayN_ptsto_linked.
    eapply pimpl_trans; eauto.
    eapply listpred_pimpl_replace.
    cancel.
  Qed.

  Theorem init_ok :
    forall lxp xp ms pr,
    {< F Fm Fs m0 sm m bl dl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (Fs * listpred (fun a => a |->?) (seq 0 (length dl)))%pred sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:bm', hm', RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * rep xp freeblocks) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep; intros.
    safestep.
    unfold Sig.BMPStart; cancel.
    auto.
    safestep.
    erewrite listpred_seq_smrep in H7; eauto.
    step.

    subst.
    erewrite H13; eauto.
    solve_hashmap_subset.
    cancel.
  Qed.

  Theorem init_nofree_ok :
    forall lxp xp ms pr,
    {< F Fs Fm m0 sm m bl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ Fs sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * rep xp nil) ]]] *
          [[ (Fs * smrep nil)%pred sm ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init_nofree lxp xp ms.
  Proof.
    unfold init_nofree, rep; intros.
    step.
    step.
    step.

    subst.
    solve_hashmap_subset.
  Qed.

  Theorem steal_ok :
    forall lxp xp bn ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * rep xp freeblocks) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
          [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
          [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep, bn_valid.
    safestep.
    eassign FP; eassign freeblocks;
    eassign (Fm * dummy)%pred; cancel.
    all: eauto.
    step.
    prestep. norm. cancel.

    intuition simpl.
    pred_apply.
    denote pimpl as Hx; rewrite Hx.
    cancel; cancel.
    eassign freepred'; cancel.
    unfold smrep in *.
    rewrite listpred_remove in *|- by eauto using ptsto_conflict.
    pred_apply; cancel.
    solve_hashmap_subset.
    Unshelve. all: try exact addr_eq_dec; auto.
  Qed.


  Theorem alloc_ok :
    forall lxp xp ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[[ m ::: (Fm * rep xp freeblocks) ]]] *
           [[ (Fs * smrep freeblocks)%pred sm ]]
    POST:bm', hm', RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm' hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * bn |->? * rep xp (remove addr_eq_dec bn freeblocks)) ]]] *
           [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]] *
           [[ In bn freeblocks ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, rep, bn_valid.
    hoare.

    solve_hashmap_subset.
    match goal with
    | [ H1 : (_ =p=> ?F * _)%pred, H2 : context [ ?F ] |- _ ] => rewrite H1 in H2
    end.
    unfold smrep.
    or_r; norm. cancel.

    intuition eauto.
    pred_apply; cancel.
    eassign a3; cancel.
    pred_apply; unfold smrep.
    rewrite listpred_remove; eauto using ptsto_conflict.
    cancel.
    solve_hashmap_subset.
  Qed.

  Theorem free_ok :
    forall lxp xp bn ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks * bn |->?) ]]] *
           [[ (Fs * bn |->? * smrep freeblocks)%pred sm ]]
    POST:bm', hm', RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks)) ]]] *
           [[ (Fs * smrep (bn :: freeblocks))%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep, bn_valid.
    hoare.
    eassign (Fm * dummy0 * bn |-> (dummy0_cur, dummy0_old))%pred; cancel.
    exists (list2nmem m); pred_apply; cancel.

    unfold FP in *; eauto.
    rewrite sep_star_assoc with (p1:= Fm).
    rewrite sep_star_comm with (p1:= dummy0).
    specialize (H13 (dummy0_cur, dummy0_old) I).
    eassign freepred'. rewrite H13; cancel.
    solve_hashmap_subset.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep ?xp _) (rep ?xp _)) => constructor : okToUnify.


  Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).
  Proof.
    intros; cancel.
  Qed.

  Lemma smrep_cons: forall T l a b,
    smrep l * a |-> b =p=> @smrep T (a :: l).
  Proof.
    unfold smrep.
    cancel.
  Qed.

  Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Blockmem bm
    Hashmap hm
    Ghost [ F Fm Fs crash m0 freeblocks sm ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks)) *
                       listpred (fun a => a |->?) (skipn i l) ]]] *
      [[ (Fs * smrep (rev (firstn i l) ++ freeblocks) *
                       listpred (fun a => a |->?) (skipn i l))%pred sm ]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;;
      Ret ^(ms)
    Rof ^(ms);;
    Ret ms.


  Theorem freevec_ok :
    forall lxp xp l ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks * listpred (fun a => a |->?) l ) ]]] *
           [[ (Fs * listpred (fun a => a |->?) l * smrep freeblocks)%pred sm ]]
    POST:bm', hm', RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms sm bm' hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks)) ]]] *
           [[ (Fs * smrep (rev l ++ freeblocks))%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} freevec lxp xp l ms.
  Proof.
    unfold freevec.
    step.

    prestep; norml.
    denote Fm as Hx.
    denote smrep as Hs.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx, Hs by (rewrite skipn_length; omega).
    rewrite skipn_selN, Nat.add_0_r in Hx, Hs.

    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    destruct_lift Hs.
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eassign (listpred (fun a : addr => a |->?) (removeN (skipn m1 (n :: l)) 0) ✶ Fm)%pred;
    eassign (t, l1); cancel.
    eassign (listpred (fun a : addr => a |->?) (removeN (skipn m1 (n :: l)) 0) ✶ Fs)%pred;
    eassign dummy; cancel.

    step.
    step.

    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    rewrite smrep_cons.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    step.
    step.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    cancel.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    cancel.
    solve_hashmap_subset.
    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)).
    unfold false_pred; cancel.
    Unshelve. all: eauto; try exact tt.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.


  Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.
  Proof.
    unfold Sig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.

  Lemma bn_valid_goodSize : forall F l m xp a,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.
  Proof.
    unfold rep, bn_valid.
    unfold Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Lemma bn_valid_goodSize_pimpl : forall l xp,
    rep xp l <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply bn_valid_goodSize; eauto.
    cancel.
  Qed.

  Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
  Proof.
    unfold bn_valid; auto.
  Qed.

  Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Theorem bn_valid_roundtrip : forall xp a F l m,
    (F * rep xp l)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold rep, Alloc.rep, Alloc.Bmp.rep, Alloc.Bmp.items_valid,
       Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply bn_valid_roundtrip'; auto.
  Qed.

  Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.
  Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.

  Definition items_per_val := Alloc.BmpSig.items_per_val.


  Theorem xform_rep : forall xp l,
    crash_xform (rep xp l) =p=> rep xp l.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite Alloc.xform_rep_rawpred.
    cancel.
    auto.
    unfold FP; intros.
    eassign x.
    rewrite H2; cancel.
    intros.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.

End BALLOC.


Module BALLOCC.

  Module Sig <: AllocSig.
    Definition xparams := balloc_xparams.
    Definition BMPStart := BmapStart.
    Definition BMPLen := BmapNBlocks.

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 bytes of disk space *)
    Definition xparams_ok xp := (BmapNBlocks xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAllocCache Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := Alloc.BmapCacheType.
  Definition MSLog := Alloc.MSLog.
  Definition MSCache := Alloc.MSCache.
  Definition upd_memstate lms ms := Alloc.mk_memstate lms (Alloc.MSCache ms).
  Definition mk_memstate lms cms := Alloc.mk_memstate lms cms.

  Definition alloc lxp xp ms :=
    r <- Alloc.alloc lxp xp ms;;
    Ret r.

  Definition free lxp xp bn ms :=
    r <- Alloc.free lxp xp bn ms;;
    Ret r.

  Definition steal lxp xp bn ms :=
    r <- Alloc.steal lxp xp bn ms;;
    Ret r.

  Definition init lxp xp ms :=
    r <- Alloc.init lxp xp ms;;
    Ret r.

  Definition init_nofree lxp xp ms :=
    r <- Alloc.init_nofree lxp xp ms;;
    Ret r.

  Definition bn_valid xp bn := bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.

  Definition FP (x : valuset) := True.

  Definition rep xp (freeblocks : list addr) ms :=
    ( exists freepred, freepred * Alloc.rep FP xp freeblocks freepred ms)%pred.

  Definition smrep (freeblocks : list addr) : @pred _ addr_eq_dec bool :=
    (listpred (fun a => a |->?) freeblocks)%pred.

  Lemma listpred_seq_smrep: forall F xp fp ms m l freelist,
    (F * Alloc.rep FP xp freelist fp ms)%pred m ->
    (LOG.arrayP 0 l =p=> fp) ->
    listpred (fun a => a |->?) (seq 0 (length l)) =p=> smrep freelist.
  Proof.
    unfold smrep, Alloc.rep, Alloc.Alloc.rep in *.
    intros.
    destruct_lifts.
    denote piff as Hp; rewrite Hp in *.

    eapply arrayN_ptsto_linked.
    eapply pimpl_trans; eauto.
    eapply listpred_pimpl_replace.
    cancel.
  Unshelve.
    all: try exact addr_eq_dec. exact unit.
  Qed.

  Lemma rep_ignore_mslog_ok: forall bxps frees lms lms' cm,
    rep bxps frees (mk_memstate lms cm) =p=>
    rep bxps frees (mk_memstate lms' cm).
  Proof.
    intros.
    unfold mk_memstate, rep.
    cancel.
  Qed.

  Lemma rep_clear_mscache_ok : forall bxps frees lms cm,
    rep bxps frees (mk_memstate lms cm) =p=>
    rep bxps frees (mk_memstate lms Alloc.freelist0).
  Proof.
    intros.
    unfold mk_memstate, rep.
    cancel.
    rewrite Alloc.rep_clear_mscache_ok.
    cancel.
  Qed.

  Theorem init_ok :
    forall lxp xp ms pr,
    {< F Fm Fs m0 sm m bl dl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 dl
                        * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ (Fs * listpred (fun a => a |->?) (seq 0 (length dl)))%pred sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp /\ length dl = ((BmapNBlocks xp) * valulen)%nat ]]
    POST:bm', hm', RET:ms exists m' freeblocks,
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * rep xp freeblocks ms) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ forall bn, bn < (BmapNBlocks xp) * valulen -> In bn freeblocks ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init lxp xp ms.
  Proof.
    unfold init, rep, MSLog; intros.
    safestep.
    unfold Sig.BMPStart; cancel.
    auto.
    safestep.
    erewrite listpred_seq_smrep in H7; eauto.
    step.
    solve_hashmap_subset.
    cancel.
  Qed.

  Theorem init_nofree_ok :
    forall lxp xp ms pr,
    {< F Fm Fs m0 sm m bl,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) ms sm bm hm *
          [[[ m ::: (Fm * arrayN (@ptsto _ _ _) (BmapStart xp) bl) ]]] *
          [[ Fs sm ]] *
          [[ (BmapNBlocks xp) <= valulen * valulen /\ BmapStart xp <> 0 ]] *
          [[ length bl = BmapNBlocks xp ]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[ (Fs * smrep nil)%pred sm ]] *
          [[[ m' ::: (Fm * rep xp nil ms) ]]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} init_nofree lxp xp ms.
  Proof.
    unfold init_nofree, rep, MSLog; intros.
    step.
    step.
    step.

    subst.
    solve_hashmap_subset.
  Qed.

  Theorem steal_ok :
    forall lxp xp bn ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
          LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
          [[[ m ::: (Fm * rep xp freeblocks ms) ]]] *
          [[ (Fs * smrep freeblocks)%pred sm ]] *
          [[ bn_valid xp bn /\ In bn freeblocks ]]
    POST:bm', hm', RET:ms exists m',
          LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
          [[[ m' ::: (Fm * bn |->? * 
           rep xp (remove addr_eq_dec bn freeblocks) ms) ]]] *
          [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} steal lxp xp bn ms.
  Proof.
    unfold steal, rep, bn_valid, MSLog.
    step.
    step.
    prestep. norm. cancel.

    intuition simpl.    
    pred_apply.
    denote pimpl as Hx; rewrite Hx.
    cancel; cancel.
    pred_apply; unfold smrep.
    rewrite listpred_remove; eauto using ptsto_conflict.
    cancel.
    solve_hashmap_subset.
    Unshelve . all: try exact addr_eq_dec; auto.
  Qed.


  Theorem alloc_ok :
    forall lxp xp ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
           [[[ m ::: (Fm * rep xp freeblocks ms) ]]] *
           [[ (Fs * smrep freeblocks)%pred sm ]]
    POST:bm', hm', RET:^(ms, r)
           [[ r = None ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm' hm'
        \/ exists bn m',
           [[ r = Some bn ]] * [[ bn_valid xp bn ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * bn |->? * 
            rep xp (remove addr_eq_dec bn freeblocks) ms) ]]] *
           [[ (Fs * bn |->? * smrep (remove addr_eq_dec bn freeblocks))%pred sm ]] *
           [[ In bn freeblocks ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} alloc lxp xp ms.
  Proof.
    unfold alloc, rep, bn_valid, MSLog.
    hoare.

    solve_hashmap_subset.
    match goal with
    | [ H1 : (_ =p=> ?F * _)%pred, H2 : context [ ?F ] |- _ ] => rewrite H1 in H2
    end.
    unfold smrep.
    or_r; norm. cancel.

    intuition eauto.
    pred_apply; cancel.
    pred_apply; unfold smrep.
    rewrite listpred_remove; eauto using ptsto_conflict.
    cancel.
    solve_hashmap_subset.
  Qed.

  Theorem free_ok :
    forall lxp xp bn ms pr,
    {< F Fm Fs m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
           [[ bn_valid xp bn ]] *
           [[[ m ::: (Fm * rep xp freeblocks ms* bn |->?) ]]] *
           [[ (Fs * bn |->? * smrep freeblocks)%pred sm ]]
    POST:bm', hm', RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep xp (bn :: freeblocks) ms) ]]] *
           [[ (Fs * smrep (bn :: freeblocks))%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} free lxp xp bn ms.
  Proof.
    unfold free, rep, bn_valid, MSLog.
    hoare.
    exists (list2nmem m); pred_apply; cancel.

    unfold FP in *; eauto.
    solve_hashmap_subset.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (init_nofree _ _ _) _) => apply init_nofree_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (steal _ _ _ _) _) => apply steal_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep ?xp _ _) (rep ?xp _ _)) => constructor : okToUnify.

  Lemma sep_star_reorder_helper : forall a b c d : (@pred _ addr_eq_dec valuset),
    ((a * b) * (c * d)) =p=> d * (a * b * c).
  Proof.
    intros; cancel.
  Qed.

  Lemma smrep_cons: forall l a b,
    smrep l * a |-> b =p=> smrep (a :: l).
  Proof.
    unfold smrep.
    cancel.
  Qed.

  Definition freevec lxp xp l ms :=
    let^ (ms) <- ForN i < length l
    Blockmem bm
    Hashmap hm
    Ghost [ F Fm Fs crash m0 sm freeblocks ]
    Loopvar [ ms ]
    Invariant
      exists m', LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm hm *
      [[[ m' ::: (Fm * rep xp (rev (firstn i l) ++ freeblocks) ms) *
                       listpred (fun a => a |->?) (skipn i l) ]]] *
      [[ (Fs * smrep (rev (firstn i l) ++ freeblocks) *
                       listpred (fun a => a |->?) (skipn i l))%pred sm ]]
    OnCrash crash
    Begin
      ms <- free lxp xp (selN l i 0) ms;;
      Ret ^(ms)
    Rof ^(ms);;
    Ret ms.


  Theorem freevec_ok :
    forall lxp xp l ms pr,
    {< F Fs Fm m0 sm m freeblocks,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLog ms) sm bm hm *
           [[ Forall (bn_valid xp) l ]] *
           [[[ m ::: (Fm * rep xp freeblocks ms * listpred (fun a => a |->?) l ) ]]] *
           [[ (Fs * listpred (fun a => a |->?) l * smrep freeblocks)%pred sm ]]
    POST:bm', hm', RET:ms exists m',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLog ms) sm bm' hm' *
           [[[ m' ::: (Fm * rep xp (rev l ++ freeblocks) ms) ]]] *
           [[ (Fs * smrep (rev l ++ freeblocks))%pred sm ]]
    CRASH:bm', hm',  LOG.intact lxp F m0 sm bm' hm'
    >} freevec lxp xp l ms.
  Proof.
    unfold freevec.
    safestep.
    eauto.
    eauto.
   
    prestep; norml.
    denote Fm as Hx.
    denote smrep as Hs.

    destruct l.
    denote (_ < _) as Hy; simpl in Hy; inversion Hy.
    rewrite listpred_isolate with (i := 0) in Hx, Hs by (rewrite skipn_length; omega).
    rewrite skipn_selN, Nat.add_0_r in Hx, Hs.

    apply sep_star_reorder_helper in Hx.
    apply pimpl_exists_r_star_r in Hx; destruct Hx as [ [? ?] ?].
    destruct_lift Hs.
    safecancel.
    rewrite selN_cons_fold; apply Forall_selN; auto.
    eassign (listpred (fun a : addr => a |->?) (removeN (skipn m1 (n :: l)) 0) ✶ Fm)%pred;
    eassign (t, l1); cancel.
    eassign (listpred (fun a : addr => a |->?) (removeN (skipn m1 (n :: l)) 0) ✶ Fs)%pred;
    eassign dummy; cancel.

    step.
    step.

    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    replace ([n]) with (rev [n]) by auto.
    rewrite <- rev_app_distr.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    rewrite removeN_0_skipn; cancel.
    rewrite selN_cons_fold.
    rewrite smrep_cons.
    rewrite app_comm_cons, <- rev_unit.
    rewrite <- firstn_S_selN by auto.
    cancel.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    solve_hashmap_subset.
    solve_blockmem_subset.

    step.
    step.

    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    cancel.
    rewrite firstn_oob by auto.
    rewrite skipn_oob by auto.
    cancel.
    solve_hashmap_subset.
    eassign (false_pred (AT:=addr)(AEQ:=addr_eq_dec)(V:=valuset)).
    unfold false_pred; cancel.
    Unshelve. all: eauto; try exact tt.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (freevec _ _ _ _) _) => apply freevec_ok : prog.


  Lemma xparams_ok_goodSize : forall xp a,
    Sig.xparams_ok xp ->
    a < (BmapNBlocks xp) * valulen ->
    goodSize addrlen a.
  Proof.
    unfold Sig.xparams_ok; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.

  Lemma bn_valid_goodSize : forall F l m ms xp a,
    (F * rep xp l ms)%pred m ->
    bn_valid xp a ->
    goodSize addrlen a.
  Proof.
    unfold rep, bn_valid.
    unfold Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Lemma bn_valid_goodSize_pimpl : forall l xp ms,
    rep xp l ms <=p=> [[ forall a, bn_valid xp a -> goodSize addrlen a ]] * rep xp l ms.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply bn_valid_goodSize; eauto.
    cancel.
  Qed.

  Lemma bn_valid_facts : forall xp bn,
    bn_valid xp bn -> bn <> 0 /\ bn < (BmapNBlocks xp) * valulen.
  Proof.
    unfold bn_valid; auto.
  Qed.

  Theorem bn_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold bn_valid; intuition.
    rewrite wordToNat_natToWord_idempotent' in H0; auto.
    eapply xparams_ok_goodSize; eauto.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Theorem bn_valid_roundtrip : forall xp a F l ms m,
    (F * rep xp l ms)%pred m ->
    bn_valid xp a ->
    bn_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold rep, Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply bn_valid_roundtrip'; auto.
  Qed.

  Lemma bn_valid_switch : forall xp1 xp2,
    BmapNBlocks xp1 = BmapNBlocks xp2 ->
    bn_valid xp1 = bn_valid xp2.
  Proof.
    unfold bn_valid; intuition; auto.
    rewrite H; auto.
  Qed.

  Definition items_per_val := Alloc.Alloc.BmpSig.items_per_val.


  Theorem xform_rep : forall xp l ms,
    crash_xform (rep xp l ms) =p=> rep xp l ms.
  Proof.
    unfold Alloc.rep, rep; intros.
    xform_norm.
    rewrite Alloc.xform_rep_rawpred.
    cancel.
    auto.
    unfold FP; intros.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.


End BALLOCC.


(* Specialize for inode allocation *)

Module IAlloc.

  Module Sig <: AllocSig.
    Definition xparams     := fs_xparams.
    Definition BMPStart xp := BmapStart (FSXPInodeAlloc xp).
    Definition BMPLen   xp := BmapNBlocks (FSXPInodeAlloc xp).

    (* should return an address that fits in addrlen (goodSize addrlen _).
       valulen * valulen supports about 2^48 inodes *)
    Definition xparams_ok xp := (BMPLen xp) <= valulen * valulen.
  End Sig.

  Module Alloc := BmapAllocCache Sig.
  Module Defs := Alloc.Defs.

  Definition BmapCacheType := Alloc.BmapCacheType.
  Definition MSLog := Alloc.MSLog.
  Definition MSCache := Alloc.MSCache.
  Definition mk_memstate := Alloc.mk_memstate.

  Definition init := Alloc.init.

  Definition alloc := Alloc.alloc.

  Definition free := Alloc.free.

  Definition rep := Alloc.rep.

  Definition ino_valid xp ino := ino < (Sig.BMPLen xp) * valulen.

  Definition init_ok := Alloc.init_ok.

  Definition alloc_ok := Alloc.alloc_ok.

  Definition free_ok := Alloc.free_ok.

  Definition items_per_val := Alloc.Alloc.BmpSig.items_per_val.

  Hint Extern 1 ({{_|_}} Bind (init _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (alloc _ _ _) _) => apply alloc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (free _ _ _ _) _) => apply free_ok : prog.
  Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) (rep _ ?xp _ _ _)) => constructor : okToUnify.

  Definition xform_rep := Alloc.xform_rep.

  Lemma xparams_ok_goodSize : forall xp ino,
    Sig.xparams_ok xp ->
    ino_valid xp ino ->
    goodSize addrlen ino.
  Proof.
    unfold Sig.xparams_ok, ino_valid; intuition.
    eapply goodSize_trans.
    eapply Nat.lt_le_incl; eauto.
    eapply goodSize_trans.
    eapply mult_le_compat_r; eauto.
    unfold goodSize.
    replace addrlen with (16 + 16 + 16 + 16) by (compute; auto).
    rewrite <- Nat.mul_1_r at 1.
    repeat apply mult_pow2_bound; try apply valulen_bound.
    apply one_lt_pow2.
  Qed.

  Lemma ino_valid_goodSize : forall V FP F l m xp a prd allocc,
    (F * @rep V FP xp l prd allocc)%pred m ->
    ino_valid xp a ->
    goodSize addrlen a.
  Proof.
    unfold rep, ino_valid.
    unfold Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Lemma ino_valid_goodSize_pimpl : forall V FP l xp p allocc,
    @rep V FP xp l p allocc <=p=> [[ forall a, ino_valid xp a -> goodSize addrlen a ]] * rep FP xp l p allocc.
  Proof.
    intros; split.
    unfold pimpl; intros.
    pred_apply; cancel.
    apply emp_star in H.
    eapply ino_valid_goodSize; eauto.
    cancel.
  Qed.

  Theorem ino_valid_roundtrip' : forall xp a,
    Sig.xparams_ok xp ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold ino_valid; intuition.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply xparams_ok_goodSize; eauto.
  Qed.

  Theorem ino_valid_roundtrip : forall V FP xp a F l m p allocc,
    (F * @rep V FP xp l p allocc)%pred m ->
    ino_valid xp a ->
    ino_valid xp (# (natToWord addrlen a)).
  Proof.
    unfold rep, Alloc.rep, Alloc.Alloc.rep, Alloc.Alloc.Bmp.rep, Alloc.Alloc.Bmp.items_valid,
       Alloc.Alloc.BmpSig.xparams_ok; intuition.
    destruct_lift H.
    apply ino_valid_roundtrip'; auto.
  Qed.

  Lemma rep_clear_cache: forall V FP xp freelist freepred ms mslog,
    @rep V FP xp freelist freepred ms =p=>
    rep FP xp freelist freepred (mk_memstate mslog Alloc.freelist0).
  Proof.
    auto using Alloc.rep_clear_cache.
  Qed.

  Hint Extern 0 (okToUnify (rep _ ?xp _ _ _) _) => unfold rep; trivial with okToUnify : okToUnify.
  Hint Extern 0 (okToUnify _ (rep _ ?xp _ _ _)) => unfold rep; trivial with okToUnify : okToUnify.

End IAlloc.
