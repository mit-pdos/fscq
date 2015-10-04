Require Import Eqdep_dec Arith Omega List.
Require Import Word WordAuto Pred GenSep Rec Prog BasicProg Hoare SepAuto Array Log.
Require Import BFile RecArray Inode.
Require Import GenSep.
Require Import GenSepN.
Require Import ListPred.
Require Import MemMatch.
Require Import FSLayout.
Require Import Bool.
Require Import Rounding.
Require Import Program.Wf.
Require Import Psatz.
Require Import ProofIrrelevance.

Set Implicit Arguments.

(* rew .. in notations for eq_rect *)
Import EqNotations.

(** BFileRec implements a record-based abstraction on top of a BFILE. Records
must be sized so that a whole number fit into a block. *)
Section RECBFILE.

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

  Theorem items_per_valu_not_0' : wordToNat items_per_valu <> 0.
  Proof.
    intros H.
    apply items_per_valu_not_0.
    apply wordToNat_inj; auto.
  Qed.

  Theorem itemlen_not_0 : Rec.len itemtype <> 0.
  Proof.
    intro H.
    unfold blocktype in blocksz_ok.
    simpl in blocksz_ok.
    rewrite H in blocksz_ok.
    rewrite valulen_is in blocksz_ok.
    rewrite <- mult_n_O in blocksz_ok.
    discriminate.
  Qed.

  Hint Resolve itemlen_not_0.
  Hint Resolve items_per_valu_not_0.
  Hint Resolve items_per_valu_not_0'.


  Definition rep_block := RecArray.rep_block blocksz_ok.
  Definition valu_to_block := RecArray.valu_to_block itemtype items_per_valu blocksz_ok.
  Definition rep_valu_id := RecArray.rep_valu_id blocksz_ok.

  (** Get the [pos]'th item in the [block_ix]'th block of inode [inum] *)
  Definition bf_get_pair T lxp ixp inum block_ix (pos : addr) mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum block_ix mscs;
    let i := Rec.of_word (Rec.word_selN #pos (valu_to_wreclen itemtype items_per_valu blocksz_ok v)) in
    rx ^(mscs, i).

  (** Get all items in the [block_ix]'th block of inode [inum] *)
  Definition bf_get_entire_block T lxp ixp inum block_ix mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum block_ix mscs;
    let ii := Rec.of_word (valu_to_wreclen itemtype items_per_valu blocksz_ok v) in
    rx ^(mscs, ii).

  (** Update the [pos]'th item in the [block_ix]'th block of inode [inum] to [i] *)
  Definition bf_put_pair T lxp ixp inum block_ix (pos : addr) i mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum block_ix mscs;
    let v' := wreclen_to_valu itemtype items_per_valu blocksz_ok
              (Rec.word_updN #pos (valu_to_wreclen itemtype items_per_valu blocksz_ok v) (Rec.to_word i)) in
    mscs <- BFILE.bfwrite lxp ixp inum block_ix v' mscs;
    rx mscs.

  Definition itemsize := Rec.len itemtype.
  Definition block_items := # items_per_valu.
  (** analogous to Bytes.bytes, an [items count] is a word with enough bits to hold [count] items. **)
  Definition items count := word (count * itemsize).

  Corollary block_items_gt_0 : block_items > 0.
  Proof.
    apply Nat.neq_0_lt_0.
    apply items_per_valu_not_0'.
  Qed.

  Corollary block_items_0_lt : 0 < block_items.
  Proof.
    apply block_items_gt_0.
  Qed.

  Hint Resolve block_items_gt_0.
  Hint Resolve block_items_0_lt.

  Corollary block_items_S_n : block_items = S (block_items - 1).
  Proof.
    assert (H := block_items_gt_0).
    omega.
  Qed.

  Definition array_item_pairs (vs : list block) : pred :=
    ([[ Forall Rec.well_formed vs ]] *
     arrayN 0 (map rep_block vs))%pred.

  Definition array_item_file file (vs : list item) : Prop :=
    exists vs_nested,
    length vs_nested = length (BFILE.BFData file) /\
    array_item_pairs vs_nested (list2nmem (BFILE.BFData file)) /\
    vs = concat vs_nested.

  Ltac split_rep H :=
    let vs_nested := fresh "vs_nested" in
    let Hrep := fresh "Hrep" in
    let Hrep1 := fresh "Hrep_len" in
    let Hrep23 := fresh "Hrep23" in
    let Hrep2 := fresh "Hrep_items" in
    let Hrep3 := fresh "Hrep_concat" in
    inversion H as [vs_nested Hrep];
    inversion Hrep as [Hrep1 Hrep23];
    inversion Hrep23 as [Hrep2 Hrep3];
    clear Hrep Hrep23.

  Ltac split_reps :=
    match goal with
    | [ H : array_item_file _ _ |- _ ] => split_rep H
    end.

  Section RepImplications.

  Lemma well_formed_length : forall (vs : list block),
    Forall Rec.well_formed vs ->
    Forall (fun sublist => length sublist = block_items) vs.
  Proof.
    intros.
    rewrite Forall_forall.
    intros.
    rewrite Forall_forall in H.
    apply H in H0.
    apply H0.
  Qed.

  Corollary block_length_is : forall x (vs : list block),
    Forall Rec.well_formed vs
    -> In x vs
    -> length x = # items_per_valu.
  Proof.
    intros.
    apply well_formed_length in H.
    rewrite Forall_forall in H.
    apply H; assumption.
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
    apply in_cons_head.
    eapply Forall_cons2.
    eassumption.
  Qed.

  Lemma block_length_fold_right_nat : forall (bl : list block),
    Forall Rec.well_formed bl ->
    length (concat bl) =
      (length bl) * block_items.
  Proof.
    intros.
    rewrite concat_length.
    rewrite fold_right_add_const by auto.
    auto.
  Qed.

  Lemma block_length_fold_right : forall (bl : list block),
    Forall Rec.well_formed bl
    -> $ (length (concat bl))
       = ($ (length bl) ^* items_per_valu)%word.
  Proof.
    intros.
    rewrite block_length_fold_right_nat by assumption.
    rewrite natToWord_mult.
    unfold block_items.
    rewrite natToWord_wordToNat; reflexivity.
  Qed.

  Lemma array_items_block_sized : forall f vs,
    array_item_file f vs ->
    length (BFILE.BFData f) * block_items = length vs.
  Proof.
    intros.
    split_reps.
    unfold array_item_pairs in Hrep_items.
    assert (length vs = length vs_nested * block_items).
    rewrite Hrep_concat.
    destruct_lift Hrep_items.
    apply block_length_fold_right_nat; assumption.
    rewrite <- Hrep_len.
    auto.
  Qed.

  Corollary array_items_num_blocks : forall f vs,
    array_item_file f vs ->
    length (BFILE.BFData f) = divup (length vs) block_items.
  Proof.
    intros.
    rewrite <- (array_items_block_sized H).
    symmetry; apply divup_mul.
    apply items_per_valu_not_0'.
  Qed.

  Lemma lt_div_mono : forall a b c,
    b <> 0 -> a < c -> a / b < c.
  Proof.
    intros.
    replace b with (S (b - 1)) by omega.
    apply Nat.div_lt_upper_bound; auto.
    simpl.
    apply le_plus_trans; auto.
  Qed.

  Lemma bfrec_bound_goodSize :
    goodSize addrlen (INODE.blocks_per_inode * #items_per_valu).
  Proof.
    unfold goodSize.
    assert (X := blocksz_ok).
    unfold blocktype in X; simpl in X.
    rewrite Nat.mul_comm in X.
    apply Nat.div_unique_exact in X; auto.
    rewrite X.

    unfold addrlen.
    eapply mult_pow2_bound_ex with (a := 10); try omega.
    compute; omega.
    apply lt_div_mono; auto.
    eapply pow2_bound_mono.
    apply valulen_bound.
    omega.
  Qed.

  Lemma bfrec_bound' : forall F m bxp ixp (inum : addr) (bl : list block) fl,
    length bl = length (BFILE.BFData (sel fl inum BFILE.bfile0))
    -> Forall Rec.well_formed bl
    -> (F * BFILE.rep bxp ixp fl)%pred m
    -> # inum < length fl
    -> length (concat bl)
          <= # (natToWord addrlen (INODE.blocks_per_inode * # items_per_valu)).
  Proof.
    intros.
    erewrite wordToNat_natToWord_idempotent'.
    subst; rewrite concat_length.
    rewrite fold_right_add_const; auto.
    apply mult_le_compat_r.
    rewrite H.
    eapply BFILE.bfdata_bound; eauto.
    apply bfrec_bound_goodSize.
  Qed.

  Lemma bfrec_bound : forall F A m bxp ixp (inum : addr) fl f l,
    array_item_file f l
    -> (A * # inum |-> f)%pred (list2nmem fl)
    -> (F * BFILE.rep bxp ixp fl)%pred m
    -> length l <= # (natToWord addrlen (INODE.blocks_per_inode * # items_per_valu)).
  Proof.
    unfold array_item_file, array_item_pairs; intros.
    repeat deex.
    destruct_lift' H.
    rewrite_list2nmem_pred.
    eapply bfrec_bound'; eauto.
  Qed.

  Lemma rep_block_inj : forall b b',
    Rec.well_formed b ->
    Rec.well_formed b' ->
    rep_block b = rep_block b' ->
    b = b'.
  Proof.
    unfold rep_block, RecArray.rep_block.
    unfold wreclen_to_valu.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite <- Rec.of_to_id with (v := b) by auto.
    rewrite <- Rec.of_to_id with (v := b') by auto.
    f_equal.
    simpl in H1.
    destruct (eq_sym blocksz_ok).
    repeat rewrite <- (eq_rect_eq_dec Nat.eq_dec) in H1.
    auto.
  Qed.

  Lemma Forall_app_iff : forall A f (l:list A) a,
    Forall f (a :: l) ->  f a /\ Forall f l.
  Proof.
    intros.
    rewrite Forall_forall in H.
    split.
    intuition.
    rewrite Forall_forall.
    intros.
    apply H.
    constructor 2.
    auto.
  Qed.

  Lemma forall_rep_block_inj : forall bs bs',
    Forall Rec.well_formed bs ->
    Forall Rec.well_formed bs' ->
    map rep_block bs = map rep_block bs' ->
    bs = bs'.
  Proof.
    induction bs; induction bs'; intros;
      auto;
      try solve [inversion H1].
    apply Forall_app_iff in H.
    apply Forall_app_iff in H0.
    inversion H1.
    f_equal; intuition.
    apply rep_block_inj; auto.
  Qed.

  Lemma vs_nested_unique : forall f vs_nested vs_nested',
    array_item_pairs vs_nested (list2nmem (BFILE.BFData f)) ->
    array_item_pairs vs_nested' (list2nmem (BFILE.BFData f)) ->
    vs_nested = vs_nested'.
  Proof.
    unfold array_item_pairs.
    intros.
    destruct_lift H.
    destruct_lift H0.
    apply list2nmem_array_eq in H.
    apply list2nmem_array_eq in H0.
    apply forall_rep_block_inj; auto.
    congruence.
  Qed.

  End RepImplications.

  (** splitting of items mirrors splitting of bytes defined in Bytes **)

  Definition icombine sz1 (is1:items sz1) sz2 (is2:items sz2) : items (sz1+sz2).
    unfold items in *.
    rewrite Nat.mul_add_distr_r.
    exact (combine is1 is2).
  Defined.

  Definition isplit1 (sz1 sz2:nat) (is: items (sz1+sz2)) : items sz1.
  Proof.
    unfold items in *.
    rewrite Nat.mul_add_distr_r in is.
    exact (split1 _ _ is).
  Defined.

  Definition isplit2 (sz1 sz2:nat) (is: items (sz1+sz2)) : items sz2.
  Proof.
    unfold items in *.
    rewrite Nat.mul_add_distr_r in is.
    exact (split2 _ _ is).
  Defined.

  Definition isplit1_dep sz sz1 sz2 (v : items sz) (H : sz = sz1 + sz2) : items sz1 :=
    isplit1 sz1 sz2 (eq_rect sz items v _ H).

  Definition isplit2_dep sz sz1 sz2 (v : items sz) (H : sz = sz1 + sz2) : items sz2 :=
    isplit2 sz1 sz2 (eq_rect sz items v _ H).

  Definition single_item (w: items 1) : word itemsize.
  Proof.
    unfold items in w.
    rewrite Nat.mul_1_l in w.
    exact w.
  Defined.

  Definition valu2items (v:valu) : items block_items.
    unfold items, itemsize.
    rewrite blocksz_ok in v.
    exact v.
  Defined.

  Definition valu2block (v:valu) :  block.
    unfold block.
    rewrite blocksz_ok in v.
    apply (@Rec.of_word blocktype v).
  Defined.

  Definition block2valu (b:block) : valu.
    unfold block in b.
    rewrite blocksz_ok.
    apply (Rec.to_word b).
  Defined.

  Lemma block_valu_inv : forall v,
    block2valu (valu2block v) = v.
  Proof.
    intros.
    unfold block2valu, valu2block.
    rewrite Rec.to_of_id.
    unfold eq_rec_r.
    unfold eq_rec.
    rewrite eq_rect_nat_double.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    reflexivity.
  Qed.

  Lemma valu_rep_id : forall v,
    rep_block (valu2block v) = v.
  Proof.
    intros.
    unfold rep_block, valu2block.
    unfold RecArray.rep_block, wreclen_to_valu.
    rewrite Rec.to_of_id.
    eq_rect_simpl.
    reflexivity.
  Qed.

  Program Fixpoint isplit_list count (w: items count) : list (word itemsize) :=
    match count with
    | O => nil
    | S count' => (single_item (isplit1_dep 1 count' w _)) :: isplit_list (isplit2_dep 1 count' w _)
    end.

  Record chunk := {
    chunk_blocknum : addr;
    chunk_boff : nat;
    chunk_bend : nat;
    (** chunk_data is a word that can hold chunk_bend - chunk_off items **)
    chunk_data: items (chunk_bend - chunk_boff);

    chunk_bend_ok : chunk_bend <= block_items;
    chunk_size_ok : chunk_boff <= chunk_bend
  }.

  (* TODO: find ck in goal automatically *)
  Ltac ck_omega ck :=
    let Hsize := fresh "Hsize" in
    let Hbend := fresh "Hbend" in
    assert (Hsize := chunk_size_ok ck);
    assert (Hbend := chunk_bend_ok ck);
    omega.

  (** if you want this fact, you can produce its proof with this function *)
  Definition chunk_boff_ok (ck:chunk) : (chunk_boff ck) <= block_items.
  Proof.
    ck_omega ck.
  Qed.

  Record rchunk := {
    rchunk_blocknum : addr;
    rchunk_boff : nat;
    rchunk_bend : nat;

    rchunk_bend_ok : rchunk_bend <= block_items;
    rchunk_size_ok : rchunk_boff <= rchunk_bend
   }.

  Ltac rck_omega ck :=
    let Hsize := fresh "Hsize" in
    let Hbend := fresh "Hbend" in
    assert (Hsize := rchunk_size_ok ck);
    assert (Hbend := rchunk_bend_ok ck);
    omega.

  Lemma boff_mod_ok : forall off,
    off mod block_items < block_items.
  Proof.
    intros.
    apply Nat.mod_bound_pos.
    omega.
    apply block_items_gt_0.
  Qed.

  Local Ltac min_cases :=
    let Hminspec := fresh "Hminspec" in
    let Hlt := fresh "Hlt" in
    let Hmineq := fresh "Hmineq" in
    (* TODO: use a match/arg to find a min to destruct
       rather than using edestruct *)
    edestruct Nat.min_spec as [Hminspec|Hminspec];
    inversion Hminspec as [Hlt Hmineq];
    clear Hminspec;
    erewrite Hmineq;
    try omega.

  Section chunking.

  Local Obligation Tactic := Tactics.program_simpl; try min_cases.

  Program Definition preamble (off count':nat) (w: items (S count')) : chunk :=
    let count := count' + 1 in
    let blocknum := off / block_items in
    let boff := off mod block_items in
    let bend := Nat.min (boff + count) block_items in
    let bsize := bend - boff in
    @Build_chunk ($ blocknum) boff bend
      (isplit1_dep bsize (count-bsize) w _) _ _.
  Next Obligation.
    apply Nat.lt_le_incl.
    apply boff_mod_ok.
  Qed.

  Program Fixpoint build_chunks num_chunks blocknum count (w: items count) : list chunk :=
  match num_chunks with
  | 0 => nil
  | S num_chunks' => let bend := Nat.min count block_items in
    @Build_chunk ($ blocknum) 0 bend
      (isplit1_dep bend (count-bend) w _) _ _ ::
    build_chunks num_chunks' (blocknum+1)
        (isplit2_dep bend (count-bend) w _)
  end.
  Next Obligation.
    rewrite Nat.sub_0_r.
    reflexivity.
    rewrite Nat.sub_0_r.
    reflexivity.
  Qed.

  Program Definition chunkList (off count:nat) (w: items count) : list chunk :=
    let blocknum := off / block_items in
    let boff := off mod block_items in
    let bend := Nat.min (boff + count) block_items in
    let bsize := bend - boff in
    let num_chunks := divup (count - bsize) block_items in
    @Build_chunk ($ blocknum) boff bend
      (isplit1_dep bsize (count-bsize) w _) _ _ ::
      build_chunks num_chunks (blocknum+1)
      (isplit2_dep bsize (count-bsize) w _).
  Next Obligation.
    apply Nat.lt_le_incl.
    apply boff_mod_ok.
  Qed.

  Program Fixpoint build_rchunks num_chunks blocknum len : list rchunk :=
  match num_chunks with
  | 0 => nil
  | S num_chunks' => let bend := Nat.min len block_items in
    @Build_rchunk ($ blocknum) 0 bend _ _ ::
    build_rchunks num_chunks' (blocknum+1) (len-bend)
  end.

  Program Definition rchunkList (off len:nat) : list rchunk :=
    let blocknum := off / block_items in
    let boff := off mod block_items in
    let bend := Nat.min (boff + len) block_items in
    let bsize := bend - boff in
    let num_chunks := divup (len - bsize) block_items in
    @Build_rchunk ($ blocknum) boff bend _ _ ::
      build_rchunks num_chunks (blocknum+1) (len-bsize).
  Next Obligation.
    apply Nat.lt_le_incl.
    apply boff_mod_ok.
  Qed.

  Lemma build_chunk_blocknum_bound : forall num_chunks blocknum count (w: items count),
    let bound := blocknum + num_chunks in
    forall ck, In ck (build_chunks num_chunks blocknum w) ->
      # (chunk_blocknum ck) < bound.
  Proof.
    intros.
    generalize dependent blocknum.
    generalize dependent count.
    simpl.
    induction num_chunks; intros; simpl in *.
    contradiction.

    inversion H.
    replace ck; simpl.
    eapply le_lt_trans.
    apply wordToNat_natToWord_le.
    omega.
    replace (blocknum + S num_chunks) with
      ((blocknum + 1) + num_chunks) by omega.
    eapply IHnum_chunks; eauto.
  Qed.

  Lemma build_rchunk_blocknum_bound : forall num_chunks blocknum len,
    let bound := blocknum + num_chunks in
    forall ck, In ck (build_rchunks num_chunks blocknum len) ->
      # (rchunk_blocknum ck) < bound.
  Proof.
    intros.
    generalize dependent blocknum.
    generalize dependent len.
    simpl.
    induction num_chunks; intros; simpl in *.
    contradiction.

    inversion H.
    replace ck; simpl.
    eapply le_lt_trans.
    apply wordToNat_natToWord_le.
    omega.
    replace (blocknum + S num_chunks) with
      ((blocknum + 1) + num_chunks) by omega.
    eapply IHnum_chunks; eauto.
  Qed.

  Lemma build_chunks_num_chunks : forall num_chunks blocknum count (w: items count) ck,
    In ck (build_chunks num_chunks blocknum w) ->
    num_chunks > 0.
  Proof.
    intros.
    destruct num_chunks.
    inversion H.
    omega.
  Qed.

  Lemma build_rchunks_num_chunks : forall num_chunks blocknum len ck,
    In ck (build_rchunks num_chunks blocknum len) ->
    num_chunks > 0.
  Proof.
    intros.
    destruct num_chunks.
    inversion H.
    omega.
  Qed.

  Lemma rounddown_eq : forall x y,
    0 < y -> y * (x / y) = x - x mod y.
  Proof.
    intros.
    rewrite Nat.div_mod with (x := x) (y := y) at 2 by omega.
    rewrite <- Nat.add_sub_assoc by omega.
    omega.
  Qed.

  Lemma minus_distr_minus : forall a b c,
    b <= a -> c <= b -> a - (b - c) = a - b + c.
  Proof.
    intros.
    lia.
  Qed.

  Lemma minus_distr_minus' : forall a b c,
    b <= a + c -> c <= b -> a - (b - c) = a + c - b.
  Proof.
    intros.
    lia.
  Qed.

  Lemma mod_spec : forall a b m,
    a < m -> b < m -> a mod m = b mod m -> a = b.
  Proof.
    intros.
    assert (a = a mod m).
    apply Nat.mod_unique with (q := 0); omega.
    assert (b = b mod m).
    apply Nat.mod_unique with (q := 0); omega.
    omega.
  Qed.

  Lemma mod_plus_le : forall a b m,
    (a + b) mod m <= a mod m + b mod m.
  Proof.
    intros.
    (* will need m <> 0, so handle m = 0 separately *)
    case_eq m; intros.
    - auto.
    - rewrite Nat.add_mod by auto.
      apply Nat.mod_le.
      auto.
  Qed.

  Lemma mul_mono_pos_l : forall a b p,
    0 < p ->
    a = b <-> p * a = p * b.
  Proof.
    intros.
    nia.
  Qed.

  Lemma num_items : forall off count,
    block_items <= off mod block_items + count ->
    off / block_items + 1 +
    (count - (block_items - off mod block_items)) / block_items =
    (off + count) / block_items.
  Proof.
    intros.
    assert (Hboff := boff_mod_ok off).
    assert (off mod block_items <= off) as Hoffbound.
    apply Nat.mod_le; auto.
    rewrite mul_mono_pos_l with (p := block_items) by auto.
    repeat rewrite Nat.mul_add_distr_l.
    repeat rewrite rounddown_eq by auto.
    rewrite Nat.mul_1_r.
    rewrite <- Nat.mod_add with (b := 1)
      (* select correct mod *)
      (a := count - (block_items - off mod block_items)) by auto.
    rewrite Nat.mul_1_l.
    replace (count - (block_items - off mod block_items) + block_items) with
      (count + block_items - (block_items - off mod block_items)) by omega.
    replace (count + block_items - (block_items - off mod block_items)) with
      (count + off mod block_items) by omega.
    destruct (lt_dec count block_items).
    * rewrite Nat.add_mod_idemp_r by auto.
      rewrite Nat.add_comm with count off.
      (* non-trivial replacement *)
      replace ((off + count) mod block_items) with
        (off mod block_items + count - block_items).
      replace (off + count - (off mod block_items + count - block_items)) with
        (off + count - (off mod block_items + count) + block_items) by omega.
      rewrite minus_distr_minus' by omega.
      (* this miraculously works *)
      omega.

      (* return to the replacement *)
      eapply mod_spec with (m := block_items).
      omega.
      apply boff_mod_ok.
      rewrite <- Nat.mod_add with (b := 1) by auto.
      rewrite Nat.mul_1_l.
      rewrite <- Nat.add_sub_swap by omega.
      rewrite Nat.add_sub.
      rewrite Nat.add_mod_idemp_l by auto.
      rewrite Nat.mod_mod by auto.
      reflexivity.
    * assert (block_items <= count) by omega.
      rewrite Nat.add_mod_idemp_r by auto.
      (* we will prove the inequality later *)
      rewrite Nat.add_sub_assoc.
      rewrite Nat.add_sub_assoc by omega.
      replace (off - off mod block_items + block_items + count) with
        (off - off mod block_items + count + block_items) by omega.
      rewrite minus_distr_minus by omega.
      rewrite Nat.add_sub.
      replace (off - off mod block_items + count + off mod block_items) with
        (off - off mod block_items + off mod block_items + count) by omega.
      rewrite Nat.sub_add.
      rewrite plus_comm.
      omega.
      apply Nat.mod_le; auto.
      (* only the inequality above is left *)
      eapply le_trans.
      apply mod_plus_le.
      (* 1*block_items will be canceled out by mod_add *)
      replace count with (count - block_items + 1*block_items) at 1 by omega.
      rewrite Nat.mod_add by omega.
      rewrite minus_distr_minus by omega.
      apply plus_le_compat_r.
      apply Nat.mod_le; auto.
  Qed.

  Lemma num_items' : forall off count,
    block_items <= off mod block_items + count ->
    off / block_items + 1 +
    divup (count - (block_items - off mod block_items)) block_items =
    divup (off + count) block_items.
  Proof.
    intros.
    repeat rewrite divup_eq_divup'.
    unfold divup'.

    assert (Hboff := boff_mod_ok off).
    assert (off mod block_items <= off) as Hboff'.
    apply Nat.mod_le; auto.
    (* the two divup' operations match on the same mod *)
    assert ((count - (block_items - off mod block_items)) mod block_items =
            (off + count) mod block_items).
    rewrite Nat.add_comm.
    rewrite minus_distr_minus' by omega.
    rewrite <- Nat.mod_add with (b := 1) by auto.
    rewrite Nat.mul_1_l.
    rewrite Nat.sub_add by omega.
    apply Nat.add_mod_idemp_r; auto.

    rewrite H0.
    case_eq ((off + count) mod block_items); intros.
    - rewrite num_items; omega.
    - rewrite Nat.add_assoc.
      rewrite num_items; omega.
  Qed.

  Theorem chunk_blocknum_bound : forall off count (w: items count),
    goodSize addrlen off ->
    0 < count ->
    let bound := divup (off + count) block_items in
    Forall (fun ck => # (chunk_blocknum ck) < bound) (chunkList off w).
  Proof.
    intros.
    rewrite Forall_forall; intros.
    unfold chunkList in H1.
    inversion H1; clear H1. (* clear to save space *)
    rewrite <- H2.
    simpl.
    rewrite wordToNat_natToWord_idempotent'.
    unfold bound.
    apply div_lt_divup; auto.
    omega.
    apply goodSize_trans with off.
    apply div_le; auto.
    assumption.

    assert (Hbuild_bound := build_chunk_blocknum_bound _ _ _ x H2).
    eapply le_trans.
    eassumption.
    apply build_chunks_num_chunks in H2.
    unfold bound.
    min_cases.
    - rewrite Hmineq in H2.
      rewrite minus_plus in H2.
      rewrite minus_diag in H2.
      rewrite divup_0 in H2.
      inversion H2.
    - rewrite Hmineq in H2.
      rewrite num_items'; omega.
  Qed.

  Theorem rchunk_blocknum_bound : forall off len,
    goodSize addrlen off ->
    0 < len ->
    let bound := divup (off + len) block_items in
    Forall (fun ck => # (rchunk_blocknum ck) < bound) (rchunkList off len).
  Proof.
    intros.
    rewrite Forall_forall; intros.
    unfold chunkList in H1.
    inversion H1; clear H1. (* clear to save space *)
    rewrite <- H2.
    simpl.
    rewrite wordToNat_natToWord_idempotent'.
    unfold bound.
    apply div_lt_divup; auto.
    omega.
    apply goodSize_trans with off.
    apply div_le; auto.
    assumption.

    assert (Hbuild_bound := build_rchunk_blocknum_bound _ _ _ x H2).
    eapply le_trans.
    eassumption.
    apply build_rchunks_num_chunks in H2.
    unfold bound.
    min_cases.
    - rewrite Hmineq in H2.
      rewrite minus_plus in H2.
      rewrite minus_diag in H2.
      rewrite divup_0 in H2.
      inversion H2.
    - rewrite Hmineq in H2.
      rewrite num_items'; omega.
  Qed.

  Program Definition update_chunk (v:valu) (ck:chunk) : valu :=
  let v_items := valu2items v in
  let boff := chunk_boff ck in
  let bend := chunk_bend ck in
  let sz := bend - boff in
  let x := isplit1_dep boff (block_items - boff) v_items _ in
  let z := isplit2_dep (boff + sz) (block_items - (boff + sz)) v_items _ in
  icombine (icombine x (chunk_data ck)) z.
  Next Obligation.
    ck_omega ck.
  Qed.
  Next Obligation.
    ck_omega ck.
  Qed.
  Next Obligation.
    rewrite blocksz_ok.
    simpl.
    fold block_items.
    f_equal; ck_omega ck.
  Qed.

  Program Definition read_chunk (v:valu) (ck:rchunk) :
    items (rchunk_bend ck - rchunk_boff ck) :=
  let v_items := valu2items v in
  let boff := rchunk_boff ck in
  let bend := rchunk_bend ck in
  let sz := bend - boff in
  let xy := isplit1_dep bend (block_items - bend) v_items _ in
  let y := isplit2_dep (bend - sz) sz xy _ in
  y.
  Next Obligation.
    rck_omega ck.
  Qed.
  Next Obligation.
    rck_omega ck.
  Qed.

  Definition items_to_list count (w: items count) : list item :=
    @Rec.of_word (Rec.ArrayF itemtype count) w.

  Definition update_block_chunk (b:block) (ck:chunk) : block :=
  let boff := chunk_boff ck in
  let bend := chunk_bend ck in
  let sz := bend - boff in
  let x := firstn boff b in
  let z := skipn bend b in
  x ++ items_to_list (chunk_data ck) ++ z.

  Definition read_block_chunk (b:block) (ck:rchunk) :
    Rec.data (Rec.ArrayF itemtype (rchunk_bend ck - rchunk_boff ck)) :=
  let boff := rchunk_boff ck in
  let bend := rchunk_bend ck in
  let sz := bend - boff in
  firstn sz (skipn boff b).

  Lemma Forall_firstn : forall A (l : list A) P n,
    Forall P l ->
    Forall P (firstn n l).
  Proof.
    induction l; simpl; intros.
    - rewrite firstn_nil. auto.
    - destruct n; simpl; auto.
      constructor.
      inversion H; auto.
      inversion H; auto.
  Qed.

  Lemma Forall_skipn : forall A (l : list A) P n,
    Forall P l ->
    Forall P (skipn n l).
  Proof.
    induction l; simpl; intros.
    - rewrite skipn_nil; auto.
    - destruct n; simpl; auto.
      apply IHl.
      inversion H; auto.
  Qed.

  Hint Resolve Forall_firstn.
  Hint Resolve Forall_skipn.

  Lemma read_well_formed : forall b ck,
    Rec.well_formed b ->
    Rec.well_formed (read_block_chunk b ck).
  Proof.
    intros.
    unfold read_block_chunk, blocktype in *.
    unfold Rec.well_formed in *.
    intuition.
    destruct ck; simpl in *.
    unfold block_items in *.
    rewrite firstn_length.
    rewrite min_l; auto.
    rewrite skipn_length; omega.
  Qed.

  Theorem eq_rect_items : forall n n' H H' w,
    eq_rect (n*itemsize) word w (n'*itemsize) H =
    eq_rect n items w n' H'.
  Proof.
    intros.
    unfold items.
    rewrite eq_rect_word_mult.
    f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma split1_eq : forall n1 n2 n2'
    count (w: word count) Heq Heq',
    split1 n1 n2
      (eq_rect _ word w _ Heq) =
    split1 n1 n2'
      (eq_rect _ word w _ Heq').
  Proof.
    intros.
    assert (n2 = n2') by omega.
    generalize dependent Heq.
    rewrite H; intros.
    repeat f_equal.
    apply proof_irrelevance.
  Qed.

  Lemma split2_eq : forall n1 n1' n2
    count (w: word count) Heq Heq',
    split2 n1 n2
      (eq_rect _ word w _ Heq) =
    split2 n1' n2
      (eq_rect _ word w _ Heq').
  Proof.
    intros.
    assert (n1 = n1') by omega.
    generalize dependent Heq.
    rewrite H; intros.
    repeat f_equal.
    apply proof_irrelevance.
  Qed.

  Theorem icombine_app : forall (n m count:nat) H
    (v : items n) (w : items m),
    (@Rec.of_word (Rec.ArrayF itemtype n) v) ++
        (@Rec.of_word (Rec.ArrayF itemtype m) w) =
    @Rec.of_word (Rec.ArrayF itemtype count) (eq_rect (n + m) items (icombine v w)
                         count H).
  Proof.
    intros.
    generalize dependent H.
    generalize dependent count.
    generalize dependent m.
    induction n; intros.
    - simpl.
      unfold icombine, eq_rec_r, eq_rec.
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
      rewrite Rec.combine_0.
      assert (m = count) as Heq by omega.
      generalize dependent H.
      generalize dependent w.
      rewrite Heq; intros.
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
      reflexivity.

    - simpl Rec.len in *.
      destruct count.
      inversion H.
      rewrite Rec.of_word_cons.
      simpl.
      erewrite IHn with (count := count).
      unfold icombine.
      unfold eq_rec_r, eq_rec.
      simpl.
      rewrite <- combine_split with (sz1:=itemsize) (sz2:=n * itemsize) (w := v).
      f_equal.
      rewrite split1_combine.
      unfold eq_rec.
      unfold items.
      repeat rewrite eq_rect_word_mult.
      rewrite eq_rect_nat_double.
      assert (count = n + m) as Hcount by omega.
      repeat generalize_proof.
      rewrite Hcount; intros.
      eq_rect_simpl.
      rewrite combine_split.
      rewrite Rec.of_word_cons.
      fold itemsize.
      f_equal.
      * f_equal.
        rewrite <- split1_combine with (w := v) (z := w) at 1.
        erewrite split1_iter.
        rewrite eq_rect_word_match.
        apply split1_eq.
      * f_equal.
          (* clean up proof terms *)
          generalize_proof.
          generalize_proof.
          clear e e0 e1.
          clear Hcount.
          intros.
        simpl.
        rewrite <- combine_split with (w := v).
        erewrite combine_assoc.
        rewrite split2_combine.
        rewrite eq_rect_word_match; eq_rect_simpl.
        rewrite eq_rect_combine.
        rewrite split2_combine.
        f_equal.
        apply proof_irrelevance.

    Grab Existential Variables.
    all: omega.
  Qed.

  Theorem icombine_app' : forall (n m:nat)
    (v : items n) (w : items m),
    (@Rec.of_word (Rec.ArrayF itemtype n) v) ++
        (@Rec.of_word (Rec.ArrayF itemtype m) w) =
    @Rec.of_word (Rec.ArrayF itemtype (n+m)) (icombine v w).
  Proof.
    intros.
    assert (n+m = n+m) as H by reflexivity.
    replace (icombine v w) with (eq_rect (n + m) items (icombine v w) (n+m) H).
    apply icombine_app.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    reflexivity.
  Qed.

  Lemma items_Sn_cons : forall n (w: items (S n)),
    @Rec.of_word (Rec.ArrayF itemtype _) w =
      (@Rec.of_word itemtype (single_item (isplit1 1 n w))) ::
      (@Rec.of_word (Rec.ArrayF itemtype _) (isplit2 1 n w)).
  Proof.
    intros.
    unfold single_item.
    unfold eq_rec.
    simpl.
    generalize_proof; intros.
    rewrite Rec.of_word_cons.
    f_equal.
    - f_equal.
      unfold isplit1.
      rewrite eq_rect_split1.
      eq_rect_simpl.
      reflexivity.
    - f_equal.
      unfold isplit2.
      simpl in *. fold itemsize.
      eq_rect_simpl.
      replace w with (eq_rect _ word w _ eq_refl) at 1.
      apply split2_eq.
      reflexivity.
  Qed.

  Theorem isplit1_firstn' : forall (n m:nat)
    (w : items (n+m)),
    firstn n (@Rec.of_word (Rec.ArrayF itemtype (n+m)) w) =
    @Rec.of_word (Rec.ArrayF itemtype n) (isplit1 n m w).
  Proof.
    intros.
    induction n.
    - compute.
      reflexivity.
    - simpl plus in *.
      rewrite items_Sn_cons.
      simpl.
      rewrite IHn.
      rewrite items_Sn_cons.

      f_equal.
      * unfold isplit1, eq_rec.
        simpl.
        rewrite eq_rect_split1.

        rewrite eq_rect_nat_double.
        erewrite split1_iter.
        f_equal.
        f_equal.
        repeat rewrite eq_rect_word_match.
        repeat rewrite eq_rect_nat_double.
        apply split1_eq.
      * unfold isplit1, isplit2, eq_rec.
        simpl.
        rewrite eq_rect_split2.
        rewrite eq_rect_split1.
        repeat rewrite eq_rect_nat_double.
        erewrite split1_split2.
        rewrite eq_rect_word_match.
        rewrite eq_rect_nat_double.
        f_equal.
        f_equal.
        f_equal.
        f_equal.
        apply proof_irrelevance.

        Grab Existential Variables.
        all: omega.
  Qed.

  Theorem isplit2_skipn' : forall (n m:nat)
    (w : items (n+m)),
    skipn n (@Rec.of_word (Rec.ArrayF itemtype (n+m)) w) =
    @Rec.of_word (Rec.ArrayF itemtype m) (isplit2 n m w).
    intros.
    induction n.
    - simpl.
      unfold isplit2.
      simpl.
      unfold eq_rec.
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
      reflexivity.
    - simpl plus in *.
      rewrite items_Sn_cons.
      simpl.
      rewrite IHn.
      unfold isplit2, eq_rec.
      rewrite eq_rect_split2.
      rewrite eq_rect_nat_double.
      simpl.
      erewrite split2_iter.
      rewrite eq_rect_word_match.
      rewrite eq_rect_nat_double.
      f_equal.
      apply split2_eq.

      Grab Existential Variables.
      all: omega.
  Qed.

  Lemma update_chunk_valu_block : forall b ck,
    Rec.well_formed b ->
    update_block_chunk b ck =
    valu2block (update_chunk (rep_block b) ck).
  Proof.
    intros.
    unfold rep_block.
    unfold RecArray.rep_block.
    unfold valu2block.
    unfold update_chunk.
    unfold isplit1_dep, isplit2_dep.
    unfold update_block_chunk.
    eq_rect_simpl.
    unfold blocktype.
    simpl.
    fold itemsize.
    erewrite eq_rect_items.
    rewrite <- icombine_app.
    rewrite <- icombine_app'.
    rewrite <- isplit1_firstn'.
    rewrite <- isplit2_skipn'.
    rewrite app_assoc_reverse.
    unfold valu2items, wreclen_to_valu.
    unfold items.
    repeat rewrite eq_rect_word_mult.
    unfold RecArray.blocktype.
    eq_rect_simpl.
    f_equal; [| f_equal].

    - f_equal.
      assert (chunk_boff ck + (block_items - chunk_boff ck) = block_items)
        as Hck by (ck_omega ck).
      generalize_proof.
      rewrite Hck; intros.
      eq_rect_simpl.
      rewrite Rec.of_to_id; auto.
    - f_equal.
      assert (Hsize := chunk_size_ok ck).
      omega.
      simpl.
      generalize_proof.
      assert ((chunk_boff ck + (chunk_bend ck - chunk_boff ck) +
       (block_items - (chunk_boff ck + (chunk_bend ck - chunk_boff ck)))) =
       block_items) as Hck by (ck_omega ck).
      rewrite Hck; intros.
      eq_rect_simpl.
      rewrite Rec.of_to_id; auto.

      Grab Existential Variables.
      fold block_items.
      ck_omega ck.
  Qed.

  Definition apply_chunk (ck:chunk) (ilist: list item) : list item :=
  let blocknum := # (chunk_blocknum ck) in
  let ck_start := blocknum*block_items + chunk_boff ck in
  let ck_end := blocknum*block_items + chunk_bend ck in
  let data := items_to_list (chunk_data ck) in
  (firstn ck_start ilist) ++ data ++ (skipn ck_end ilist).

  Fixpoint apply_chunks (chunks: list chunk) (ilist: list item) : list item :=
  match chunks with
  | nil => ilist
  | ck :: xs => apply_chunks xs (apply_chunk ck ilist)
  end.

  End chunking.


  (** Read/modify/write a chunk in place. **)
  Definition bf_put_chunk T lxp ixp inum (ck:chunk) mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum (chunk_blocknum ck) mscs;
    let v' := update_chunk v ck in
    mscs <- BFILE.bfwrite lxp ixp  inum (chunk_blocknum ck) v' mscs;
    rx mscs.

  Definition bf_read_chunk T lxp ixp inum (ck:rchunk) mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum (rchunk_blocknum ck) mscs;
    let v' := read_chunk v ck in
    rx ^(mscs, v').

  Lemma update_chunk_parts : forall (ck:chunk) (vs_nested: list block) def,
    Forall (fun sublist => length sublist = block_items) vs_nested ->
    Forall Rec.well_formed vs_nested ->
    let blocknum := # (chunk_blocknum ck) in
    blocknum < length vs_nested ->
    let boff := chunk_boff ck in
    let bend := chunk_bend ck in
    let data := chunk_data ck in
    valu2block (update_chunk (rep_block (selN vs_nested blocknum def)) ck) =
    firstn boff (skipn (blocknum*block_items) (concat vs_nested)) ++
    items_to_list data ++
    firstn (block_items - bend) (skipn (blocknum*block_items + bend) (concat vs_nested)).
  Proof.
    intros.
    rewrite <- skipn_skipn'.
    rewrite concat_hom_skipn by assumption.
    rewrite <- update_chunk_valu_block.
    unfold update_block_chunk.
    f_equal.
    unfold boff.
    apply concat_hom_subselect_firstn with (k := block_items); try assumption.
      apply (chunk_boff_ok ck).
    f_equal.
    unfold bend.
    apply concat_hom_subselect_skipn with (k := block_items); try assumption.
      apply (chunk_bend_ok ck).
    rewrite Forall_forall in H0.
    apply H0.
    apply in_selN; assumption.
  Qed.

  Lemma apply_chunk_preserves_length : forall ck ilist,
    # (chunk_blocknum ck) * block_items + block_items <= length ilist ->
    length (apply_chunk ck ilist) = length ilist.
  Proof.
    intros.
    unfold apply_chunk.
    assert (Hbend := chunk_bend_ok ck).
    assert (Hsize := chunk_size_ok ck).
    set (blockoff := # (chunk_blocknum ck) * block_items) in *.
    set (boff := chunk_boff ck) in *.
    set (bend := chunk_bend ck) in *.
    repeat rewrite app_length.
    rewrite firstn_length_l by omega.
    rewrite skipn_length by omega.
    unfold items_to_list.
    unfold item.
    rewrite Rec.array_of_word_length.
    fold item.
    omega.
  Qed.

  Definition hidden p : Prop := p.
  Opaque hidden.

  Theorem bf_put_chunk_ok : forall lxp bxp ixp inum (ck:chunk) mscs,
  {< m mbase F Fm A f flist Fx v ilist,
    PRE LOG.rep lxp F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ (Fx * # (chunk_blocknum ck) |-> v)%pred (list2nmem (BFILE.BFData f)) ]] *
    [[ array_item_file f ilist ]]
    POST RET: mscs
      exists m' f' flist' ilist' v',
        LOG.rep lxp F (ActiveTxn mbase m') mscs *
        [[ (Fm * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ (Fx * # (chunk_blocknum ck) |-> v')%pred (list2nmem (BFILE.BFData f')) ]] *
        [[ array_item_file f' ilist' ]] *
        [[ ilist' = apply_chunk ck ilist ]] *
        [[ length ilist' = length ilist ]] *
        [[ hidden (BFILE.BFAttr f' = BFILE.BFAttr f) ]]
    CRASH LOG.would_recover_old lxp F mbase
  >} bf_put_chunk lxp ixp inum ck mscs.
  Proof.
    unfold bf_put_chunk.
    hoare.

    clear H2. (* clear some space *)
    split_reps.
    unfold array_item_pairs in Hrep_items.
    destruct_lift Hrep_items.
    unfold array_item_file.
    exists (updN vs_nested
      (# (chunk_blocknum ck))
      (valu2block (update_chunk v8 ck))).
    subst; simpl.
    split; [|split].
    - (* length *)
      rewrite length_updN.
      rewrite length_upd.
      assumption.
    - (* array_item_pairs *)
      unfold array_item_pairs.
      rewrite map_updN.
      rewrite valu_rep_id.
      apply list2nmem_array_eq in H2.
      replace (BFILE.BFData f).
      assert (Forall Rec.well_formed
        (updN
          vs_nested
          (# (chunk_blocknum ck))
          (valu2block (update_chunk v8 ck)))).
        apply Forall_upd.
        assumption.
        (* valu2block is basically Rec.of_word, with some dependent-type proofs *)
        unfold valu2block.
        apply Rec.of_word_length.
      assert (Hmaprep := list2nmem_array
        (updN (map rep_block vs_nested)
          (# (chunk_blocknum ck))
          (update_chunk v8 ck))).
      pred_apply; cancel.

    - (* ilist' = concat vs_nested' *)
      unfold apply_chunk.
      assert (# (chunk_blocknum ck) < length vs_nested) as Hblocknum_bound.
      rewrite Hrep_len.
      eapply list2nmem_inbound.
      eassumption.
      (* backup H9 *)
      assert (H9' := H9).
      apply well_formed_length in H9.
      rewrite <- concat_hom_updN_first_skip with (k := block_items) by assumption.
      rewrite firstn_sum_split.
      rewrite skipn_sum_split' with (off2 := block_items) by (apply (chunk_bend_ok ck)).
      repeat (rewrite app_assoc).
      f_equal.
      repeat (rewrite app_assoc_reverse).
      f_equal.
      replace v8 with (rep_block (selN vs_nested
        (# (chunk_blocknum ck)) (valu2block ($ 0)))).
      rewrite update_chunk_parts; auto.
      apply list2nmem_array_eq in H2.
      rewrite H2 in H5.
      eapply list2nmem_sel in H5.
      erewrite selN_map in H5 by assumption.
      rewrite H5.
      reflexivity.

    - (* prove length doesn't change *)
      apply apply_chunk_preserves_length.
      apply list2nmem_ptsto_bound in H5.
      erewrite <- array_items_block_sized by eauto.
      unfold lt in H5.
      apply Nat.mul_le_mono_pos_r with (p := block_items) in H5; auto.
      simpl in H5.
      omega.
    - Transparent hidden.
      unfold hidden.
      replace f'.
      auto.

    Grab Existential Variables.
    exact ($ 0).
  Qed.

  Theorem bf_read_chunk_ok : forall lxp bxp ixp inum (ck:rchunk) mscs,
  {< m mbase F Fm A f flist Fx v,
    PRE LOG.rep lxp F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ (Fx * # (rchunk_blocknum ck) |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET: ^(mscs, v')
        LOG.rep lxp F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ v' = read_chunk v ck ]]
    CRASH LOG.would_recover_old lxp F mbase
  >} bf_read_chunk lxp ixp inum ck mscs.
  Proof.
    unfold bf_read_chunk.
    step. (* 30s *)
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (bf_put_chunk _ _ _ _ _) _) => apply bf_put_chunk_ok : prog.

  Definition bf_read_blocks T fsxp inum off count mscs rx : prog T :=
    let^ (mscs, l) <- For i < ($ count)
      Ghost [ F mbase Fm m A flist ilist f ]
      Loopvar [mscs l ]
      Continuation lrx
      Invariant
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ array_item_file f ilist ]] *
        [[ concat (map (@Rec.of_word blocktype) l) =
            firstn (#i * block_items) (skipn (off * block_items) ilist) ]]
      OnCrash LOG.would_recover_old (FSXPLog fsxp) F mbase
      Begin
        let^ (mscs, v) <- BFILE.bfread (FSXPLog fsxp) (FSXPInode fsxp) inum $ (off + #i) mscs;
        lrx ^(mscs, l ++ (rew blocksz_ok in v) :: nil)
      Rof ^(mscs, nil);
    rx ^(mscs, l).

  Program Definition bf_read_range T fsxp inum off len mscs rx : prog T :=
    let bstart := off / block_items in
    let bend := divup (off+len) block_items in
    let size := bend - bstart in
    let^ (mscs, blocks) <- bf_read_blocks fsxp inum bstart size mscs;
    let valu_array_type := Rec.ArrayF (Rec.WordF (Rec.len blocktype)) size in
    let xyz := @Rec.to_word valu_array_type blocks in
    let xyz' := (eq_rect _ word xyz (size * block_items * itemsize) _) in
    let yz := isplit2_dep (off mod block_items)
      (size * block_items - off mod block_items) xyz' _ in
    let y := isplit1_dep len (size * block_items - off mod block_items - len) yz _ in
    rx ^(mscs, y).
  Next Obligation.
    (* eq_rect to make Rec.to_word length of form count * itemsize *)
    rewrite mult_assoc.
    reflexivity.
  Qed.
  Next Obligation.
    rewrite le_plus_minus_r.
    auto.
    destruct len.
    rewrite Nat.add_0_r.
    generalize (boff_mod_ok off).
    divup_cases;
      try rewrite minus_diag; try rewrite minus_plus;
      omega.
    assert (off / block_items < divup (off + S len) block_items).
    apply div_lt_divup; auto; omega.
    generalize (boff_mod_ok off); nia.
  Qed.
  Next Obligation.
    rewrite le_plus_minus_r; auto.
    rewrite Nat.mul_sub_distr_r.
    fold (roundup (off + len) block_items).
    (* setup a div_mod rewrite to produce just roundup - off *)
    rewrite <- Nat.sub_add_distr.
    rewrite mult_comm.
    rewrite <- Nat.div_mod; auto.
    generalize (roundup_ge (off + len) block_items block_items_gt_0).
    omega.
  Qed.

  (* Make T the only implicit argument; in particular, make len an explicit
    argument. Otherwise it's implicitly passed in rx by the _usage_ of
    bf_read_range's return value, which is confusing. *)
  Implicit Arguments bf_read_range [T].

  Lemma to_word_cons : forall ft len a tl,
    @Rec.to_word (Rec.ArrayF ft (S len)) (a::tl) =
    combine (@Rec.to_word ft a) (@Rec.to_word (Rec.ArrayF ft len) tl).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma concat_of_word_eq_of_to : forall (l:list (word (Rec.len blocktype))) size H,
    length l = size ->
    concat (map (@Rec.of_word blocktype) l) =
    @Rec.of_word (Rec.ArrayF itemtype (size*block_items))
      (* H is just mult_assoc *)
      (rew H in (@Rec.to_word (Rec.ArrayF (Rec.WordF (Rec.len blocktype)) size) l)).
  Proof.
    induction l; intros; simpl in *.
    subst.
    reflexivity.
    erewrite IHl with (size := (Nat.pred size)).
    - generalize ?H; intros.
      subst size.
      rewrite to_word_cons.

      fold block_items in *.
      simpl Rec.len.
      set (n1 := @length (word (block_items * Rec.len itemtype)) l) in *.
      set (n2 := block_items) in *.
      set (n3 := Rec.len itemtype) in *.

      unfold blocktype.
      fold block_items.
      erewrite icombine_app.
      unfold items, icombine.
      eq_rect_simpl.
      (* cleans up new proof terms *)
      repeat generalize_proof; intros.

      erewrite combine_eq_rect2 with
        (n := n1 * (n2 * n3)) (n':= n1 * n2 * n3).
      generalize ?H1 ?H'; intros.
      eq_rect_simpl.
      repeat f_equal; apply proof_irrelevance.

    (* other IHl obligation *)
    - inversion H0; auto.

    Grab Existential Variables.
    (* erewrite includes hypotheses stating facts about multiplication,
       for which nia is the most convenient tactic *)
    all: unfold block_items; auto; nia.
  Qed.

  (** Update a range of bytes in file at inode [inum]. Assumes file has been expanded already. **)
  Definition bf_update_range T fsxp inum off count (w: items count) mscs rx : prog T :=
    let chunks := chunkList off w in
    let^ (mscs) <- ForEach ck rest chunks
      Ghost [ F mbase Fm A ilist f ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant exists m' flist' f' ilist',
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ array_item_file f' ilist' ]] *
        [[ apply_chunks rest ilist' = apply_chunks chunks ilist ]] *
        [[ hidden (length ilist' = length ilist) ]] *
        [[ hidden (BFILE.BFAttr f' = BFILE.BFAttr f) ]]
      OnCrash
        exists m',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
      Begin
        mscs <- bf_put_chunk (FSXPLog fsxp) (FSXPInode fsxp) inum ck mscs;
        lrx ^(mscs)
      Rof ^(mscs);
    rx ^(mscs).

  Lemma isplit1_firstn : forall count data n n2 H,
    Rec.well_formed data ->
    @Rec.of_word (Rec.ArrayF itemtype _) (isplit1_dep
      n n2 (@Rec.to_word (Rec.ArrayF itemtype count) data) H) = firstn n data.
  Proof.
    intros.
    inversion H0.
    generalize dependent n2.
    generalize dependent data.
    generalize dependent count.
    induction n; intros; simpl in *.
    - reflexivity.
    - destruct data.
      exfalso.
      rewrite <- H1 in H.
      inversion H.
      simpl in H1.
      assert (length data = n + n2) by omega.
      destruct count.
      inversion H.
      inversion H.
      (* prove the induction hypothesis requirements first *)
      assert (@Rec.well_formed (Rec.ArrayF itemtype count) data) as Hwell_formed.
      eapply Rec.tl_well_formed; eassumption.
      assert (Forall Rec.well_formed data) as Hels_well_formed.
      eapply Forall_cons2; eassumption.
      rewrite <- IHn with (H := H5); auto.
      rewrite Rec.of_word_cons.
      fold itemsize.
      unfold isplit1_dep, isplit1.
      erewrite split1_iter.
      rewrite eq_rect_word_match.
      unfold items.
      rewrite eq_rect_word_mult.
      eq_rect_simpl.
      repeat generalize_proof.
      rewrite H5.
      simpl in *.
      intros.
      eq_rect_simpl.

      f_equal.
      (* separate d :: data *)
      (* d part *)
      * rewrite Rec.cons_to_word.
        rewrite eq_rect_combine.
        rewrite split1_combine.
        apply Rec.of_to_id.
        rewrite Forall_forall in H2.
        apply H2.
        constructor; reflexivity.
      (* data part *)
      * rewrite Rec.cons_to_word.
        f_equal.
        erewrite split2_split1.
        rewrite eq_rect_word_match.
        eq_rect_simpl.
        f_equal.
        rewrite eq_rect_combine.
        rewrite split2_combine.
        simpl.
        f_equal.
        apply proof_irrelevance.
   Grab Existential Variables.
   all: omega.
  Qed.

  Lemma isplit2_skipn : forall count data n n2 H,
    Rec.well_formed data ->
    isplit2_dep
      n n2 (@Rec.to_word (Rec.ArrayF itemtype count) data) H =
    @Rec.to_word (Rec.ArrayF itemtype _) (skipn n data).
  Proof.
    intros.
    unfold isplit2_dep.
    rewrite <- Rec.of_to_id with (v := data) by assumption.
    rewrite H.
    rewrite isplit2_skipn'.
    repeat rewrite Rec.to_of_id.
    reflexivity.
  Qed.

  Lemma isplit1_refold : forall n1 n2 Heq Heq_trivial w,
       split1 (n1*itemsize) (n2*itemsize)
           (eq_rect ((n1 + n2) * itemsize)
              (fun n : nat => word n) w (n1*itemsize + n2*itemsize) Heq) =
       isplit1_dep n1 n2 w Heq_trivial.
  Proof.
    intros.
    unfold isplit1_dep, isplit1.
    unfold eq_rec.
    repeat f_equal.
    rewrite <- (eq_rect_eq_dec eq_nat_dec).
    reflexivity.
    apply proof_irrelevance.
  Qed.

  Lemma apply_empty_chunk : forall (ck:chunk) ilist,
    chunk_boff ck = chunk_bend ck ->
    apply_chunk ck ilist = ilist.
  Proof.
    intros.
    unfold apply_chunk.
    unfold items_to_list.
    assert (chunk_bend ck - chunk_boff ck = 0) by omega.
    rewrite Rec.of_word_empty by omega.
    simpl.
    rewrite H.
    apply firstn_skipn.
  Qed.

  (* We don't let Coq simpl apply_chunks calls itself because it creates
     proof terms the kernel can't handle (for reasons that aren't entirely
     clear). Instead, we manually unfold apply_chunks when necessary or use
     the silly-looking apply_chunks_cons lemma. *)

  Arguments apply_chunks chunks ilist : simpl never.

  Lemma apply_chunks_cons : forall ck chunks ilist,
    apply_chunks (ck :: chunks) ilist =
    apply_chunks chunks (apply_chunk ck ilist).
  Proof.
    intros.
    reflexivity.
  Qed.

  Lemma apply_build_chunks_nodata : forall num_chunks blocknum
    (w: items 0) ilist,
    apply_chunks (build_chunks num_chunks blocknum w) ilist = ilist.
  Proof.
    induction num_chunks; intros; simpl; auto.
    rewrite apply_chunks_cons.
    rewrite IHnum_chunks.
    unfold apply_chunk.
    apply firstn_skipn.
  Qed.

  Lemma apply_chunks_nodata : forall off (w: items 0) ilist,
    let chunks := chunkList off w in
    apply_chunks chunks ilist = ilist.
  Proof.
    intros.
    subst chunks.
    unfold chunkList.
    rewrite apply_chunks_cons.
    rewrite apply_build_chunks_nodata.
    apply apply_empty_chunk.
    simpl.
    assert (Hboff := boff_mod_ok off).
    rewrite Nat.min_l; omega.
  Qed.

  Lemma apply_build_chunks : forall num_chunks blocknum count newdata ilist,
    goodSize addrlen (blocknum+num_chunks) ->
    let off := blocknum * block_items in
    let w := @Rec.to_word (Rec.ArrayF itemtype count) newdata in
    let chunks := build_chunks num_chunks blocknum w in
    count <= num_chunks * block_items ->
    off + count <= length ilist ->
    Rec.well_formed newdata ->
    apply_chunks chunks ilist = firstn off ilist ++ newdata ++ skipn (off + count) ilist.
  Proof.
    intros num_chunks blocknum count newdata ilist.
    intros HgoodSz.
    intros off w chunks.
    intros Hcountbound Hlistbound Hwellformed.
    inversion Hwellformed as [Hdatalen _].
    generalize dependent ilist.
    generalize dependent blocknum.
    generalize dependent count.
    induction num_chunks; intros.
    - simpl.
      inversion Hcountbound.
      simpl in *.
      subst.
      apply length_nil in H.
      subst.
      simpl.
      rewrite Nat.add_0_r.
      symmetry; apply firstn_skipn.
    - subst chunks.
      simpl.
      rewrite apply_chunks_cons.
      unfold apply_chunk; simpl.
      unfold items_to_list.
      unfold isplit1_dep, isplit1.
      erewrite eq_rect_split1_eq1.
      unfold eq_rec.
      rewrite eq_rect_nat_double.
      rewrite wordToNat_natToWord_idempotent'.
      rewrite Nat.add_0_r.
      rewrite <- Rec.to_of_id with (w := (isplit2_dep (Nat.min count block_items) (count - Nat.min count block_items) w
          (build_chunks_obligation_5 blocknum w eq_refl)))
            (ft := Rec.ArrayF itemtype (count - Nat.min count block_items)).
      unfold isplit2_dep.
      simpl in *.
      repeat generalize_proof.
      min_cases.
      (* count < block_items *)
      * simpl.
        rewrite minus_diag.
        intros.
        replace e1 with e by apply proof_irrelevance; clear e1.
        repeat generalize_proof; clear e e0.
        rewrite Nat.sub_0_r.
        rewrite Nat.mul_0_l.
        intros.
        unfold isplit2.
        unfold items.
        rewrite eq_rect_word_mult.
        eq_rect_simpl.
        repeat generalize_proof.
        intros.
        replace e2 with e1 by apply proof_irrelevance; clear e2.
        repeat generalize_proof.
        intros.
        rewrite split1_0.
        fold off.
        rewrite Rec.to_of_id.
        clear e e0 e1.
        unfold w.
        rewrite Rec.of_to_id by assumption.
        apply apply_build_chunks_nodata.
      * intros.
      rewrite <- isplit2_skipn'.
      eq_rect_simpl.
      rewrite IHnum_chunks.
      replace ((blocknum + 1) * block_items) with (off + block_items) at 1.
      rewrite firstn_sum_split.
      rewrite app_assoc_reverse.
      f_equal.
      unfold off.
      apply firstn_app.
      rewrite firstn_length_l.
      reflexivity.
      fold off.
      omega.
      assert (length (firstn (blocknum * block_items) ilist) = off) as H.
      rewrite firstn_length_l.
      reflexivity.
      fold off.
      omega.
      rewrite <- H at 1; clear H.
      rewrite skipn_app.
      rewrite firstn_app.
      repeat generalize_proof.
      assert (block_items - 0 = block_items) as H by omega.
      rewrite H; clear H.
      clear e e0 e1.
      intros.
      eq_rect_simpl.
      rewrite app_assoc.
      f_equal.
      erewrite Rec.split2_skipn.
      rewrite Rec.combine_app.
      unfold Rec.len_add.
      unfold Rec.len_split.
      eq_rect_simpl.
      repeat generalize_proof.
      intros.
      generalize dependent (eq_sym e).
      intros.
      replace e3 with e2 by apply proof_irrelevance; clear e3.
      simpl in *.
      clear e e1 e0.
      fold itemsize in *.
      rewrite combine_split.
      eq_rect_simpl.
      unfold w.
      unfold items.
      rewrite eq_rect_word_mult.
      rewrite <- e2.
      eq_rect_simpl.
      rewrite Rec.of_to_id.
      reflexivity.
      assumption.
      assert ((blocknum + 1) * block_items =
        blocknum * block_items + block_items) as H.
      rewrite Nat.mul_add_distr_r.
      omega.
      rewrite H; clear H.
      fold off.
      rewrite plus_assoc_reverse.
      rewrite <- skipn_skipn'.
      rewrite skipn_app_eq.
      rewrite <- skipn_skipn'.
      rewrite skipn_app_eq by apply Rec.array_of_word_length.
      rewrite skipn_skipn'.
      f_equal.
      omega.
      apply firstn_length_l.
      apply le_trans with (off + count).
      omega.
      assumption.
      (* condition for firstn_app *)
      unfold item.
      rewrite Rec.array_of_word_length.
      omega.

      rewrite Nat.mul_add_distr_r.
      unfold off.
      omega.
      unfold w.
      omega.
      apply Rec.skipn_well_formed.
      generalize_proof.
      simpl.
      replace (block_items + (count - block_items)) with count by omega.
      intros.
      eq_rect_simpl.
      unfold w.
      rewrite Rec.of_to_id by assumption.
      assumption.

      rewrite skipn_length.
      rewrite Rec.array_of_word_length by assumption.
      apply minus_plus.
      rewrite Rec.array_of_word_length by assumption.
      apply Nat.le_add_r.
      eapply goodSize_trans; try eassumption.
      omega.
      rewrite app_length.
      rewrite app_length.
      unfold item.
      rewrite Rec.array_of_word_length.
      rewrite firstn_length_l.
      rewrite Nat.mul_add_distr_r.
      simpl.
      rewrite skipn_length.
      all: fold off; fold item.
      all: omega.
   * eapply goodSize_trans; try eassumption; omega.

    Grab Existential Variables.
    rewrite Nat.mul_sub_distr_r.
    rewrite Nat.sub_0_r.
    reflexivity.
  Qed.

  Lemma applying_chunks_is_replace : forall off count newdata ilist,
    Rec.well_formed newdata ->
    goodSize addrlen (off+count) ->
    off+count <= length ilist ->
    let chunks := chunkList off (@Rec.to_word (Rec.ArrayF itemtype count) newdata) in
    apply_chunks chunks ilist = firstn off ilist ++ newdata ++ skipn (off + count) ilist.
  Proof.
    intros.
    inversion H.
    unfold chunkList in chunks.
    subst chunks.
    rewrite apply_chunks_cons.
    unfold apply_chunk; simpl.
    unfold items_to_list.
    rewrite wordToNat_natToWord_idempotent'.
    rewrite Nat.mul_comm.
    rewrite <- Nat.div_mod by auto.
    rewrite isplit1_firstn.
    rewrite isplit2_skipn.
    min_cases.
    (* in this case, there's only one chunk *)
    - rewrite minus_plus.
      rewrite minus_diag.
      rewrite divup_0.
      simpl.
      unfold apply_chunks.
      f_equal; f_equal.
      simpl.
      apply firstn_oob; omega.
      f_equal.
      rewrite Nat.add_assoc.
      rewrite <- Nat.div_mod; auto.
    - rewrite apply_build_chunks.
      assert (Hboff := boff_mod_ok off).
      assert (off mod block_items <= off).
      apply Nat.mod_le; auto.
      (* tame some of this arithmetic *)
      rewrite minus_distr_minus' by omega.
      rewrite Nat.mul_add_distr_r.
      rewrite Nat.mul_1_l.
      rewrite Nat.mul_comm.
      rewrite rounddown_eq by auto.
      replace (off - off mod block_items + block_items +
        (count + off mod block_items - block_items))
        with (off + count) by omega.
      replace (off - off mod block_items + block_items) with
        (off + (block_items - off mod block_items)) by omega.
      assert (off = length (firstn off ilist)).
      rewrite firstn_length_l; omega.
      rewrite firstn_sum_app by omega.
      rewrite skipn_sum_app by omega.
      rewrite app_assoc_reverse.
      f_equal.
      assert (block_items - off mod block_items =
        length (firstn (block_items - off mod block_items) newdata)).
      rewrite firstn_length_l; omega.
      rewrite firstn_app by auto.
      rewrite app_assoc.
      rewrite firstn_skipn.
      f_equal.
      replace count with (block_items - off mod block_items + (count -
        (block_items - off mod block_items))) at 1 by omega.
      rewrite H6 at 1.
      rewrite skipn_app_r.
      rewrite skipn_skipn.
      f_equal.
      omega.
      rewrite num_items'.
      eapply goodSize_trans; try eassumption.
      apply divup_lt_arg.
      omega.
      apply roundup_ge; auto.
      repeat rewrite app_length.
      rewrite firstn_length_l by omega.
      rewrite firstn_length_l by omega.
      rewrite skipn_length.
      rewrite Nat.mul_add_distr_r.
      rewrite Nat.mul_1_l.
      rewrite minus_distr_minus'; try omega.
      rewrite plus_assoc_reverse.
      rewrite Nat.mul_comm.
      assert (Hboff := boff_mod_ok off).
      assert (off mod block_items <= off).
      apply Nat.mod_le; auto.
      rewrite rounddown_eq by auto.
      omega.
      apply Nat.lt_le_incl.
      apply boff_mod_ok.
      rewrite rounddown_eq by auto.
      (* give omega some hints *)
      assert (off mod block_items <= off).
      apply Nat.mod_le; auto.
      assert (Hboff := boff_mod_ok off).
      omega.
      apply Rec.skipn_well_formed.
      (* need to fix the array length to apply the assumption *)
      rewrite minus_distr_minus'; try omega.
      assert (off mod block_items < block_items) by apply boff_mod_ok.
      replace (block_items - off mod block_items +
        (count + off mod block_items - block_items)) with count by omega.
      assumption.
      apply Nat.lt_le_incl.
      apply boff_mod_ok.
     - assumption.
     - assumption.
     - eapply goodSize_trans; try eassumption.
       eapply le_trans.
       apply div_le; auto.
       omega.
  Qed.

  Lemma applying_chunks_is_update : forall Fx off count olddata newdata ilist ilist',
    @Rec.well_formed (Rec.ArrayF _ _) newdata ->
    goodSize addrlen (off+count) ->
    (Fx * arrayN off olddata)%pred (list2nmem ilist) ->
    length olddata = length newdata ->
    ilist' = apply_chunks (chunkList off (@Rec.to_word (Rec.ArrayF itemtype count) newdata)) ilist ->
    (Fx * arrayN off newdata)%pred (list2nmem ilist').
  Proof.
    intros.
    assert (H1' := list2nmem_arrayN_bound _ _ H1).
    inversion H.
    inversion H1'.
    (* empty write case *)
    - rewrite H6 in *; clear H6.
      simpl in H2; symmetry in H2; apply length_nil in H2.
      rewrite H2 in *; clear H2.
      replace ilist'.
      replace count.
      rewrite apply_chunks_nodata.
      pred_apply; cancel.
    - replace ilist'.
      rewrite applying_chunks_is_replace; auto; try omega.
      replace count with (length olddata) by omega.
      apply list2nmem_arrayN_newlist; auto.
      exact (Rec.of_word $0).
  Qed.

  Theorem bf_update_range_ok : forall fsxp inum off count (w: items count) mscs,
  {< mbase m F Fm Fx A flist ilist f olddata newdata,
    PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ array_item_file f ilist ]] *
    [[ (Fx * arrayN off olddata)%pred (list2nmem ilist) ]] *
    [[ hidden (newdata = @Rec.of_word (Rec.ArrayF itemtype _) w) ]] *
    [[ hidden (length olddata = length newdata) ]] *
    [[ count > 0 ]]
    POST RET: ^(mscs)
      exists m' f' flist' ilist',
        LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ (Fx * arrayN off newdata)%pred (list2nmem ilist') ]] *
        [[ array_item_file f' ilist' ]] *
        [[ hidden (length ilist' = length ilist) ]] *
        [[ hidden (BFILE.BFAttr f' = BFILE.BFAttr f) ]]
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
  >} bf_update_range fsxp inum off w mscs.
  Proof.
    unfold bf_update_range.
    hoare.

    - Transparent hidden.
      unfold hidden in *.
      auto.
    - Transparent hidden.
      unfold hidden in *.
      assert (length olddata = count) as Hlenold.
      replace (length olddata).
      replace newdata.
      apply Rec.array_of_word_length.
      assert (olddata <> nil) as Holdnotnil.
      intro Hnil.
      rewrite Hnil in Hlenold.
      simpl in Hlenold.
      rewrite <- Hlenold in H4.
      now inversion H4.
      assert (off + count <= length ilist).
      apply list2nmem_arrayN_bound in H7.
      inversion H7.
      contradiction.
      now omega.

      apply list2nmem_array_pick.
      eapply lt_le_trans.
      assert (Hbound := @chunk_blocknum_bound off count w).
      rewrite Forall_forall in Hbound.
      apply Hbound; auto.

      apply goodSize_trans with (off + count).
      omega.
      eapply goodSize_trans; eauto.
      eapply goodSize_bound.
      eapply bfrec_bound; eauto.
      rewrite <- H0.
      apply in_app_middle.
      eapply Nat.le_trans.
      apply divup_mono; eauto.
      Transparent hidden.
      unfold hidden in *.
      replace (length ilist).
      erewrite <- array_items_num_blocks by eauto.
      auto.
    - subst.
      rewrite <- H17.
      apply apply_chunks_cons.
    - Transparent hidden.
      unfold hidden in *.
      subst newdata.
      eapply applying_chunks_is_update.
      apply Rec.of_word_length.

      (* this was proven above; this proof is slightly longer
         since above we had some useful asserts in scope *)
      eapply goodSize_trans.
      apply list2nmem_arrayN_bound in H7.
      inversion H7.
      subst olddata.
      rewrite Rec.array_of_word_length in H5.
      rewrite <- H5 in H4.
      now inversion H4.
      replace count with (length olddata).
      eassumption.
      replace (length olddata).
      apply Rec.array_of_word_length.
      eapply goodSize_bound; eauto.
      eapply bfrec_bound; eauto.
      eassumption.
      now omega.

      rewrite Rec.to_of_id.
      rewrite <- H15.
      reflexivity.
    - apply LOG.activetxn_would_recover_old.

    Grab Existential Variables.
    exact $0.
    exact tt.
  Qed.

  Lemma map_rep_valu_id : forall x,
    Forall Rec.well_formed x ->
    map valu_to_block (map rep_block x) = x.
  Proof.
    induction x; simpl; intros; auto.
    rewrite rep_valu_id. f_equal.
    apply IHx.
    eapply Forall_cons2; eauto.
    eapply Forall_inv; eauto.
  Qed.

  Lemma map_repblock_injective :
    cond_injective (map rep_block) (Forall Rec.well_formed).
  Proof.
    eapply cond_left_inv_inj with (f' := map valu_to_block) (PB := fun _ => True).
    unfold cond_left_inverse; intuition.
    apply map_rep_valu_id; auto.
  Qed.

  Lemma array_item_pairs_eq : forall vs1 vs2 m,
    array_item_pairs vs1 m
    -> array_item_pairs vs2 m
    -> vs1 = vs2.
  Proof.
    unfold array_item_pairs; intros.
    destruct_lift H. destruct_lift H0.
    apply map_repblock_injective; auto.
    eapply arrayN_list_eq; eauto.
  Qed.

  Lemma array_item_file_eq : forall f vs1 vs2,
    array_item_file f vs1
    -> array_item_file f vs2
    -> vs1 = vs2.
  Proof.
    unfold array_item_file; intros.
    repeat deex.
    f_equal.
    eapply array_item_pairs_eq; eauto.
  Qed.

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

  Lemma item0_list_repeat :
    item0_list = repeat item_zero (# items_per_valu).
  Proof.
    unfold item0_list, valu_to_block, RecArray.valu_to_block, RecArray.blocktype.
    unfold valu_to_wreclen.
    rewrite blocksz_ok. simpl.
    rewrite Rec.of_word_zero_list.
    reflexivity.
  Qed.

  Lemma block_upd_well_formed: forall (v : item) (b : block) i,
    Rec.well_formed v
    -> Rec.well_formed b
    -> @Rec.well_formed blocktype (upd b i v).
  Proof.
    intros.
    split.
    destruct H0.
    rewrite length_upd; auto.
    apply Forall_upd.
    apply H0.
    apply H.
  Qed.

  Hint Resolve block_upd_well_formed.
  Hint Resolve Rec.of_word_length.


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
    rewrite listapp_memupd.
    eapply arrayN_app_memupd with (v := v) in H as Hx.
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


  Lemma list2nmem_array_item_pairs_eq : forall a b,
    array_item_pairs a (list2nmem b) -> b = map rep_block a.
  Proof.
    unfold array_item_pairs; intros.
    apply list2nmem_array_eq.
    pred_apply; cancel.
  Qed.

  Theorem array_item_pairs_firstn' : forall n vs fd,
    n <= length vs
    -> array_item_pairs vs (list2nmem fd)
    -> array_item_pairs (firstn n vs) (list2nmem (firstn n fd)).
  Proof.
    unfold array_item_pairs; intros.
    assert (fd = map rep_block vs).
    apply list2nmem_array_eq.
    pred_apply; cancel.

    rewrite <- arrayN_split with (off := n) in H0.
    rewrite <- firstn_skipn with (l := fd) (n  := n) in H0 by auto.
    apply list2nmem_arrayN_app_iff with (l' := skipn n fd).
    pred_apply; cancel.
    rewrite firstn_map.
    rewrite map_length.
    rewrite firstn_length_l by auto.
    cancel.

    rewrite Forall_forall in H2 |- *; intros.
    apply H2; eapply in_firstn_in; eauto.
    autorewrite with core; auto.
  Qed.

  Theorem array_item_pairs_firstn : forall n vs fd,
    array_item_pairs vs (list2nmem fd)
    -> array_item_pairs (firstn n vs) (list2nmem (firstn n fd)).
  Proof.
    intros.
    assert (fd = map rep_block vs) by (apply list2nmem_array_item_pairs_eq; auto).
    destruct (le_lt_dec n (length vs)); subst.
    apply array_item_pairs_firstn'; auto.
    repeat rewrite firstn_oob; try omega; auto.
    rewrite map_length.
    apply Nat.lt_le_incl in l; eauto.
  Qed.

  Lemma concat_app_nil : forall A (l : list (list A)) (v: list A),
    concat l ++ v = concat (l ++ v :: nil).
  Proof.
    intros.
    induction l; simpl.
    symmetry; apply app_nil_r.
    rewrite app_assoc_reverse.
    rewrite IHl.
    reflexivity.
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
    {< F F1 A mbase m flist f ilistlist,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
           [[ array_item_pairs ilistlist (list2nmem (BFILE.BFData f)) ]] *
           [[ length ilistlist = length (BFILE.BFData f) ]] *
           [[ wordToNat block_ix < length (BFILE.BFData f) ]] *
           [[ (pos < items_per_valu)%word ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = sel (sel ilistlist block_ix nil) pos item_zero ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_get_pair lxp ixp inum block_ix pos mscs.
  Proof.
    unfold bf_get_pair.
    unfold array_item_pairs.
    hoare.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.

    subst.
    rewrite Rec.word_selN_equiv with (def:=item_zero) by rec_bounds.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block, sel, upd.
    erewrite selN_map by rec_bounds.
    rewrite valu_wreclen_id; rewrite Rec.of_to_id; auto.
    rewrite Forall_forall in *; apply H12.
    apply in_selN; rec_bounds.
  Qed.


  Theorem bf_get_entire_block_ok : forall lxp bxp ixp inum mscs block_ix,
    {< F F1 A mbase m flist f ilistlist,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
           [[ array_item_pairs ilistlist (list2nmem (BFILE.BFData f)) ]] *
           [[ length ilistlist = length (BFILE.BFData f) ]] *
           [[ wordToNat block_ix < length (BFILE.BFData f) ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = sel ilistlist block_ix nil ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_get_entire_block lxp ixp inum block_ix mscs.
  Proof.
    unfold bf_get_entire_block.
    unfold array_item_pairs.
    hoare.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.

    subst.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block, sel, upd.
    erewrite selN_map by rec_bounds.
    rewrite valu_wreclen_id; rewrite Rec.of_to_id; auto.
    rewrite Forall_forall in *; apply H11.
    apply in_selN; rec_bounds.
  Qed.


  Theorem bf_put_pair_ok : forall lxp bxp ixp inum mscs block_ix pos i,
    {< F F1 A mbase m flist f ilistlist,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
             [[ array_item_pairs ilistlist (list2nmem (BFILE.BFData f)) ]] *
             [[ length ilistlist = length (BFILE.BFData f) ]] *
             [[ wordToNat block_ix < length (BFILE.BFData f) ]] *
             [[ (pos < items_per_valu)%word ]] *
             [[ Rec.well_formed i ]]
    POST RET:mscs
             exists m' flist' f' fdata',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (F1 * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * # inum |-> f')%pred (list2nmem flist') ]] *
             [[ array_item_pairs (upd ilistlist block_ix 
                                     (upd (sel ilistlist block_ix nil) pos i))
                                 (list2nmem (BFILE.BFData f')) ]] *
             [[ f' = BFILE.Build_bfile fdata' (BFILE.BFAttr f) ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} bf_put_pair lxp ixp inum block_ix pos i mscs.
  Proof.
    unfold bf_put_pair.
    unfold array_item_pairs.
    hoare.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.
    erewrite arrayN_except with (i := #block_ix); rec_bounds.

    subst; simpl in *. pred_apply.

    rewrite Rec.word_updN_equiv by rec_bounds.
    unfold sel, upd; autorewrite with core.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block.
    rewrite arrayN_ex_updN_eq.
    rewrite selN_updN_eq by rec_bounds.
    erewrite selN_map by rec_bounds.
    rewrite valu_wreclen_id; rewrite Rec.of_to_id; auto.
    2: rewrite Forall_forall in *; apply H13;
       apply in_selN; rec_bounds.
    cancel.

    assert (Hx := H13).
    apply Forall_upd; auto.
    rewrite Forall_forall in Hx.
    unfold Rec.well_formed in Hx; simpl in Hx.
    unfold Rec.well_formed; simpl.
    rewrite length_updN; intuition.
    apply Hx; apply in_sel; rec_bounds.
    apply Forall_upd; auto.
    apply Hx; apply in_sel; rec_bounds.
  Qed.


  Hint Extern 1 ({{_}} progseq (bf_get_pair _ _ _ _ _ _) _) => apply bf_get_pair_ok : prog.
  Hint Extern 1 ({{_}} progseq (bf_get_entire_block _ _ _ _ _) _) => apply bf_get_entire_block_ok : prog.
  Hint Extern 1 ({{_}} progseq (bf_put_pair _ _ _ _ _ _ _) _) => apply bf_put_pair_ok : prog.



  Definition bf_get T lxp ixp inum idx mscs rx : prog T :=
    let^ (mscs, i) <- bf_get_pair lxp ixp inum (idx ^/ items_per_valu)
                                               (idx ^% items_per_valu) mscs;
    rx ^(mscs, i).

  Definition bf_put T lxp ixp inum idx v mscs rx : prog T :=
    mscs <- bf_put_pair lxp ixp inum (idx ^/ items_per_valu)
                                     (idx ^% items_per_valu) v mscs;
    rx mscs.

  Definition bf_get_all T lxp ixp inum mscs rx : prog T :=
    let^ (mscs, len) <- BFILE.bflen lxp ixp inum mscs;
    let^ (mscs, l) <- For i < len
      Ghost [ mbase m F F1 bxp flist A f ilistlist ]
      Loopvar [ mscs l ]
      Continuation lrx
      Invariant
        LOG.rep lxp F (ActiveTxn mbase m) mscs *
        [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
        [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
        [[ array_item_pairs ilistlist (list2nmem (BFILE.BFData f)) ]] *
        [[ l = fold_left (@app _) (firstn #i ilistlist) nil ]]
      OnCrash
        LOG.would_recover_old lxp F mbase
      Begin
        let^ (mscs, blocklist) <- bf_get_entire_block lxp ixp inum i mscs;
        lrx ^(mscs, l ++ blocklist)
      Rof ^(mscs, nil);
    rx ^(mscs, l).

  Definition bf_getlen T lxp ixp inum mscs rx : prog T :=
    let^ (mscs, len) <- BFILE.bflen lxp ixp inum mscs;
    let r := (len ^* items_per_valu)%word in
    rx ^(mscs, r).

  (* extending one block and put v at the first entry *)
  Definition bf_extend T lxp bxp ixp inum v mscs rx : prog T :=
    let^ (mscs, off) <- BFILE.bflen lxp ixp inum mscs;
    let^ (mscs, r) <- BFILE.bfgrow lxp bxp ixp inum mscs;
    If (Bool.bool_dec r true) {
      let ib := rep_block (upd (valu_to_block $0) $0 v) in
      mscs <- BFILE.bfwrite lxp ixp inum off ib mscs;
      rx ^(mscs, true)
    } else {
      rx ^(mscs, false)
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
    -> upd (concat l) pos v =
       concat (upd l (pos ^/ items_per_valu)
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



  Lemma S_lt_add_1 : forall m n, m > 0 ->
    S n < m <-> n < m - 1.
  Proof.
    intros; split; omega.
  Qed.

  Lemma lt_add_1_le_sub_1 : forall a b c,
    b + 1 <= c -> a < b -> a < c - 1.
  Proof.
    intros; omega.
  Qed.

  Lemma bfrec_bound_lt : forall F A m bxp ixp (inum : addr) fl f l,
    array_item_file f l
    -> (F * BFILE.rep bxp ixp fl)%pred m
    -> (A * # inum |-> f)%pred (list2nmem fl)
    -> length l < # (natToWord addrlen (INODE.blocks_per_inode * # items_per_valu) ^+ $1).
  Proof.
    intros.
    erewrite wordToNat_plusone.
    apply le_lt_n_Sm.
    eapply bfrec_bound; eauto.
    word2nat_auto.
    unfold goodSize.

    assert (X := blocksz_ok).
    unfold blocktype in X; simpl in X.
    rewrite Nat.mul_comm in X.
    apply Nat.div_unique_exact in X; auto.
    rewrite X.

    unfold addrlen.
    apply S_lt_add_1.
    apply zero_lt_pow2.
    eapply lt_add_1_le_sub_1.
    replace 64 with (63 + 1) by omega.
    apply pow2_le_S.
    eapply mult_pow2_bound_ex with (a := 10); try omega.
    compute; omega.
    apply lt_div_mono. auto.
    eapply pow2_bound_mono.
    apply valulen_bound.
    omega.

    apply bfrec_bound_goodSize.
  Qed.

  Lemma helper_item_index_valid: forall F m bxp ixp inum i fl (bl : list block),
    length bl = length (BFILE.BFData (sel fl inum BFILE.bfile0))
    -> Forall Rec.well_formed bl
    -> (F * BFILE.rep bxp ixp fl)%pred m
    -> # inum < length fl
    -> # i < length (concat bl)
    -> # (i ^/ items_per_valu) < length (BFILE.BFData (sel fl inum BFILE.bfile0)).
  Proof.
    intros.
    apply helper_wlt_wmult_wdiv_lt; auto.
    rewrite <- H.
    rewrite <- block_length_fold_right by auto.
    apply lt_wlt; erewrite wordToNat_natToWord_bound.
    subst; auto.
    eapply bfrec_bound'; eauto.
  Qed.


  Ltac bf_extend_bfdata_bound :=
    match goal with
    | [ H1 : context [ BFILE.rep _ _ ?ll ],
        H2 : (_ * _ |-> ?ff)%pred (list2nmem ?ll)
           |- length (BFILE.BFData ?ff) <= _ ] =>
      eapply BFILE.bfdata_bound_ptsto with (f := ff) (l := ll); eauto
    end.

  Local Hint Extern 1 (length (BFILE.BFData _) <= _) => bf_extend_bfdata_bound.
  Local Hint Unfold array_item_file array_item_pairs : hoare_unfold.

  (** Resize the file at [inum] to hold count_items (rounded up to fit
  a whole number of blocks) using BFILE.bftrunc. **)
  Definition bf_resize T fsxp inum count_items mscs rx : prog T :=
    let size := divup count_items block_items in
    let^ (mscs, ok) <- BFILE.bftrunc (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum ($ size) mscs;
    rx ^(mscs, ok).

  (** Alias for bf_resize where spec requires the new size to be
  smaller than the old. *)
  Definition bf_shrink T fsxp inum count_items mscs rx : prog T :=
    bf_resize fsxp inum count_items mscs rx.

  (** Alias for bf_resize where spec requires the new size to be
  larger than the old. *)
  Definition bf_expand T fsxp inum count_items mscs rx : prog T :=
    bf_resize fsxp inum count_items mscs rx.

  (* Note: these functions are the same but have distinct nice names
     in the context of shrinking/expanding *)
  (** When the file is shrunk to hold count_items,
      how many items do we actually retain? *)
  Definition kept_items count_items : nat := roundup count_items block_items.
  (** When the file is expanded to hold count_items,
      how many items do we actually allocate space for? *)
  Definition alloc_items count_items : nat := roundup count_items block_items.

  Lemma goodSize_items_blocks : forall n wsz bsz,
    goodSize wsz n -> goodSize wsz (divup n bsz).
  Proof.
    intros.
    apply goodSize_trans with n.
    apply divup_lt_arg.
    assumption.
  Qed.

  Lemma array_item_pairs_length_ok : forall lists fd,
    array_item_pairs lists (list2nmem fd)
    -> Forall (fun l => length l = block_items) lists.
  Proof.
    intros.
    rewrite Forall_forall; intros.
    unfold array_item_pairs in H.
    destruct_lift H.
    eapply RecArray.block_length_is; eauto.
  Qed.
  Local Hint Resolve array_item_pairs_length_ok.


  Lemma rep_shrink_file : forall f count_items ilist,
    count_items <= length ilist ->
    goodSize addrlen count_items ->
    array_item_file f ilist ->
    let newlen := # (natToWord addrlen (divup count_items block_items)) in
    let f' := {| BFILE.BFData := setlen (BFILE.BFData f) newlen ($ 0);
                 BFILE.BFAttr := BFILE.BFAttr f |} in
    array_item_file f' (firstn (roundup count_items block_items) ilist).
  Proof.
    intros.
    split_reps.
    unfold array_item_file.
    simpl.
    rewrite setlen_length.
    exists (firstn (divup count_items block_items) vs_nested).
    split; [|split].

    (* length file = length vs_nested *)
    unfold newlen.
    rewrite wordToNat_natToWord_idempotent' by
      (apply goodSize_items_blocks; assumption).
    apply firstn_length_l.
    unfold array_item_pairs in Hrep_items.
    destruct_lift Hrep_items.
    assert (Hl := array_items_num_blocks H1).
    rewrite Hrep_len.
    apply le_trans with (divup (length ilist) block_items).
    apply divup_mono; assumption.
    omega.

    unfold setlen, newlen.
    rewrite wordToNat_natToWord_idempotent' by
      (apply goodSize_items_blocks; assumption).
    replace ((divup count_items block_items) - length (BFILE.BFData f)) with 0; simpl.
    rewrite app_nil_r.

    (* array_item_pairs *)
    apply array_item_pairs_firstn; auto.
    apply eq_sym; apply Nat.sub_0_le.
    rewrite <- Hrep_len.
    eapply le_trans.
    eapply divup_mono; eauto.
    rewrite Hrep_concat.
    rewrite concat_hom_length with (k := block_items) by eauto.
    rewrite divup_mul; auto.

    (* vs_nested fold *)
    rewrite Hrep_concat.
    rewrite <- concat_hom_firstn with (k := block_items) by eauto.
    auto.
  Qed.

  Lemma arrayN_end : forall A (def:A) F n (l l':list A),
    (F * arrayN n l')%pred (list2nmem l) ->
    length l = n + length l' ->
    l' = skipn n l.
  Proof.
    Search arrayN skipn.
    intros.
    apply arrayN_list2nmem in H; auto.
    rewrite H.
    apply firstn_oob.
    rewrite skipn_length; omega.
  Qed.

  Lemma pred_subset : forall A (def:A) F n (l l':list A),
    (F * arrayN n l')%pred (list2nmem l) ->
    length l = n + length l' ->
    F (list2nmem (firstn n l)).
  Proof.
    intros.
    assert (l' = skipn n l) by (eapply arrayN_end; eauto).
    eapply list2nmem_arrayN_app_iff with (skipn n l).
    rewrite <- firstn_skipn with (n := n) (l := l) in H.
    pred_apply; cancel.
    rewrite firstn_length_l by omega.
    auto.
  Qed.

  Theorem bf_shrink_ok : forall fsxp inum count_items mscs,
    {< mbase m F Fm A Fi f flist ilist deleted,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ array_item_file f ilist ]] *
        (* split items into preserved [Fi] and [deleted] items *)
        (* this also ensures count_items < length ilist and this is a shrink *)
        [[ (Fi * arrayN (kept_items count_items) deleted)%pred (list2nmem ilist) ]] *
        (* the [deleted] list is actually the rest of [ilist], not some strict prefix *)
        [[ length ilist = length deleted + kept_items count_items ]]
      POST RET: ^(mscs, ok)
        exists m',
        LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
        ( [[ ok = false ]] \/
        exists f' ilist' flist',
        [[ ok = true ]] *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ array_item_file f' ilist' ]] *
        [[ ilist' = firstn (roundup count_items block_items) ilist ]] *
        (* preserves any predicate regarding the non-deleted items *)
        (* [length ilist' <= length ilist] is implied by setting [Fi] appropriately *)
        [[ Fi%pred (list2nmem ilist') ]] )
      CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} bf_shrink fsxp inum count_items mscs.
  Proof.
    unfold bf_shrink, bf_resize.

    step.
    step.

    assert (array_item_file f (concat vs_nested)).
    eexists; intuition eauto.

    apply pimpl_or_r; right; cancel.
    pose proof rep_shrink_file as H'; unfold array_item_file in H'; simpl in H'.
    apply H'; auto.
    apply le_trans with (kept_items count_items).
    unfold kept_items.
    apply roundup_ge.
    apply block_items_gt_0.
    rewrite H4.
    omega.
    apply goodSize_trans with (length (concat vs_nested)).
    eapply le_trans.
    apply roundup_ge with (sz := block_items); auto.
    unfold kept_items in *.
    fold item in *.
    omega.

    eapply goodSize_bound.
    eapply bfrec_bound; eauto.

    unfold kept_items in *.
    eapply pred_subset; eauto; try omega.
    exact item_zero.
  Qed.

  Lemma array_item_app_repeated_0 : forall vs_nested l n,
    array_item_pairs vs_nested (list2nmem l) ->
    array_item_pairs (vs_nested ++ (repeat block_zero n))
      (list2nmem (l ++ repeat ($ (0)) n)).
  Proof.
    intros.
    unfold array_item_pairs in *.
    destruct_lift H.
    assert (Forall Rec.well_formed (vs_nested ++ repeat block_zero n)).
    apply Forall_append.
    assumption.
    unfold block_zero, blocktype.
    induction n; simpl.
    auto.
    apply Forall_cons; auto.
    assert (arrayN 0 (map rep_block (vs_nested ++ repeat block_zero n))%pred
      (list2nmem (l ++ repeat ($ (0)) n))).
    rewrite map_app.
    rewrite repeat_map.
    assert (repeat (rep_block block_zero) n = repeat ($ (0)) n).
    f_equal.
    (* turn off notation to see what this is doing *)
    unfold rep_block, block_zero, block_items.
    unfold blocktype.
    unfold RecArray.rep_block.
    unfold wreclen_to_valu.
    rewrite Rec.to_of_id.
    simpl.
    rewrite blocksz_ok.
    reflexivity.
    apply list2nmem_array_eq in H.
    rewrite H.
    rewrite H2.
    apply list2nmem_array.
    pred_apply.
    cancel.
  Qed.

  Lemma repeat_repeat_concat : forall A (a:A) n k,
    concat (repeat (repeat a k) n) = repeat a (k*n).
  Proof.
    intros.
    induction n; simpl.
    rewrite Nat.mul_0_r.
    reflexivity.
    replace (k * S n) with (k + k*n).
    rewrite <- repeat_app.
    f_equal.
    assumption.
    replace (S n) with (1 + n) by omega.
    rewrite Nat.mul_add_distr_l.
    omega.
  Qed.

  Lemma repeated_blocks_are_items : forall n,
    concat (repeat block_zero n) = repeat item_zero (n * block_items).
  Proof.
    intros.
    assert (block_zero = repeat item_zero block_items).
    apply Rec.of_word_zero_list.
    rewrite H.
    rewrite Nat.mul_comm.
    apply repeat_repeat_concat.
  Qed.

  Lemma rep_expand_file : forall f count_items ilist,
    roundup count_items block_items >= length ilist ->
    goodSize addrlen count_items ->
    array_item_file f ilist ->
    let newlen := # (natToWord addrlen (divup count_items block_items)) in
    let f' := {| BFILE.BFData := setlen (BFILE.BFData f) newlen ($ 0);
                 BFILE.BFAttr := BFILE.BFAttr f |} in
    let newdata := repeat item_zero (alloc_items count_items - length ilist) in
    array_item_file f' (ilist ++ newdata).
  Proof.
    intros.
    split_reps.
    exists (vs_nested ++ repeat block_zero (newlen - (length (BFILE.BFData f)))).
    simpl.
    rewrite setlen_length.
    assert (newlen >= length (BFILE.BFData f)) as Hexpand.
      unfold newlen;
      rewrite wordToNat_natToWord_idempotent'.
      unfold ge.
      apply Nat.mul_le_mono_pos_r with block_items; auto.
      erewrite array_items_block_sized; eauto.
      apply goodSize_items_blocks; assumption.
    intuition.
    (* length of file = length vs *)
    rewrite app_length.
    rewrite Hrep_len.
    rewrite repeat_length.
    omega.

    (* array_item_pairs *)
    unfold setlen.
    rewrite firstn_oob by assumption.
    apply array_item_app_repeated_0; assumption.

    rewrite concat_app.
    f_equal.
    auto.
    rewrite repeated_blocks_are_items.
    subst newdata newlen.
    f_equal.
    rewrite wordToNat_natToWord_idempotent'.
    unfold alloc_items, roundup.
    rewrite Nat.mul_sub_distr_r.
    erewrite array_items_block_sized; eauto.
    apply goodSize_items_blocks; auto.
  Qed.

  Theorem bf_expand_ok : forall fsxp inum count_items mscs,
    {< mbase m F Fm Fi A f flist ilist,
     PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
       [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
       [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
       [[ array_item_file f ilist ]] *
       [[ Fi%pred (list2nmem ilist) ]] *
       (* require that this is an expand since postcondition implies all of ilist
          is preserved  *)
       [[ roundup count_items block_items >= length ilist ]] *
       [[ goodSize addrlen count_items ]]
     POST RET: ^(mscs, ok)
      exists m',
      LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
      ( [[ ok = false ]] \/
        exists f' ilist' flist' newitems,
        [[ ok = true ]] *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ array_item_file f' ilist' ]] *
        [[ ilist' = ilist ++ newitems ]] *
        (* we don't mess with ilist ([Fi] still holds) *)
        [[ (Fi * arrayN (length ilist) newitems)%pred (list2nmem ilist') ]] *
        (* this is a weak postcondition (in reality newitems consists of repeated zeros
          due to bftrunc); this allows bf_expand to eventually leave junk data with
          the same spec *)
        [[ length newitems = alloc_items count_items - length ilist ]] *
        [[ hidden (BFILE.BFAttr f' = BFILE.BFAttr f) ]] )
      CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} bf_expand fsxp inum count_items mscs.
  Proof.
    unfold bf_expand, bf_resize.

    step. (* 40s *)
    step.

    apply pimpl_or_r; right; cancel.
    unfold setlen.
    rewrite wordToNat_natToWord_idempotent'.
    instantiate (newitems := repeat item_zero
      ((divup count_items block_items -
        length (BFILE.BFData f))*block_items)).
    exists (vs_nested ++ repeat block_zero
      (divup count_items block_items -
        length (BFILE.BFData f))).
    assert (length (BFILE.BFData f) <= divup count_items block_items) as Hflen.
    unfold item in H5.
    replace (length (concat vs_nested)) with ((length (BFILE.BFData f)) * block_items) in H5.
    unfold roundup in H5.
    unfold ge in H5.
    apply Nat.mul_le_mono_pos_r with block_items; auto.
    apply array_items_block_sized.
    exists vs_nested; auto.
    autorewrite with lengths.
    rewrite Nat.min_r by auto.
    split; [|split].
    omega.
    assert
      (Forall Rec.well_formed
     (vs_nested ++
      repeat block_zero (divup count_items block_items - length (BFILE.BFData f)))).
    apply Forall_append.
    destruct_lift H0.
    auto.
    apply Forall_repeat.
    unfold block_zero.
    apply Rec.of_word_length.
    assert
      ((arrayN 0
      (map rep_block
        (vs_nested ++
         repeat block_zero (divup count_items block_items - length (BFILE.BFData f)))))%pred
      (list2nmem
         (firstn (divup count_items block_items) (BFILE.BFData f) ++
          repeat $ (0) (divup count_items block_items - length (BFILE.BFData f))))).
    unfold block_zero.
    destruct_lift H0.
    apply list2nmem_array_eq in H0.
    rewrite map_app.
    rewrite firstn_oob by auto.
    replace (BFILE.BFData f).
    rewrite repeat_map.
    assert (rep_block (@Rec.of_word blocktype (natToWord (block_items*itemsize) 0)) = $ (0)).
    unfold rep_block.
    unfold RecArray.rep_block, wreclen_to_valu, eq_rec_r, eq_rec.
    rewrite Rec.to_of_id.
    generalize_proof.
    rewrite blocksz_ok; intros.
    eq_rect_simpl.
    reflexivity.
    fold itemsize.
    fold block_items.
    rewrite H10.
    apply list2nmem_array.
    pred_apply; cancel.
    rewrite concat_app.
    f_equal.
    assert (block_zero = repeat item_zero block_items) as H0block.
    unfold block_zero, block_items, item_zero.
    simpl.
    apply Rec.of_word_zero_list.
    rewrite H0block.
    rewrite repeat_repeat_concat.
    f_equal.
    apply Nat.mul_comm.

    (* goodSize proof *)
    eapply goodSize_trans; [|eauto].
    apply divup_lt_arg.

    apply list2nmem_arrayN_app; assumption.
    autorewrite with lengths.
    unfold alloc_items, roundup.
    rewrite Nat.mul_sub_distr_r.
    f_equal.
    apply array_items_block_sized.
    (* have rep function, but only in its pieces *)
    exists vs_nested; auto.

    reflexivity.
  Qed.

  Theorem bf_getlen_ok : forall lxp bxp ixp inum mscs,
    {< F F1 A mbase m flist f ilist,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ array_item_file f ilist ]] *
           [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = $ (length ilist) ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_getlen lxp ixp inum mscs.
  Proof.
    unfold bf_getlen.
    hoare.
    destruct_lift H.
    rewrite block_length_fold_right by auto.
    subst; rec_bounds.
  Qed.


  Theorem bf_get_ok : forall lxp bxp ixp inum idx mscs,
    {< F F1 A mbase m flist f ilist,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ array_item_file f ilist ]] *
           [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ wordToNat idx < length ilist ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = sel ilist idx item_zero ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_get lxp ixp inum idx mscs.
  Proof.
    unfold bf_get.
    hoare.

    repeat rewrite_list2nmem_pred.
    eapply helper_item_index_valid; subst; eauto.
    destruct_lift H0; eauto.

    subst; unfold rep_block in H.
    apply nested_sel_divmod_concat; auto.
    destruct_lift H0.
    eapply Forall_impl; eauto.
    unfold Rec.well_formed.
    simpl; intuition.
  Qed.

  Lemma concat_eq_fold_right : forall A (l:list (list A)),
    concat l = fold_right (@app A) nil l.
  Proof.
    intros.
    reflexivity.
  Qed.

  Theorem bf_get_all_ok : forall lxp bxp ixp inum mscs,
    {< F F1 A mbase m flist f ilist,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * # inum |-> f)%pred (list2nmem flist) ]] *
           [[ array_item_file f ilist ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = ilist ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_get_all lxp ixp inum mscs.
  Proof.
    unfold bf_get_all.
    hoare.

    apply wlt_lt in H4.
    erewrite wordToNat_natToWord_bound in H4; auto.

    erewrite wordToNat_plusone by eauto.
    replace (S #m1) with (#m1 + 1) by omega.
    erewrite firstn_plusone_selN.
    rewrite fold_left_app. subst. simpl. unfold sel. auto.
    apply wlt_lt in H4.
    erewrite wordToNat_natToWord_bound in H4; auto.
    apply list2nmem_array_eq in H13. rewrite H13 in H4. autorewrite_fast. auto.

    subst.
    rewrite concat_eq_fold_right.
    rewrite <- fold_symmetric.
    f_equal.
    rewrite firstn_oob; auto.
    erewrite wordToNat_natToWord_bound; auto. omega.
    intros; apply app_assoc.
    intros; rewrite app_nil_l; rewrite app_nil_r; auto.

    Grab Existential Variables.
    exact tt.
  Qed.

  Theorem bf_put_ok : forall lxp bxp ixp inum idx v mscs,
    {< F F1 A mbase m flist f ilist,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ array_item_file f ilist ]] *
             [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ wordToNat idx < length ilist ]] *
             [[ Rec.well_formed v ]]
    POST RET:mscs
             exists m' flist' f' fdata',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ array_item_file f' (upd ilist idx v) ]] *
             [[ (F1 * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ f' = BFILE.Build_bfile fdata' (BFILE.BFAttr f) ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_put lxp ixp inum idx v mscs.
  Proof.
    unfold bf_put.
    hoare.

    repeat rewrite_list2nmem_pred.
    eapply helper_item_index_valid; subst; eauto.
    destruct_lift H; eauto.

    subst; simpl in *.

    subst; repeat rewrite_list2nmem_pred; subst.
    destruct_lift H.
    eexists; intuition; try (pred_apply; cancel).
    apply list2nmem_array_eq in H13 as Heq.
    rewrite Heq; autorewrite with core; auto.
  Qed.

  Local Hint Resolve Rec.of_word_length.

  Theorem bf_extend_ok : forall lxp bxp ixp inum v mscs,
    {< F F1 A mbase m flist f ilist,
    PRE   LOG.rep lxp F (ActiveTxn mbase m) mscs *
          [[ array_item_file f ilist ]] *
          [[ (F1 * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ Rec.well_formed v ]]
    POST RET:^(mscs, r)
          exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
          ([[ r = false ]] \/
           [[ r = true ]] * exists flist' f' fdata',
           [[ array_item_file f' (ilist ++ (upd item0_list $0 v)) ]] *
           [[ (F1 * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ f' = BFILE.Build_bfile fdata' (BFILE.BFAttr f) ]] )
    CRASH  LOG.would_recover_old lxp F mbase
    >} bf_extend lxp bxp ixp inum v mscs.
  Proof.
    unfold bf_extend.
    hoare.
    erewrite wordToNat_natToWord_bound; eauto.
    eapply pimpl_or_r; right; cancel.

    eexists; intuition; simpl.
    instantiate (vs_nested := vs_nested ++ (upd item0_list $0 v) :: nil).
    repeat (rewrite app_length; autorewrite with core); rec_bounds.
    unfold upd at 3; erewrite wordToNat_natToWord_bound; eauto.

    rewrite updN_app_tail.
    apply array_item_pairs_app; auto.
    unfold valu_to_block, RecArray.valu_to_block, rep_block, RecArray.rep_block.
    rewrite valu_wreclen_id.
    rewrite Rec.of_to_id; auto.
    apply block_upd_well_formed; auto; apply Rec.of_word_length.

    apply concat_app_nil.

    Grab Existential Variables.
    exact $0. exact emp. exact BFILE.bfile0.
    exact emp. exact nil. exact emp. exact bxp.
  Qed.


  Theorem bfile0_empty : array_item_file BFILE.bfile0 nil.
  Proof.
    unfold array_item_file, array_item_pairs.
    exists nil; intuition.
    unfold BFILE.bfile0; simpl.
    assert (emp (list2nmem (@nil valu))) by firstorder.
    pred_apply. cancel.
  Qed.

  Lemma sel_eq_selN : forall A w n (l:list A) def,
    #w = n ->
    sel l w def = selN l n def.
  Proof.
    intros.
    unfold sel.
    congruence.
  Qed.

  Lemma skipn_length' : forall A n (l:list A),
    length (skipn n l) = length l - n.
  Proof.
    intros.
    case_eq (le_dec n (length l)); intros.
    apply skipn_length; auto.
    rewrite skipn_oob; simpl; omega.
  Qed.

  Theorem bf_read_blocks_ok : forall fsxp inum off count mscs,
    {< mbase m F Fm A flist ilist f,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ array_item_file f ilist ]] *
        [[ @wordToNat addrlen ($ (off + count)) = off + count ]] *
        [[ off + count <= length (BFILE.BFData f) ]]
      POST RET: ^(mscs, l)
        LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ concat (map (@Rec.of_word blocktype) l) =
          firstn (count * block_items) (skipn (off * block_items) ilist) ]]
      CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} bf_read_blocks fsxp inum off count mscs.
  Proof.
    unfold bf_read_blocks.
    step. (* 30s *)
    assert (Hm1bound := H6).
    apply wlt_lt in H6.
    rewrite wordToNat_natToWord_idempotent' in H6.
    hoare.

    erewrite arrayN_except with (i := # ($ (off + # (m1)))); rec_bounds.
    unfold block in H13.
    unfold RecArray.block.
    simpl in *.
    replace (length vs_nested0).
    rewrite wordToNat_natToWord_idempotent'.
    eapply lt_le_trans; [|eauto]; omega.
    apply wordToNat_natToWord_idempotent'_iff in H5.
    eapply goodSize_trans; [|eauto]; omega.

    assert (Hoffcount := H5).
    apply wordToNat_natToWord_idempotent'_iff in H5.
    assert (@wordToNat addrlen ($ (off + #m1)) < length (BFILE.BFData f)).
    rewrite wordToNat_natToWord_idempotent'.
    omega.
    eapply goodSize_trans; [|eauto]; omega.
    unfold RecArray.block, block in *.
    simpl in *.

    assert (vs_nested0 = vs_nested).
    eapply vs_nested_unique; eauto.
    subst.
    rewrite map_app.
    replace (# (m1 ^+ $ (1))) with (#m1 + 1).
    rewrite concat_app.
    rewrite H14.

    assert (Forall (fun sublist => length sublist = block_items)
      vs_nested).
    destruct_lift H10.
    apply well_formed_length; auto.
    assert (Forall (fun sublist => length sublist = block_items)
      (skipn off vs_nested)).
    rewrite Forall_forall in *; intros.
    apply H12.
    eapply in_skipn_in; eauto.

    rewrite concat_hom_skipn by auto.
    do 2 rewrite concat_hom_firstn by auto.
    erewrite firstn_plusone_selN.
    rewrite concat_app.
    f_equal.
    rewrite skipn_selN.
    simpl.
    do 2 rewrite app_nil_r.

    erewrite selN_map.
    unfold rep_block, RecArray.rep_block, wreclen_to_valu, valu_to_wreclen.
    eq_rect_simpl.
    rewrite Rec.of_to_id.
    rewrite wordToNat_natToWord_idempotent'.
    auto.

    eapply goodSize_trans; [|eauto]; omega.
    destruct_lift H10.
    rewrite Forall_forall in H18.
    apply H18.
    apply in_selN.

    omega.
    omega.
    autorewrite with lengths; omega.
    eapply natplus1_wordplus1_eq; eauto.
    unfold addrlen; omega.
    apply wordToNat_natToWord_idempotent'_iff in H5.
    eapply goodSize_trans; [|eauto]; omega.

    step.
    rewrite H12.
    f_equal.
    rewrite wordToNat_natToWord_idempotent'.
    auto.
    apply wordToNat_natToWord_idempotent'_iff in H5.
    eapply goodSize_trans; [|eauto]; omega.

    Grab Existential Variables.
    exact nil.
    exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (bf_read_blocks _ _ _ _ _) _) => apply bf_read_blocks_ok : prog.

  Theorem split1_firstn' : forall t n m
    (w: word ((n+m)*Rec.len t)) Heq,
    firstn n (@Rec.of_word (Rec.ArrayF t (n+m)) w) =
      @Rec.of_word (Rec.ArrayF t n) (split1 (n*Rec.len t) (m*Rec.len t)
        (eq_rect _ word w _ Heq)).
  Proof.
    intros.
    apply Rec.split1_firstn.
  Qed.

  (* this is actually more general than the above split1_firstn' *)
  Theorem split2_skipn' : forall t n m sz
    (w: word sz) Heq Heq',
    skipn n (@Rec.of_word (Rec.ArrayF t (n+m)) (rew Heq' in w)) =
      @Rec.of_word (Rec.ArrayF t m) (split2 (n*Rec.len t) (m*Rec.len t)
        (rew Heq in w)).
  Proof.
    intros.
    erewrite Rec.split2_skipn.
    eq_rect_simpl.
    repeat f_equal; apply proof_irrelevance.

    Grab Existential Variables.
    simpl.
    nia.
  Qed.

  Theorem of_word_rew : forall n n' t
    (w: word (n*Rec.len t)) (H: n * Rec.len t = n' * Rec.len t),
    Rec.len t <> 0 ->
    @Rec.of_word (Rec.ArrayF t n')
      (rew H in w) =
    @Rec.of_word (Rec.ArrayF t n) w.
  Proof.
    intros.
    generalize_proof.
    replace n' with n by nia.
    intros; eq_rect_simpl.
    reflexivity.
  Qed.

  Lemma split_array_rew : forall n n' m t
    (w: word (n * (m * Rec.len t)))
    (H: n * (m * Rec.len t) = n' * Rec.len t)
    (H1: n * (m * Rec.len t) = n * m * Rec.len t)
    H2,
    rew H in w = rew H2 in (rew H1 in w).
  Proof.
    intros.
    eq_rect_simpl.
    f_equal; apply proof_irrelevance.
  Qed.

  Theorem bf_read_range_ok : forall fsxp inum off len mscs,
    {< mbase m F Fm A flist ilist f,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ array_item_file f ilist ]] *
        [[ goodSize addrlen (divup (off+len) block_items) ]] *
        [[ divup (off + len) block_items <= length (BFILE.BFData f) ]]
      POST RET: ^(mscs, data)
        LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ @Rec.of_word (Rec.ArrayF itemtype len) data = firstn len (skipn off ilist) ]]
      CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} bf_read_range fsxp inum off len mscs.
  Proof.
    unfold bf_read_range.
    step. (* 20s *)

    apply wordToNat_natToWord_idempotent'.
    eapply goodSize_trans; [|eauto].
    rewrite le_plus_minus_r.
    omega.
    apply le_trans with ((off+len)/block_items).
    apply Nat.div_le_mono; auto.
    omega.
    apply div_le_divup.
    rewrite le_plus_minus_r.
    auto.
    (* XXX: duplicates proof above *)
    apply le_trans with ((off+len)/block_items).
    apply Nat.div_le_mono; auto.
    omega.
    apply div_le_divup.

    hoare.
    subst.
    destruct_lift H.
    rewrite <- H0 in H4.
    assert (Hoff := boff_mod_ok off).
    assert (off mod block_items <= off).
    apply Nat.mod_le; auto.
    assert (off + len <= roundup (off + len) block_items).
    apply roundup_ge; auto.
    generalize_proof.
    repeat match goal with
    | [ |- context[isplit1_dep _ _ _ ?H] ] => generalize H
    | [ |- context[isplit2_dep _ _ _ ?H] ] => generalize H
    end.
    simpl.
    intros.
    unfold isplit1_dep, isplit1, eq_rec.
    unfold itemsize.
    set (num_blocks := divup (off + len) block_items - off / block_items) in *.
    generalize_proof; intros.
    eq_rect_simpl.
    rewrite <- split1_firstn'.
    unfold isplit2_dep, isplit2, items; eq_rect_simpl.
    unfold itemsize.
    repeat rewrite eq_rect_word_mult.
    eq_rect_simpl.
    repeat generalize_proof; intros.
    clear e e0 e1 e2.
    (* unfortunately the explicit H hint (or both n and n') is necessary *)
    erewrite of_word_rew with (H := e4) by auto.
    fold block_items in *.
    erewrite <- split2_skipn'.
    generalize ?Heq'; intros.
    erewrite split_array_rew with (H := e).
    generalize ?H2 ?H1; intros.
    erewrite of_word_rew with (H := e0) by auto.
    erewrite <- concat_of_word_eq_of_to.
    simpl.
    fold block_items.
    rewrite H12.

    rewrite firstn_skipn_subslice.
    f_equal.
    f_equal.
    rewrite plus_comm.
    rewrite mult_comm.
    rewrite <- Nat.div_mod; auto.

    unfold num_blocks.
    rewrite Nat.mul_sub_distr_r.
    fold (roundup (off+len) block_items).
    rewrite mult_comm.
    rewrite rounddown_eq by auto.
    omega.

    assert (length (concat
      (map (@Rec.of_word blocktype) a)) = length a * block_items)
        as Hconcatmaplen.
    rewrite concat_hom_length with (k := block_items).
    rewrite map_length.
    auto.
    rewrite Forall_forall; intros.
    rewrite in_map_iff in H10.
    deex.
    apply Rec.array_of_word_length.
    simpl in *.
    fold block_items in *.
    apply Nat.mul_cancel_r with (p := block_items); auto.
    rewrite <- Hconcatmaplen.
    rewrite H12.
    rewrite firstn_length_l; auto.
    assert (@length item (concat vs_nested) =
      length vs_nested * block_items) as Hconcatlen.
    apply concat_hom_length with (k := block_items).
    rewrite Forall_forall; intros.
    rewrite Forall_forall in H6.
    apply H6 in H10.
    unfold Rec.well_formed in H10.
    simpl in H10.
    intuition.
    autorewrite with lengths; rewrite Hconcatlen.
    unfold num_blocks.
    rewrite Nat.mul_sub_distr_r.
    apply Nat.sub_le_mono_r.
    apply Nat.mul_le_mono_pos_r; auto.
    apply Nat.mul_le_mono_pos_r; auto.
    apply le_trans with (divup (off + len) block_items).
    apply le_trans with ((off + len) / block_items).
    apply Nat.div_le_mono; [auto | omega].
    apply div_le_divup.
    omega.

    Grab Existential Variables.
    (* nia either can't handle these or is too slow *)
    - rewrite <- mult_assoc.
      rewrite e3.
      rewrite Nat.mul_add_distr_r.
      auto.
    - apply mult_assoc.
    - simpl.
      rewrite e3.
      rewrite Nat.mul_add_distr_r.
      auto.
  Qed.

End RECBFILE.

Implicit Arguments bf_read_range [itemtype T].

Hint Extern 1 ({{_}} progseq (bf_getlen _ _ _ _ _) _) => apply bf_getlen_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_get _ _ _ _ _ _ _ _) _) => apply bf_get_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_get_all _ _ _ _ _ _ _) _) => apply bf_get_all_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_read_range _ _ _ _ _ _ _) _) => apply bf_read_range_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_put _ _ _ _ _ _ _ _ _) _) => apply bf_put_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_extend _ _ _ _ _ _ _ _ _) _) => apply bf_extend_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_update_range _ _ _ _ _ _ _) _) => apply bf_update_range_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_shrink _ _ _ _ _) _) => apply bf_shrink_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_expand _ _ _ _ _) _) => apply bf_expand_ok : prog.

(* Two BFileRec arrays should always be equal *)
Hint Extern 0 (okToUnify (array_item_file ?a ?b ?c ?d _) (array_item_file ?a ?b ?c ?d _)) =>
  unfold okToUnify; constructor : okToUnify.
