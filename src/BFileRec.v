Require Import Eqdep_dec Arith Omega List.
Require Import Word WordAuto Pred GenSep Rec Prog BasicProg Hoare SepAuto Array Log.
Require Import BFile RecArray Inode.
Require Import GenSep.
Require Import GenSepN.
Require Import ListPred.
Require Import MemMatch.
Require Import FSLayout.
Require Import Bool.
Require Import Psatz.
Require Import Program.Wf.

Set Implicit Arguments.

Definition divup (n unitsz : nat) : nat := (n + unitsz - 1) / unitsz.
Definition roundup (n unitsz:nat) : nat := (divup n unitsz) * unitsz.

 Lemma roundup_ge: forall x sz,
      sz > 0 ->
      roundup x sz >= x.
  Proof.
    unfold roundup, divup; intros.
    rewrite (Nat.div_mod x sz) at 1 by omega.
    rewrite <- Nat.add_sub_assoc by omega.
    rewrite <- plus_assoc.
    rewrite (mult_comm sz).
    rewrite Nat.div_add_l by omega.

    case_eq (x mod sz); intros.
    - rewrite (Nat.div_mod x sz) at 2 by omega.
       nia.

    - rewrite Nat.mul_add_distr_r.
      replace (S n + (sz - 1)) with (sz + n) by omega.
      replace (sz) with (1 * sz) at 3 by omega.
      rewrite Nat.div_add_l by omega.
      rewrite (Nat.div_mod x sz) at 2 by omega.
      assert (x mod sz < sz).
      apply Nat.mod_bound_pos; omega.
      nia.
  Qed.

  Lemma divup_ok:
    forall x,
      divup x valubytes * valubytes >= x.
  Proof.
    intros.
    apply roundup_ge.
    rewrite valubytes_is; omega.
  Qed.

  Lemma divup_0:
    forall x,
    divup 0 x = 0.
  Proof.
    intros.
    case_eq x; intros.
    reflexivity.
    apply Nat.div_small.
    omega.
  Qed.

  Lemma divup_divup_eq:
    forall x,
      (divup ((divup x valubytes)*valubytes) valubytes) * valubytes =
      (divup x valubytes) * valubytes.
  Proof.
    unfold divup; intros.
    rewrite <- Nat.add_sub_assoc by ( rewrite valubytes_is; omega ).
    rewrite Nat.div_add_l by ( rewrite valubytes_is; auto ).
    rewrite Nat.mul_add_distr_r.
    replace ((valubytes - 1) / valubytes * valubytes) with 0. omega.
    rewrite valubytes_is.
    compute.
    auto.
  Qed.

  Lemma divup_lt_arg: forall x sz,
    divup x sz <= x.
  Proof.
    intros.
    case_eq sz; intros.
    (* sz = 0 *)
    simpl. omega.
    case_eq x; intros.
    (* x = 0 *)
    rewrite divup_0; constructor.
    unfold divup.
    (* sz > 0, x > 0 *)
    rewrite Nat.div_mod with (y := S n) by omega.
    rewrite <- H.
    rewrite <- H0.
    apply le_trans with (sz * x / sz).
    apply Nat.div_le_mono.
    omega.
    replace (sz) with (1 + (sz - 1)) at 2 by omega.
    rewrite Nat.mul_add_distr_r.
    rewrite Nat.mul_1_l.
    replace (x + sz - 1) with (x + (sz - 1)).
    apply plus_le_compat_l.
    replace x with (n0 + 1) by omega.
    rewrite Nat.mul_add_distr_l.
    rewrite plus_comm.
    rewrite Nat.mul_1_r.
    apply le_plus_l.
    omega.
    rewrite mult_comm.
    rewrite Nat.div_mul by omega.
    apply Nat.eq_le_incl.
    apply Nat.div_mod.
    omega.
  Qed.

  Lemma divup_mono: forall m n sz,
    m <= n -> divup m sz <= divup n sz.
  Proof.
    intros.
    case_eq sz; intros.
    reflexivity.
    apply Nat.div_le_mono.
    auto.
    omega.
  Qed.

  Definition divup' x m :=
  match (x mod m) with
  | O => x / m
  | S _ => x / m + 1
  end.

  Theorem divup_eq_divup'_m_nonzero : forall x m,
    m <> 0 ->
    divup x m = divup' x m.
  Proof.
    intros.
    unfold divup, divup'.
    case_eq (x mod m); intros.
    assert (Hxm := Nat.div_mod x m H).
    rewrite H0 in Hxm.
    symmetry.
    apply Nat.div_unique with (m - 1).
    omega.
    omega.
    assert (Hxm := Nat.div_mod x m H).
    symmetry.
    apply Nat.div_unique with (r := x mod m - 1).
    apply lt_trans with (x mod m).
    omega.
    apply Nat.mod_upper_bound; assumption.
    replace (x + m - 1) with (x + (m - 1)) by omega.
    rewrite Hxm at 1.
    rewrite Nat.mul_add_distr_l.
    rewrite Nat.mul_1_r.
    assert (x mod m + (m - 1) = m + (x mod m - 1)).
    omega.
    omega.
  Qed.

  Theorem divup_eq_divup' : forall x m,
    divup x m = divup' x m.
  Proof.
    intros.
    case_eq m; intros.
    unfold divup, divup'.
    reflexivity.
    apply divup_eq_divup'_m_nonzero.
    omega.
  Qed.

  Lemma divup_mul : forall x m,
    m <> 0 ->
    divup (x*m) m = x.
  Proof.
    intros.
    rewrite divup_eq_divup'.
    unfold divup'.
    rewrite Nat.mod_mul by assumption.
    apply Nat.div_mul.
    assumption.
  Qed.

  Lemma le_divup:
    forall m n,
      m <= n ->
      divup m valubytes <= divup n valubytes.
  Proof.
    intros.
    apply divup_mono; assumption.
  Qed.

  Lemma le_roundup:
    forall m n,
      m <= n ->
      roundup m valubytes <= roundup n valubytes.
  Proof.
    unfold roundup, divup; intros.
    apply Nat.mul_le_mono_r.
    apply le_divup; assumption.
  Qed.

  (* slightly different from the one in Word.v *)
  Lemma lt_minus':
    forall a b c,
      a < c -> a - b < c.
  Proof.
    intros.
    omega.
  Qed.

  Lemma divup_goodSize:
    forall (a: addr),
      goodSize addrlen (divup #a valubytes).
  Proof.
    assert (addrlen > 1) by ( unfold addrlen ; omega ).
    generalize dependent addrlen.
    intros.
    unfold goodSize, divup.
    apply Nat.div_lt_upper_bound.
    rewrite valubytes_is; auto.
    apply lt_minus'.
    unfold addrlen.
    rewrite valubytes_is.
    replace (4096) with (pow2 12) by reflexivity.
    rewrite <- pow2_add_mul.
    replace (pow2 (12 + n)) with (pow2 (11 + n) + pow2 (11 + n)).
    apply plus_lt_compat.
    eapply lt_trans.
    apply natToWord_goodSize.
    apply pow2_inc; omega.
    apply pow2_inc; omega.
    replace (12 + n) with ((11 + n) + 1) by omega.
    rewrite (pow2_add_mul (11+n) 1).
    simpl (pow2 1).
    omega.
  Qed.

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

  (** if you want this fact, you can produce its proof with this function *)
  Definition chunk_boff_ok (ck:chunk) : (chunk_boff ck) <= block_items.
  Proof.
    apply le_trans with (chunk_bend ck).
    apply (chunk_size_ok ck).
    apply (chunk_bend_ok ck).
  Qed.


  Lemma boff_mod_ok : forall off,
    off mod block_items < block_items.
  Proof.
    intros.
    apply Nat.mod_bound_pos.
    omega.
    apply block_items_gt_0.
  Qed.

  Section chunking.

  Local Ltac min_cases :=
    let Hminspec := fresh "Hminspec" in
    let Hlt := fresh "Hlt" in
    let Hmineq := fresh "Hmineq" in
    edestruct Nat.min_spec as [Hminspec|Hminspec];
    inversion Hminspec as [Hlt Hmineq];
    erewrite Hmineq;
    try omega.

  Local Obligation Tactic := Tactics.program_simpl; try min_cases.

  (** split w into a list of chunks **)
  Program Fixpoint chunkList (off count:nat) (w: items count) {measure count} : list chunk :=
    match count with
    | 0 => nil
    | S count' =>
      let blocknum := off / block_items in
      let boff := off mod block_items in
      let bend := Nat.min (boff + count) block_items in
      let bsize := bend - boff in
      @Build_chunk ($ blocknum) boff bend
        (isplit1_dep bsize (count-bsize) w _) _ _ ::
        chunkList (off+boff+bsize) (isplit2_dep bsize (count-bsize) w _)
    end.
  Next Obligation.
    apply Nat.lt_le_incl.
    apply boff_mod_ok.
  Qed.
  (** decreasing obligation produced by [{measure count}] *)
  Next Obligation.
    assert (Hblock := boff_mod_ok off).
    omega.
  Qed.

  Program Definition preamble (off count:nat) (w: items count) : chunk :=
  let blocknum := off / block_items in
  let boff := off mod block_items in
  let bend := Nat.min (boff + count) (if (eq_nat_dec boff 0) then 0 else block_items) in
  let bsize := bend - boff in
  @Build_chunk ($ blocknum) boff bend
    (isplit1_dep bsize (count-bsize) w _) _ _.
  Next Obligation.
    all: case_eq (off mod block_items); intros;
      rewrite H in *;
      simpl in *;
      try omega.
  Qed.
  Next Obligation.
    assert (Hblock := boff_mod_ok off).
    case_eq (off mod block_items); intros;
      try rewrite H in *;
      simpl in *;
      try omega.
  Qed.

  (** says that the chunk covers items [istart, end) *)
  Definition covers (ck:chunk) istart iend : Prop :=
  let blockstart := (# (chunk_blocknum ck)) * block_items in
  let boff := chunk_boff ck in
  let bend := chunk_bend ck in
  blockstart + boff = istart /\ blockstart + bend = iend.

  Theorem preamble_covers : forall off count (w: items count),
    goodSize addrlen off ->
    count >= block_items ->
    covers (preamble off w) off (roundup off block_items).
  Proof.
    intros.
    unfold covers, preamble.
    simpl.
    rewrite wordToNat_natToWord_idempotent'.
    split.
    symmetry.
    rewrite Nat.mul_comm.
    apply Nat.div_mod.
    apply items_per_valu_not_0'.
    unfold roundup.
    rewrite divup_eq_divup'.
    unfold divup'.
    case_eq (off mod block_items); intro; simpl.
    rewrite Nat.mul_comm.
    replace (block_items * (off / block_items)) with off.
      rewrite Nat.min_0_r.
      omega.
      apply Nat.div_exact.
        apply items_per_valu_not_0'.
        assumption.
    intros.
    assert (Hblock := block_items_gt_0).
      (* simplify the match *)
      rewrite -> block_items_S_n.
      rewrite <- block_items_S_n.
    rewrite Nat.min_r.
    ring_simplify.
    rewrite <- plus_assoc.
    rewrite Nat.add_cancel_l.
    omega.
    omega.
    eapply goodSize_trans.
    apply div_le; auto.
    assumption.
  Qed.

  (* min_cases is very slow, and proofs are better with some simplification
     before applying min_cases *)
  Local Obligation Tactic := Tactics.program_simpl.

  Program Definition postscript (off count:nat) (w: items count) : chunk :=
  let wend := off + count in
  let blocknum := wend / block_items in
  let boff := 0 in
  let bend := Nat.min (wend - (wend / block_items * block_items)) count in
  let bsize := bend - boff in
  @Build_chunk ($ blocknum) boff bend
    (isplit1_dep bsize (count-bsize) w _) _ _.
  Next Obligation.
    rewrite Nat.sub_0_r.
    min_cases.
  Qed.
  Next Obligation.
    rewrite Nat.mul_comm.
    rewrite <- Nat.mod_eq by auto.
    assert ((off + count) mod block_items < block_items).
    apply Nat.mod_upper_bound.
    apply items_per_valu_not_0'.
    min_cases.
  Qed.
  Next Obligation.
    omega.
  Qed.

  Theorem postscript_covers : forall off count (w: items count),
  let wend := off + count in
    goodSize addrlen (off+count) ->
    count >= block_items ->
    covers (postscript off w) ((wend / block_items) * block_items) wend.
  Proof.
    intros.
    unfold covers, postscript.
    simpl.
    rewrite wordToNat_natToWord_idempotent'.
    split.
    rewrite Nat.add_0_r.
    reflexivity.
    rewrite Nat.mul_comm.
    rewrite <- Nat.mod_eq by auto.
    rewrite Nat.min_l.
    unfold wend.
    symmetry; apply Nat.div_mod; auto.
    eapply Nat.le_trans.
    apply Nat.lt_le_incl. apply Nat.mod_upper_bound; auto.
    assumption.
    eapply goodSize_trans.
    apply div_le; auto.
    eassumption.
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
    assert (Hboff := chunk_boff_ok ck).
    omega.
  Qed.
  Next Obligation.
    assert (Hboff := chunk_boff_ok ck).
    assert (Hbend := chunk_bend_ok ck).
    omega.
  Qed.
  Next Obligation.
    assert (Hboff := chunk_boff_ok ck).
    assert (Hbend := chunk_bend_ok ck).
    assert (Hsz := chunk_size_ok ck).
    (* why was omega not able to construct this argument,
    but manages the above ones? *)
    replace (chunk_boff ck + (chunk_bend ck - chunk_boff ck))
      with (chunk_bend ck) by omega.
    replace (chunk_bend ck + (block_items - chunk_bend ck))
      with block_items by omega.
    rewrite blocksz_ok.
    reflexivity.
  Qed.

  Definition items_to_list count (w: items count) : list item :=
    map Rec.of_word (isplit_list w).

  (** TODO: prove update_chunk_ok: something in separation logic about what
  update_chunk does to the item lists *)

  Definition apply_chunk (ck:chunk) (ilist: list item) : list item :=
  let blocknum := # (chunk_blocknum ck) in
  let ck_start := blocknum*block_items + chunk_boff ck in
  let ck_end := blocknum*block_items + chunk_bend ck in
  let data := items_to_list (chunk_data ck) in
  (firstn ck_start ilist) ++ data ++ (skipn ck_end ilist).

  Fixpoint apply_chunks (chunks: list chunk) (ilist: list item) : list item :=
  match chunks with
  | nil => ilist
  | ck :: xs => let ilist' := apply_chunks xs ilist in
    apply_chunk ck ilist'
  end.

  End chunking.

  Definition valu2block (v:valu) :  block.
    unfold block.
    rewrite blocksz_ok in v.
    apply (@Rec.of_word blocktype v).
  Defined.

  (** Read/modify/write a chunk in place. **)
  Definition bf_put_chunk T lxp ixp inum (ck:chunk) mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum (chunk_blocknum ck) mscs;
    let v' := update_chunk v ck in
    mscs <- BFILE.bfwrite lxp ixp  inum (chunk_blocknum ck) v' mscs;
    rx mscs.

  (* several facts about concat on lists of equally-sized
     (homogeneous) lists *)
  Lemma concat_hom_length : forall A (lists: list (list A)) k,
    Forall (fun sublist => length sublist = k) lists ->
    length (concat lists) = (length lists) * k.
  Proof.
    intros.
    induction lists.
    rewrite concat_nil.
    simpl; reflexivity.
    rewrite concat_cons.
    rewrite app_length.
    simpl.
    rewrite IHlists.
    rewrite Forall_forall in H.
    replace k with (length a).
    reflexivity.
    apply H.
    unfold In. left; reflexivity.
    apply Forall_cons2 with a.
    assumption.
  Qed.

  Lemma concat_hom_firstn : forall A (lists: list (list A)) n k,
    Forall (fun sublist => length sublist = k) lists ->
    firstn (n * k) (concat lists) = concat (firstn n lists).
  Proof.
    intros.
    generalize dependent n.
    induction lists; intros; simpl.
    repeat (rewrite firstn_nil).
    reflexivity.
    case_eq n; intros.
     + reflexivity.
     + rewrite firstn_cons.
       rewrite concat_cons.
       assert (H' := H).
       rewrite Forall_forall in H'.
       assert (length a = k) as Hk.
       apply H'. left; reflexivity.
       replace (S n0 * k) with (k + n0 * k).
       rewrite <- Hk.
       rewrite firstn_app_r.
       f_equal.
       rewrite Hk.
       apply IHlists.
       apply Forall_cons2 in H.
       assumption.
       ring_simplify; reflexivity.
  Qed.

  (* copied concat_hom_firstn proof, s/firstn/skipn/
     (except for firstn_cons, that becomes simpl) *)
  Lemma concat_hom_skipn : forall A (lists: list (list A)) n k,
    Forall (fun sublist => length sublist = k) lists ->
    skipn (n * k) (concat lists) = concat (skipn n lists).
  Proof.
    intros.
    generalize dependent n.
    induction lists; intros; simpl.
    repeat (rewrite skipn_nil).
    reflexivity.
    case_eq n; intros.
     + reflexivity.
     + simpl.
       assert (H' := H).
       rewrite Forall_forall in H'.
       assert (length a = k) as Hk.
       apply H'. left; reflexivity.
       replace (S n0 * k) with (k + n0 * k).
       rewrite <- Hk.
       rewrite skipn_app_r.
       f_equal.
       rewrite Hk.
       apply IHlists.
       apply Forall_cons2 in H.
       assumption.
       ring_simplify; reflexivity.
  Qed.

  Lemma concat_hom_updN_first_skip : forall A n k (lists: list (list A)) (l: list A),
    Forall (fun sublist => length sublist = k) lists ->
    n < length lists ->
    firstn (n * k) (concat lists) ++ l ++
    skipn (n * k + k) (concat lists) = concat (updN lists n l).
  Proof.
    intros.
    rewrite updN_firstn_skipn by assumption.
    rewrite concat_app.
    rewrite concat_cons.
    rewrite concat_app.
    rewrite concat_nil.
    rewrite app_nil_l.
    f_equal.
    apply concat_hom_firstn; assumption.
    f_equal.
    replace (n * k + k) with ((n + 1) * k).
    apply concat_hom_skipn; assumption.
    ring_simplify; reflexivity.
  Qed.

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
        [[ ilist' = apply_chunk ck ilist ]]
    CRASH LOG.would_recover_old lxp F mbase
  >} bf_put_chunk lxp ixp inum ck mscs.
  Proof.
    unfold bf_put_chunk.

    step. (* bf_read *)
    step. (* bf_write *)
    step. (* return *)

    inversion H4 as [vs_nested Hrep].
    inversion Hrep as [Hrep1 Hrep23]; clear Hrep.
    inversion Hrep23 as [Hrep2 Hrep3]; clear Hrep23.
    unfold array_item_pairs in Hrep2.
    destruct_lift Hrep2.
    unfold array_item_file.
    exists (updN vs_nested
      (# (chunk_blocknum ck))
      (valu2block (update_chunk v8 ck))).
    subst; simpl.
    split; [|split].
    (* length *)
    rewrite length_updN.
    rewrite length_upd.
    assumption.

    (* array_item_pairs *)
    unfold array_item_pairs.
    rewrite map_updN.
    assert (update_chunk v8 ck = rep_block (valu2block (update_chunk  v8 ck))).
      unfold rep_block, valu2block.
      unfold RecArray.rep_block.
      rewrite Rec.to_of_id.
      unfold wreclen_to_valu.
      unfold eq_rec_r.
      rewrite eq_rect_nat_double.
      rewrite <- (eq_rect_eq_dec eq_nat_dec).
      reflexivity.
    rewrite <- H7.
    apply list2nmem_array_eq in H3.
    rewrite H3.
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

    (* ilist' = concat vs_nested' *)
    unfold apply_chunk.
  Admitted.


  (** Update a range of bytes in file at inode [inum]. Assumes file has been expanded already. **)
  Definition bf_update_range T fsxp inum off count (w: items count) mscs rx : prog T :=
    let chunks := chunkList off w in
    let^ (mscs) <- ForEach ck rest chunks
      Ghost [ F mbase Fm A ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant exists m' flist' f' ilist',
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ array_item_file f' ilist' ]]
      OnCrash
        exists m',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
      Begin
        mscs <- bf_put_chunk (FSXPLog fsxp) (FSXPInode fsxp) inum ck mscs;
        lrx ^(mscs)
      Rof ^(mscs);
    rx ^(mscs).

  Theorem bf_update_range_ok : forall fsxp inum off count (w: items count) mscs,
  {< mbase m F Fm Fx A flist ilist f olddata newdata,
    PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ array_item_file f ilist ]] *
    [[ (Fx * arrayN off olddata)%pred (list2nmem ilist) ]] *
    [[ length olddata = count ]] *
    [[  @Rec.to_word (Rec.ArrayF itemtype count) newdata = w ]]
    POST RET: ^(mscs)
      exists m' f' ilist',
        LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist) ]] *
        [[ array_item_file f' ilist' ]] *
        [[ (Fx * arrayN off newdata)%pred (list2nmem ilist') ]]
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
  >} bf_update_range fsxp inum off w mscs.
  Proof.
    unfold bf_update_range.
  Admitted.

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
    inversion H.
    inversion H0; clear H0. inversion H2; clear H2.
    unfold array_item_pairs in H0.
    assert (length vs = length x * block_items).
    rewrite H3.
    destruct_lift H0.
    apply block_length_fold_right_nat; assumption.
    rewrite <- H1.
    rewrite H2.
    reflexivity.
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
    -> (F * BFILE.rep bxp ixp fl)%pred m
    -> (A * # inum |-> f)%pred (list2nmem fl)
    -> length l <= # (natToWord addrlen (INODE.blocks_per_inode * # items_per_valu)).
  Proof.
    unfold array_item_file, array_item_pairs; intros.
    repeat deex.
    destruct_lift' H.
    rewrite_list2nmem_pred.
    eapply bfrec_bound'; eauto.
  Qed.

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

  Lemma rep_shrink_file : forall f count_items ilist,
  count_items <= length ilist ->
  goodSize addrlen count_items ->
  array_item_file f ilist ->
  let newlen := # (natToWord addrlen (divup count_items block_items)) in
  let f' := {| BFILE.BFData := setlen (BFILE.BFData f) newlen ($ 0);
               BFILE.BFAttr := BFILE.BFAttr f |} in
  array_item_file f' (firstn count_items ilist).
  Proof.
    intros.
    inversion H1 as [vs_nested Hrep123].
    inversion Hrep123 as [Hrep1 Hrep23]; clear Hrep123.
    inversion Hrep23 as [Hrep2 Hrep3]; clear Hrep23.
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
    unfold array_item_pairs in Hrep2.
    destruct_lift Hrep2.
    assert (Hl := array_items_num_blocks H1).
    rewrite Hrep1.
    apply le_trans with (divup (length ilist) block_items).
    apply divup_mono; assumption.
    omega.

    (* array_item_pairs *)
    admit.

    (* vs_nested fold *)
    admit.
  Admitted.

  (** TODO: bf_shrink should not promise to make number of items
  exactly count_items, only roundup countitems block_items *)
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
      [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
      [[ array_item_file f' ilist' ]] *
      [[ ilist' = firstn count_items ilist ]] *
      (* preserves any predicate regarding the non-deleted items *)
      (* [length ilist' <= length ilist] is implied by setting [Fi] appropriately *)
      [[ Fi%pred (list2nmem ilist') ]] )
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
  >} bf_shrink fsxp inum count_items mscs.
  Proof.
    unfold bf_shrink, bf_resize.

    step.
    step.

    apply pimpl_or_r; right; cancel.
    eassumption.
    apply rep_shrink_file.
    apply le_trans with (kept_items count_items).
    unfold kept_items.
    apply roundup_ge.
    apply block_items_gt_0.
    rewrite H4.
    omega.
    admit. (* count_items <= length ilist, which should be goodSize *)
    split with vs_nested.
    split; [assumption | split; auto].

    admit. (* [[ Fi * deleted]] is true on ilist (H5, precondition);
    via array_item_file on (f with attributes modified), this implies
    Fi is true in (firstn count_items ilist) *)
  Admitted.

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
  count_items >= length ilist ->
  goodSize addrlen count_items ->
  array_item_file f ilist ->
  let newlen := # (natToWord addrlen (divup count_items block_items)) in
  let f' := {| BFILE.BFData := setlen (BFILE.BFData f) newlen ($ 0);
               BFILE.BFAttr := BFILE.BFAttr f |} in
  let newdata := repeat item_zero (alloc_items count_items - length ilist) in
  array_item_file f' (ilist ++ newdata).
  Proof.
    intros.
    inversion H1 as [vs_nested Hrep123].
    inversion Hrep123 as [Hrep1 Hrep23]; clear Hrep123.
    inversion Hrep23 as [Hrep2 Hrep3]; clear Hrep23.
    unfold array_item_file.
    simpl.
    rewrite setlen_length.
    assert (newlen >= length (BFILE.BFData f)) as Hexpand.
      unfold newlen.
      replace (length (BFILE.BFData f)) with (divup (length ilist) block_items).
      rewrite wordToNat_natToWord_idempotent'.
      apply divup_mono. (* divup is increasing *)
      omega.
      apply goodSize_items_blocks; assumption.
      symmetry; apply array_items_num_blocks; assumption.
    exists (vs_nested ++ repeat block_zero (newlen - (length (BFILE.BFData f))));
      split; [|split].
    (* length of file = length vs *)
    rewrite app_length.
    rewrite Hrep1.
    rewrite repeat_length.
    omega.

    (* array_item_pairs *)
    unfold setlen.
    rewrite firstn_oob by assumption.
    apply array_item_app_repeated_0; assumption.
    rewrite concat_app.
    f_equal.
    apply Hrep3.
    rewrite repeated_blocks_are_items.
    unfold newdata.
    f_equal.
    rewrite Nat.mul_sub_distr_r.
    unfold alloc_items, roundup.
    unfold newlen.
    rewrite wordToNat_natToWord_idempotent'.
    f_equal.
    symmetry; apply array_items_block_sized.
    assumption.
    apply goodSize_items_blocks; assumption.
  Qed.

  (** TODO: bf_expand should not promise to make number of items
  exactly count_items, only roundup countitems block_items *)
  Theorem bf_expand_ok : forall fsxp inum count_items mscs,
  {< mbase m F Fm Fi A f flist ilist,
   PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ array_item_file f ilist ]] *
    [[ Fi%pred (list2nmem ilist) ]] *
    (* require that this is an expand since postcondition implies all of ilist
       is preserved  *)
    [[ count_items >= length ilist ]] *
    [[ goodSize addrlen count_items ]]
    POST RET: ^(mscs, ok)
    exists m',
    LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
      ( [[ ok = false ]] \/
      exists f' ilist' flist' newitems,
      [[ ok = true ]] *
      [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
      [[ array_item_file f' ilist' ]] *
      [[ ilist' = ilist ++ newitems ]] *
      (* we don't mess with ilist ([Fi] still holds) *)
      [[ (Fi * arrayN (length ilist) newitems)%pred (list2nmem ilist') ]] *
      (* [length ilist' >= length ilist] is implied by setting [Fi] appropriately *)
      (* this is a weak postcondition (in reality newitems consists of repeated zeros
        due to bftrunc); this allows bf_expand to eventually leave junk data with
        the same spec *)
      [[ length newitems = alloc_items count_items - length ilist ]] )
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
  >} bf_expand fsxp inum count_items mscs.
  Proof.
    unfold bf_expand, bf_resize.

    step.
    step.

    apply pimpl_or_r; right; cancel.
    eassumption.
    apply rep_expand_file.
    assumption.
    assumption.
    unfold array_item_file; exists vs_nested.
    split; [assumption | split; auto].
    apply list2nmem_arrayN_app; assumption.
    apply repeat_length.
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


End RECBFILE.


Hint Extern 1 ({{_}} progseq (bf_getlen _ _ _ _ _) _) => apply bf_getlen_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_get _ _ _ _ _ _ _ _) _) => apply bf_get_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_get_all _ _ _ _ _ _ _) _) => apply bf_get_all_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_put _ _ _ _ _ _ _ _ _) _) => apply bf_put_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_extend _ _ _ _ _ _ _ _ _) _) => apply bf_extend_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_update_range _ _ _ _ _ _ _) _) => apply bf_update_range_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_shrink _ _ _ _ _ _) _) => apply bf_shrink_ok : prog.
Hint Extern 1 ({{_}} progseq (bf_expand _ _ _ _ _ _) _) => apply bf_expand_ok : prog.

(* Two BFileRec arrays should always be equal *)
Hint Extern 0 (okToUnify (array_item_file ?a ?b ?c ?d _) (array_item_file ?a ?b ?c ?d _)) =>
  unfold okToUnify; constructor : okToUnify.
