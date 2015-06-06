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

  Lemma le_divup:
    forall m n,
      m <= n ->
      (divup m valubytes) * valubytes <= (divup n valubytes) * valubytes.
  Proof.
    unfold divup; intros.
    apply Nat.mul_le_mono_r.
    apply Nat.div_le_mono.
    rewrite valubytes_is; auto.
    omega.
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
  Definition blocksize := Rec.len blocktype.
  (** analogous to Bytes.bytes, an [items count] is a word with enough bits to hold [count] items. **)
  Definition items count := word (count * itemsize).

  Theorem blocksize_not_0 : blocksize <> 0.
  Proof.
    unfold blocksize.
    rewrite <- blocksz_ok.
    rewrite valulen_is.
    intro H.
    discriminate.
  Qed.

  Corollary blocksize_gt_0 : blocksize > 0.
  Proof.
    apply Nat.neq_0_lt_0.
    apply blocksize_not_0.
  Qed.

  Definition array_item_pairs (vs : list block) : pred :=
    ([[ Forall Rec.well_formed vs ]] *
     arrayN 0 (map rep_block vs))%pred.

  Definition array_item_file file (vs : list item) : Prop :=
    exists vs_nested,
    length vs_nested = length (BFILE.BFData file) /\
    array_item_pairs vs_nested (list2nmem (BFILE.BFData file)) /\
    vs = fold_right (@app _) nil vs_nested.

  (** splitting of items mirrors splitting of bytes defined in Bytes **)
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

    chunk_bend_ok : chunk_bend <= blocksize;
    chunk_size_ok : chunk_boff < chunk_bend
  }.

  (** if you want this fact, you can produce its proof with this function *)
  Definition chunk_boff_ok (ck:chunk) : (chunk_boff ck) < blocksize.
  Proof.
    apply le_trans with (chunk_bend ck).
    apply (chunk_size_ok ck).
    apply (chunk_bend_ok ck).
  Qed.

  (** TODO: replace bits chunk_boff through chunk_bend within v
  (also a word, but of a potentially larger size) with the data in chunk_data **)
  Definition update_chunk v (ck:chunk) : valu := v.

  Lemma boff_mod_ok : forall off,
    off mod blocksize < blocksize.
  Proof.
    intros.
    apply Nat.mod_bound_pos.
    omega.
    apply blocksize_gt_0.
  Qed.

  Section chunking.

  Local Ltac min_cases :=
    edestruct Nat.min_spec as [Hminspec|Hminspec];
    inversion Hminspec as [Hlt Hmineq];
    erewrite Hmineq;
    try omega.

  Local Obligation Tactic := Tactics.program_simpl; min_cases.

  (** split w into a list of chunks **)
  Program Fixpoint chunkList (off count:nat) (w: items count) {measure count} : list chunk :=
    match count with
    | 0 => nil
    | S count' =>
      let blocknum := off / blocksize in
      let boff := off mod blocksize in
      let bend := Nat.min (boff + count) blocksize in
      let bsize := bend - boff in
      @Build_chunk ($ blocknum) boff bend
        (isplit1_dep bsize (count-bsize) w _) _ _ ::
        chunkList (off+boff+bsize) (isplit2_dep bsize (count-bsize) w _)
    end.
  Next Obligation.
    apply boff_mod_ok.
  Defined.
  (** decreasing obligation produced by [{measure count}] *)
  Next Obligation.
    assert (off mod blocksize < blocksize) by (apply boff_mod_ok).
    omega.
  Defined.

  End chunking.


  (** Read/modify/write a chunk in place. **)
  Definition bf_put_chunk T lxp ixp inum (ck:chunk) mscs rx : prog T :=
    let^ (mscs, v) <- BFILE.bfread lxp ixp inum (chunk_blocknum ck) mscs;
    let v' := update_chunk v ck in
    mscs <- BFILE.bfwrite lxp ixp  inum (chunk_blocknum ck) v mscs;
    rx mscs.

  Theorem bf_put_chunk_ok : forall lxp bxp ixp inum (ck:chunk) mscs,
  {< m mbase F Fm Fx A f flist v,
    PRE LOG.rep lxp F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep bxp ixp flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ (Fx * # (chunk_blocknum ck) |-> v)%pred (list2nmem (BFILE.BFData f)) ]]
    POST RET: mscs
      exists m' flist' v',
        LOG.rep lxp F (ActiveTxn mbase m') mscs *
        [[ (Fm * BFILE.rep bxp ixp flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ (Fx * # (chunk_blocknum ck) |-> v')%pred (list2nmem (BFILE.BFData f)) ]] *
        [[ v' = update_chunk v ck ]]
    CRASH LOG.would_recover_old lxp F mbase
  >} bf_put_chunk lxp ixp inum ck mscs.
  Proof.
    unfold bf_put_chunk.

    step. (* bf_read *)
    step. (* bf_write *)
    step. (* return *)
  Qed.

  (** Increase the size of the BFILE at inode [inum] if necessary, using BFILE.bftrunc. **)
  Definition bf_resize T fsxp inum count_items mscs rx : prog T :=
      let size := divup count_items blocksize in
      let^ (mscs, ok) <- BFILE.bftrunc (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum ($ size) mscs;
      rx ^(mscs, ok).

  (** TODO: split bf_resize into shrink/expand and give them different specs **)

  (* Note: these functions are the same but have distinct nice names
     in the context of shrinking/expanding *)
  (** When the file is shrunk to hold count_items,
      how many items do we actually retain? *)
  Definition kept_items count_items : nat := roundup count_items (# items_per_valu).
  (** When the file is expanded to hold count_items,
      how many items do we actually allocate space for? *)
  Definition alloc_items count_items : nat := roundup count_items (# items_per_valu).

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
    [[ length deleted + kept_items count_items = length ilist ]]
    POST RET: ^(mscs, ok)
    exists m',
    LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
      ( [[ ok = false ]] \/
      exists f' ilist',
      [[ ok = true ]] *
      [[ (A * #inum |-> f')%pred (list2nmem flist) ]] *
      [[ array_item_file f' ilist' ]] *
      (* preserves any predicate regarding the non-deleted items *)
      (* [length ilist' <= length ilist] is implied by setting [Fi] appropriately *)
      [[ Fi%pred (list2nmem ilist') ]] )
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
  >} bf_resize fsxp inum count_items mscs.
  Proof.
    unfold bf_resize.
  Admitted.

  Theorem bf_expand_ok : forall fsxp inum count_items mscs,
  {< mbase m F Fm Fi A f flist ilist,
   PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
    [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
    [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
    [[ array_item_file f ilist ]] *
    [[ Fi%pred (list2nmem ilist) ]] *
    (* require that this is an expand since postcondition implies all of ilist
       is preserved  *)
    [[ count_items >= length ilist ]]
    POST RET: ^(mscs, ok)
    exists m',
    LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
      ( [[ ok = false ]] \/
      exists f' ilist' newitems,
      [[ ok = true ]] *
      [[ (A * #inum |-> f')%pred (list2nmem flist) ]] *
      [[ array_item_file f' ilist' ]] *
      (* we don't mess with ilist ([Fi] still holds) *)
      [[ (Fi * arrayN (length ilist) newitems)%pred (list2nmem ilist') ]] *
      (* [length ilist' >= length ilist] is implied by setting [Fi] appropriately *)
      [[ length newitems = alloc_items count_items - length ilist ]] )
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
  >} bf_resize fsxp inum count_items mscs.
  Proof.
    unfold bf_resize.
  Admitted.

  (** Update a range of bytes in file at inode [inum]. Assumes file has been expanded already. **)
  Definition bf_update_range T fsxp inum off count (w: items count) mscs rx : prog T :=
    let chunks := chunkList off w in
    let^ (mscs) <- ForEach ck rest chunks
      Ghost [ F mbase m ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs
      (** TODO: loop invariants **)
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

  Lemma block_length_fold_right : forall (bl : list block),
    Forall Rec.well_formed bl
    -> $ (length (fold_right (app (A:=item)) nil bl)) 
       = ($ (length bl) ^* items_per_valu)%word.
  Proof.
    intros.
    rewrite concat_length.
    rewrite fold_right_add_const by auto.
    rewrite natToWord_mult.
    rewrite natToWord_wordToNat; auto.
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
    -> length (fold_right (app (A:=Rec.data itemtype)) nil bl) 
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
    -> # i < length (fold_right (app (A:=Rec.data itemtype)) nil bl)
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

    rewrite fold_right_app; simpl; rewrite app_nil_r.
    rewrite fold_right_app_init; f_equal; auto.

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

(* Two BFileRec arrays should always be equal *)
Hint Extern 0 (okToUnify (array_item_file ?a ?b ?c ?d _) (array_item_file ?a ?b ?c ?d _)) =>
  unfold okToUnify; constructor : okToUnify.
