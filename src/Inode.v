Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import Pack.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
    IXLen : addr
}.

Module INODE.
  Definition blocks_per_inode := 3.
  Definition inodetype : Rec.type := Rec.RecF ([
    ("len", Rec.WordF addrlen);
    ("blocks", Rec.ArrayF (Rec.WordF addrlen) blocks_per_inode)]).

  Definition inode := Rec.data inodetype.
  Definition inode_zero := @Rec.of_word inodetype $0.

  Definition itemsz := Rec.len inodetype.
  Definition items_per_valu : addr := $16.
  Theorem itemsz_ok : wordToNat items_per_valu * itemsz = valulen.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition blocktype : Rec.type := Rec.ArrayF inodetype (wordToNat items_per_valu).
  Definition block := Rec.data blocktype.
  Definition block_zero := @Rec.of_word blocktype $0.

  Theorem blocksz : Rec.len blocktype = valulen.
    rewrite valulen_is; auto.
  Qed.

  Definition rep_block (b : block) : valu.
    rewrite <- blocksz. apply (Rec.to_word b).
  Defined.

  Definition valu_to_block (v : valu) : block.
    rewrite <- blocksz in v. apply (Rec.of_word v).
  Defined.

  Lemma rep_valu_idem : forall b, valu_to_block (rep_block b) = b.
    unfold valu_to_block, rep_block.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Pack.eq_rect_nat_double.
    rewrite <- eq_rect_eq_dec; [| apply eq_nat_dec ].
    admit.
  Qed.

  Definition rep_pair xp (ilistlist : list block) :=
    ( [[ length ilistlist = wordToNat (IXLen xp) ]] *
     array (IXStart xp)
          (map (fun i => rep_block (selN ilistlist i nil))
          (seq 0 (wordToNat (IXLen xp)))) $1)%pred.

  Definition iget_pair T lxp xp iblock ipos rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let ib := valu_to_block v in
    let i := sel ib ipos inode_zero in
    rx i.

  Definition iput_pair T lxp xp iblock ipos i rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let ib' := upd (valu_to_block v) ipos i in
    let v' := rep_block ib' in
    ok <- LOG.write_array lxp (IXStart xp) iblock $1 v' ;
    rx ok.

  Hint Rewrite map_length.
  Hint Rewrite seq_length.
  Hint Resolve wlt_lt.
  Hint Rewrite sel_map_seq using auto.
  Hint Rewrite rep_valu_idem.

  Theorem iget_pair_ok : forall lxp xp iblock ipos,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep_pair xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel (sel ilistlist iblock nil) ipos inode_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget_pair lxp xp iblock ipos.
  Proof.
    unfold iget_pair.
    hoare.
    unfold rep_pair in *. cancel.
    autorewrite with core. auto.
    autorewrite with core. auto.

    subst. autorewrite with core. auto.
    unfold LOG.log_intact. cancel.
  Qed.

  Lemma selS : forall t (z : t) h l i,
    selN l i z = selN (h :: l) (S i) z.
  Proof.
    auto.
  Qed.

  Lemma sel_lists_eq : forall t (z : t) n l1 l2, n = length l1 -> n = length l2 ->
    (forall i, i < n -> selN l1 i z = selN l2 i z) -> l1 = l2.
  Proof.
    induction n; destruct l1; try discriminate; destruct l2; try discriminate.
    trivial.
    intros.
    replace t1 with t0 by (apply (H1 0); omega).
    replace l2 with l1. trivial. apply IHn; auto.
    intros i Hl. erewrite selS.
    replace (selN l2 i z) with (selN (t1 :: l2) (S i) z). apply H1. omega.
    erewrite <- selS. trivial.
  Qed.

  Lemma map_sel_seq : forall t (z : t) (l : list t) n,
    n = length l -> map (fun i => selN l i z) (seq 0 n) = l.
  Proof.
    intros. apply sel_lists_eq with (z := z) (n := n); auto.
    rewrite map_length. rewrite seq_length. trivial.
    intros i Hl. apply selN_map_seq; assumption.
  Qed.

  Theorem iput_update : forall xlen inode l iblock ipos,
    (ipos < items_per_valu)%word ->
    xlen = length l ->
    (upd (map (fun i => rep_block (selN l i nil)) (seq 0 xlen)) iblock
       (rep_block (upd (selN l (wordToNat iblock) nil) ipos inode))) =
    (map (fun i => rep_block (selN (upd l iblock (upd (sel l iblock nil) ipos inode)) i nil))
       (seq 0 xlen)).
  Proof.
    unfold upd, sel; intros. remember (updN (selN l (wordToNat iblock) nil) (wordToNat ipos) inode0) as ud.
    rewrite <- map_map. rewrite map_sel_seq by assumption. rewrite <- map_updN.
    replace (map (fun i : nat => rep_block (selN (updN l (wordToNat iblock) ud) i nil)) (seq 0 xlen))
      with (map rep_block (map (fun i : nat => (selN (updN l (wordToNat iblock) ud) i nil)) (seq 0 xlen)))
      by (apply map_map). (* XXX how can I specify the rewrite location here?? *)
    rewrite map_sel_seq. trivial. autorewrite with core. assumption.
  Qed.

  Theorem iput_pair_ok : forall lxp xp iblock ipos i,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep_pair xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep_pair xp (upd ilistlist iblock (upd (sel ilistlist iblock nil) ipos i)))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput_pair lxp xp iblock ipos i.
  Proof.
    unfold iput_pair.
    hoare_unfold LOG.unfold_intact.
    unfold rep_pair. cancel.
    autorewrite with core. auto.
    unfold rep_pair. cancel.

    (* Coq bug 3815 or 3816? *)
    autorewrite with core. auto.

    apply pimpl_or_r. right. unfold rep_pair in *.
    destruct_lift H3. cancel.
    rewrite sel_map_seq by auto. autorewrite with core.
    rewrite iput_update; auto.
    autorewrite with core. auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (iget_pair _ _ _ _) _) => apply iget_pair_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput_pair _ _ _ _ _) _) => apply iput_pair_ok : prog.

  Definition rep xp (ilist : list inode) :=
    (exists ilistlist, rep_pair xp ilistlist *
     [[ ilist = fold_right (@app _) nil ilistlist ]])%pred.

  Definition iget T lxp xp inum rx : prog T :=
    i <- iget_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu);
    rx i.

  Definition iput T lxp xp inum i rx : prog T :=
    ok <- iput_pair lxp xp (inum ^/ items_per_valu) (inum ^% items_per_valu) i;
    rx ok.

  Theorem iget_ok : forall lxp xp inum,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel ilist inum inode_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp inum.
  Proof.
    unfold iget, rep.

    intros.
    eapply pimpl_ok2. eauto with prog.

    intros.
    norm.
    cancel.
    (* Something about type coersions is making [assumption] take forever.. *)
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    pred_apply; instantiate (a2:=l); cancel.
    apply wdiv_lt_upper_bound; [word_neq | rewrite wmult_comm; assumption].
    apply wmod_upper_bound; word_neq.
    step.
    subst.
    (* need to prove that we are selecting the right inode.. *)
    unfold rep_pair in H. unfold rep_block in H.
    
    admit.
    step.
  Qed.

  Theorem iput_ok : forall lxp xp inum i,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp (upd ilist inum i))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp inum i.
  Proof.
    unfold iput, rep.
    intros. eapply pimpl_ok2. eauto with prog.
    intros.
    norm.
    cancel.
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    split; [constructor |].
    pred_apply. instantiate (a2:=l); cancel.
    apply wdiv_lt_upper_bound; [word_neq | rewrite wmult_comm; assumption].
    apply wmod_upper_bound; word_neq.
    (* I've unfolded [step] here manually *)
    intros.
    eapply pimpl_ok2. eauto with prog.
    intros. subst.
    cancel. step. subst.
    intros.
    unfold stars. simpl. subst.
    pimpl_crash.
    norm.
    apply stars_or_right.
    unfold stars. simpl. subst.
    pimpl_crash.
    norm.
    cancel'.
    intuition. pred_apply.
    norm.
    repeat (cancel_one || delay_one).
    instantiate (a:= (upd l (inum ^/ items_per_valu)
        (upd (sel l (inum ^/ items_per_valu) nil) (inum ^% items_per_valu) i))).
    apply finish_frame. (* Coq loops here without the [instantiate] *)
    split; [constructor |].
    split; [constructor |].
    admit. (* right inode again *)
    constructor.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _) _) => apply iput_ok : prog.

End INODE.
