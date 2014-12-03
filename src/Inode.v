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

  Lemma rep_valu_id : forall b, Rec.well_formed b -> valu_to_block (rep_block b) = b.
    unfold valu_to_block, rep_block.
    unfold eq_rec_r, eq_rec.
    intros.
    rewrite Pack.eq_rect_nat_double.
    rewrite <- eq_rect_eq_dec; [| apply eq_nat_dec ].
    apply Rec.of_to_id; assumption.
  Qed.

  Definition rep_pair xp (ilistlist : list block) :=
    ([[ length ilistlist = wordToNat (IXLen xp) ]] *
     [[ Forall Rec.well_formed ilistlist ]] *
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
  Hint Rewrite rep_valu_id.

  Lemma nth_selN_eq : forall t n l (z:t), selN l n z = nth n l z.
  Proof.
    induction n; intros; destruct l; simpl; auto.
  Qed.

  Ltac nth_selN H := intros; repeat rewrite nth_selN_eq; apply H; assumption.

  Lemma in_selN : forall t n l (z:t), n < length l -> In (selN l n z) l.
  Proof.
    nth_selN nth_In.
  Qed.

  Lemma in_sel : forall t n l (z:t), wordToNat n < length l -> In (sel l n z) l.
  Proof.
    intros. apply in_selN; assumption.
  Qed.

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

    subst. autorewrite with core. auto.
    unfold rep_pair in H3.
    destruct_lift H3. rewrite Forall_forall in H9. apply H9.
    apply in_selN. rewrite H7. auto.
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

  Lemma in_updN : forall t n l x (xn:t), In x (updN l n xn) ->
    In x l \/ x = xn.
  Proof.
    induction n; intros; destruct l; intuition; simpl in *; destruct H; auto.
    destruct (IHn l x xn H); auto.
  Qed.

  Lemma in_upd : forall t n l x (xn:t), In x (upd l n xn) ->
    In x l \/ x = xn.
  Proof.
    intros. apply in_updN with (n:=wordToNat n); auto.
  Qed.

  Lemma Forall_upd : forall t P l n (v:t), Forall P l -> P v -> Forall P (upd l n v).
  Proof.
    intros. apply Forall_forall. intros v0 Hi. apply in_upd in Hi. destruct Hi.
    rewrite Forall_forall in H. apply H; assumption.
    subst. assumption.
  Qed.

  Theorem iput_pair_ok : forall lxp xp iblock ipos i,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep_pair xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]] *
           [[ Rec.well_formed i ]]
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
    destruct_lift H. cancel.
    rewrite sel_map_seq by auto. autorewrite with core.
    rewrite iput_update; auto.
    rewrite Forall_forall in H9. apply H9.
    apply in_selN. rewrite H7. auto.
    autorewrite with core. auto.
    apply Forall_upd. assumption.
    split. autorewrite with core. rewrite Forall_forall in H9. apply H9.
    apply in_sel. rewrite H7. auto.
    apply Forall_upd. rewrite Forall_forall in H9. apply H9. apply in_sel. rewrite H7. auto.
    rewrite Forall_forall in H9.
    auto.
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

  Lemma selN_app1 : forall t l l' (d:t) n,
    n < length l -> selN (l ++ l') n d = selN l n d.
  Proof.
    nth_selN app_nth1.
  Qed.

  Lemma selN_app2 : forall t l l' (d:t) n,
    n >= length l -> selN (l ++ l') n d = selN l' (n - length l) d.
  Proof.
    nth_selN app_nth2.
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

  Lemma nested_sel_divmod_concat : forall t l n m (z:t), m <> $0 ->
    Forall (fun sl => length sl = wordToNat m) l ->
    sel (sel l (n ^/ m) nil) (n ^% m) z = sel (fold_right (app (A:=t)) nil l) n z.
  Proof.
    intros. unfold sel. rewrite nested_selN_concat with (m:=wordToNat m).
    word2nat'. rewrite Nat.mul_comm. rewrite Nat.add_comm. rewrite <- Nat.div_mod.
    trivial. assumption. apply le_lt_trans with (m := wordToNat n). apply div_le; assumption.
    apply wordToNat_bound.
    apply lt_le_trans with (m := wordToNat m).
    apply Nat.mod_upper_bound; assumption.
    apply Nat.lt_le_incl; apply wordToNat_bound.
    word2nat'.
    apply Nat.mod_upper_bound; assumption.
    apply lt_le_trans with (m := wordToNat m).
    apply Nat.mod_upper_bound; assumption.
    apply Nat.lt_le_incl; apply wordToNat_bound.
    assumption.
  Qed.

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
    rewrite H9. destruct_lift H.
    apply nested_sel_divmod_concat; auto. word_neq.
    eapply Forall_impl.
    Focus 2. apply H8.
    intro a. simpl. tauto.
    step.
  Qed.

  Theorem iput_ok : forall lxp xp inum i,
    {< F mbase m ilist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilist)%pred m ]] *
           [[ (inum < IXLen xp ^* items_per_valu)%word ]] *
           [[ Rec.well_formed i ]]
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
    split.
    split; [constructor |].
    pred_apply. instantiate (a2:=l); cancel.
    apply wdiv_lt_upper_bound; [word_neq | rewrite wmult_comm; assumption].
    apply wmod_upper_bound; word_neq.
    assumption.
    step.
    apply pimpl_or_r. right.
    norm.
    cancel.
    split; [constructor |].
    split; [constructor |].
    pred_apply. cancel.
    admit. (* right inode again *)
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _) _) => apply iput_ok : prog.

End INODE.
