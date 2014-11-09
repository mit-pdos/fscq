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

Import ListNotations.

Set Implicit Arguments.


(* Inode layout *)

Record xparams := {
  IXStart : addr;
    IXLen : addr
}.

Module INODE.
  Definition inodetype : Rec.rectype := [("len", addrlen); ("block0", addrlen)].
  Definition inode := Rec.recdata inodetype.
  Definition inode_zero := Rec.word2rec inodetype $0.

  Definition itemsz := Rec.reclen inodetype.
  Definition items_per_valu : addr := $32.
  Theorem itemsz_ok : wordToNat items_per_valu * itemsz = valulen.
  Proof.
    rewrite valulen_is; auto.
  Qed.

  Definition rep_block (inodes_in_block : list inode) :=
    fold_right (fun pos v =>
                let i := selN inodes_in_block pos inode_zero in
                let iw := Rec.rec2word i in
                Pack.update items_per_valu itemsz_ok v $ pos iw)
               $0 (seq 0 (wordToNat items_per_valu)).

  Definition rep_pair xp (ilistlist : list (list inode)) :=
    array (IXStart xp)
          (map (fun i => rep_block (selN ilistlist i nil))
          (seq 0 (wordToNat (IXLen xp)))) $1.

  Definition iget_pair T lxp xp iblock ipos rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let iw := Pack.extract itemsz items_per_valu itemsz_ok v ipos in
    let i := Rec.word2rec inodetype iw in
    rx i.

  Definition iput_pair T lxp xp iblock ipos i rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let iw := Rec.rec2word i in
    let v' := Pack.update items_per_valu itemsz_ok v ipos iw in
    ok <- LOG.write_array lxp (IXStart xp) iblock $1 v' ;
    rx ok.

  Hint Resolve Nat.lt_le_incl.

  Theorem extract_sel' : forall count start ilist ipos, (ipos >= $ start)%word
    -> (ipos < $ (start + count))%word
    -> (start + count <= wordToNat items_per_valu)
    -> extract itemsz items_per_valu itemsz_ok (fold_right
         (fun (pos : nat) (v : valu) =>
          update items_per_valu itemsz_ok v $ (pos) (Rec.rec2word (selN ilist pos inode_zero)))
         $0 (seq start count)) ipos = Rec.rec2word (sel ilist ipos inode_zero).
  Proof.
    induction count; simpl; intros.
    - exfalso. unfold not in *; apply H. replace (start) with (start+0) by omega. auto.
    - assert (start < wordToNat items_per_valu) by ( simpl; omega ).
      destruct (weq $ start ipos).
      + subst. rewrite extract_same; auto.
        unfold sel. erewrite wordToNat_natToWord_bound; eauto.
        apply lt_wlt. erewrite wordToNat_natToWord_bound; eauto.
      + rewrite extract_other; auto.
        eapply IHcount; try replace (S start + count) with (start + S count) by omega; auto.
        assert ($ start < ipos)%word by ( apply le_neq_lt; auto ).
        unfold not; intros.
        apply wlt_lt in H4.
        apply wlt_lt in H3.
        erewrite wordToNat_natToWord_bound in H3; eauto.
        erewrite wordToNat_natToWord_bound in H4; eauto.
        omega.
  Qed.

  Theorem extract_sel : forall ilist ipos, (ipos < items_per_valu)%word
    -> extract itemsz items_per_valu itemsz_ok (rep_block ilist) ipos =
       Rec.rec2word (sel ilist ipos inode_zero).
  Proof.
    intros; unfold rep_block.
    apply extract_sel'.
    intro x; apply wlt_lt in x; rewrite roundTrip_0 in *; omega.
    rewrite plus_O_n. rewrite natToWord_wordToNat. auto.
    omega.
  Qed.

  Hint Rewrite map_length.
  Hint Rewrite seq_length.
  Hint Resolve wlt_lt.
  Hint Rewrite sel_map_seq using auto.
  Hint Rewrite extract_sel using auto.
  Hint Rewrite Rec.word2rec_rec2word.

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

    eexists. pred_apply. cancel.

    autorewrite with core. auto.

    subst. autorewrite with core. auto.

    unfold LOG.log_intact; cancel.
  Qed.

  Theorem map_rep_block_below : forall xlen xstart l ui v, ui < xstart
    -> map (fun i => rep_block (selN (updN l ui v) i nil)) (seq xstart xlen) =
       map (fun i => rep_block (selN l i nil)) (seq xstart xlen).
  Proof.
    induction xlen; simpl; intros.
    - reflexivity.
    - apply f_equal2.
      rewrite selN_updN_ne by omega; reflexivity.
      auto.
  Qed.

  Theorem iput_update' : forall xlen xstart inode l iblock ipos,
    updN (map (fun i => rep_block (selN l i nil)) (seq xstart xlen)) iblock
      (update items_per_valu itemsz_ok (rep_block (selN l (iblock + xstart) nil)) ipos
         (Rec.rec2word inode)) =
    map (fun i => rep_block
      (selN (updN l (iblock + xstart) (updN (selN l (iblock + xstart) nil) (wordToNat ipos) inode)) i nil))
      (seq xstart xlen).
  Proof.
    induction xlen; simpl; auto; intros.
    destruct iblock; apply f_equal2.
    - admit.
    - rewrite map_rep_block_below; auto; omega.
    - rewrite selN_updN_ne; auto; omega.
    - replace (S iblock + xstart) with (iblock + S xstart) by omega; auto.
  Qed.

  Theorem iput_update : forall xlen inode l iblock ipos,
    (upd (map (fun i => rep_block (selN l i nil)) (seq 0 xlen)) iblock
       (update items_per_valu itemsz_ok (rep_block (selN l (wordToNat iblock) nil)) ipos
          (Rec.rec2word inode))) =
    (map (fun i => rep_block (selN (upd l iblock (upd (sel l iblock nil) ipos inode)) i nil))
       (seq 0 xlen)).
  Proof.
    unfold upd, sel; intros.
    replace (wordToNat iblock) with (wordToNat iblock + 0) at 2 by omega.
    rewrite iput_update'.
    apply f_equal2; [| auto ].
    apply functional_extensionality; intros.
    replace (wordToNat iblock) with (wordToNat iblock + 0) at 3 4 by omega.
    auto.
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
    step.

    eexists. pred_apply. cancel.

    autorewrite with core. auto.

    step.

    (* Coq bug 3312? *)
    autorewrite with core. auto.

    (* XXX Type checks take forever due to some expansion of addrlen.. *)
  intros;
  try cancel;
  ((eapply pimpl_ok2; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok2_cont; [ solve [ eauto with prog ] | | ])
   || (eapply pimpl_ok3; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok3_cont; [ solve [ eauto with prog ] | | ]));
  intros; subst;
  try ( cancel ).

    apply pimpl_or_r. right.

    norm.
    cancel.

    split. auto.
    split. constructor.

    (* XXX here's where type checks take forever: e.g., if you run [assumption] *)

    pred_apply.
    unfold rep_pair.
    rewrite iput_update; auto.
    cancel.

    cancel.

    cancel; unfold LOG.log_intact; cancel.
    unfold LOG.log_intact; cancel.
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

    (* XXX nested predicates aren't working so well w.r.t. existential variables!
     *
     * We have a goal of the form:
     *
     *   ( ... * [[ (exists ilistlist, rep_pair xp ilistlist) m ]] ) =p=>
     *   (exists ilistlist, ... * [[ (rep_pair xp ilistlist) m ]] )
     *
     * and the existential variable for the right-side ilistlist gets created
     * before we get a chance to look inside the lifted Prop on the left side.
     *
     * Requiring that all existential variables appear at the top level could
     * be a workaround, but it seems quite inconvenient for writing representation
     * invariants about the abstract disk state inside a transaction!
     *)

    intros.
    norm'l.
    apply sep_star_comm in H4.
    (* XXX need to destruct the [exis] that's inside H4.. *)
    admit.
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
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (iget _ _ _) _) => apply iget_ok : prog.
  Hint Extern 1 ({{_}} progseq (iput _ _ _ _) _) => apply iput_ok : prog.

End INODE.
