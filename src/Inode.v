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

  Definition rep xp (ilistlist : list (list inode)) :=
    array (IXStart xp)
          (map (fun i => rep_block (selN ilistlist i nil))
          (seq 0 (wordToNat (IXLen xp)))) $1.

  Definition iget T lxp xp iblock ipos rx : prog T :=
    v <- LOG.read_array lxp (IXStart xp) iblock $1 ;
    let iw := Pack.extract itemsz items_per_valu itemsz_ok v ipos in
    let i := Rec.word2rec inodetype iw in
    rx i.

  Definition iput T lxp xp iblock ipos i rx : prog T :=
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

  Theorem iget_ok : forall lxp xp iblock ipos,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]]
    POST:r LOG.rep lxp (ActiveTxn mbase m) *
           [[ r = sel (sel ilistlist iblock nil) ipos inode_zero ]]
    CRASH  LOG.log_intact lxp mbase
    >} iget lxp xp iblock ipos.
  Proof.
    unfold iget.
    hoare.

    eexists. pred_apply. cancel.

    autorewrite with core. auto.

    subst. autorewrite with core. auto.

    unfold LOG.log_intact; cancel.
  Qed.

  Theorem iput_ok : forall lxp xp iblock ipos i,
    {< F mbase m ilistlist,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (F * rep xp ilistlist)%pred m ]] *
           [[ (iblock < IXLen xp)%word ]] *
           [[ (ipos < items_per_valu)%word ]]
    POST:r ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m)) \/
           ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (F * rep xp (upd ilistlist iblock (upd (sel ilistlist iblock nil) ipos i)))%pred m' ]])
    CRASH  LOG.log_intact lxp mbase
    >} iput lxp xp iblock ipos i.
  Proof.
    unfold iput.
    step.

    eexists. pred_apply. cancel.

    autorewrite with core. auto.

    (* Coq bug 3731 *)
  intros;
  try cancel;
  ((eapply pimpl_ok2; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok2_cont; [ solve [ eauto with prog ] | | ])
   || (eapply pimpl_ok3; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok3_cont; [ solve [ eauto with prog ] | | ]));
  intros; subst;
  try ( cancel ).

    autorewrite with core in *.
    auto.

  intros;
  try cancel;
  ((eapply pimpl_ok2; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok2_cont; [ solve [ eauto with prog ] | | ])
   || (eapply pimpl_ok3; [ solve [ eauto with prog ] | ])
   || (eapply pimpl_ok3_cont; [ solve [ eauto with prog ] | | ]));
  intros; subst;
  try ( cancel ).

    autorewrite with core in *.
    apply pimpl_or_r. right.

    norm.
    cancel.

    split. auto.
    split. constructor.
    pred_apply.
    unfold rep.

    cancel.

    (* XXX *) admit.

    cancel.

    cancel; unfold LOG.log_intact; cancel.
    unfold LOG.log_intact; cancel.
  Qed.

End INODE.
