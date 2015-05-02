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
Require Import Inode.
Require Import Balloc.
Require Import WordAuto.
Require Import GenSep.
Require Import GenSepN.
Require Import ListPred.
Require Import BFile.
Import ListNotations.

Set Implicit Arguments.

Definition bbits := 8.
Definition byte := word bbits.

Module BYTEFILE.

  Definition block_bytes := valulen / bbits.

  Fixpoint list2word elen (l : list (word elen)) : word (length l * elen).
    refine
      match l with
      | nil => $0
      | x :: l' => _
      end.
    exact (Word.combine x (list2word elen l')).
  Defined.

  Fixpoint word2list elen nelem (w : word (nelem * elen)) : list (word elen).
    refine
     (match nelem as n' return (nelem = n' -> list (word elen)) with
      | 0 => fun _ => nil
      | S nelem' => _
      end eq_refl).
    intros; subst.
    refine (split1 elen (nelem' * elen) w :: _).
    exact (word2list elen nelem' (split2 elen (nelem' * elen) w)).
  Defined.

  Theorem length_word2list : forall elen nelem (w : word (nelem * elen)),
    length (word2list elen nelem w) = nelem.
  Proof.
    induction nelem; simpl; auto.
  Qed.

  Theorem length_word2list_mult : forall elen nelem (w : word (nelem * elen)),
    nelem * elen = length (word2list elen nelem w) * elen.
  Proof.
    intros; rewrite length_word2list; auto.
  Qed.

  Theorem list2word2list : forall elen l,
    word2list elen (length l) (list2word l) = l.
  Proof.
    unfold word2list, list2word, eq_rec_r, eq_rec.
    induction l.
    reflexivity.
    simpl in *.
    f_equal.
    rewrite split1_combine; auto.
    rewrite split2_combine; auto.
  Qed.

  Require Import Eqdep_dec.
  Require Import EqdepFacts.

  Theorem word2list2word : forall elen nelem (w : word (nelem * elen)),
    list2word (word2list elen nelem w) =
    eq_rect (nelem*elen) word w (length (word2list elen nelem w) * elen) (length_word2list_mult _ _ _).
  Proof.
    induction nelem; simpl; intros.
    rewrite word0; reflexivity.
    rewrite IHnelem; clear IHnelem.
    rewrite combine_split_eq_rect2.
    f_equal.
    apply (UIP_dec eq_nat_dec).
  Qed.

  Lemma block_byte_match_1 :
    forall x,
      valulen =
      ((Nat.min x block_bytes) * 8) + (block_bytes - (Nat.min x block_bytes)) * 8.
  Proof.
    intros.
    rewrite Nat.mul_sub_distr_r.
    rewrite le_plus_minus_r.
    unfold block_bytes. rewrite valulen_is. vm_compute; auto.
    apply mult_le_compat_r.
    apply Min.le_min_r.
  Qed.

  Lemma block_byte_match_2 :
    forall lenbytes x,
      lenbytes * 8 =
      (Nat.min lenbytes x) * 8 + (lenbytes - (Nat.min lenbytes x)) * 8.
  Proof.
    intros.
    rewrite Nat.mul_sub_distr_r.
    rewrite le_plus_minus_r.
    auto.
    apply mult_le_compat_r.
    apply Min.le_min_l.
  Qed.

  Fixpoint block_byte_match (blocks : list valu) (bytes : list byte) : Prop :=
    match blocks with
    | nil => bytes = nil
    | b :: blocks' =>
      let this_block_bytes := Nat.min (length bytes) block_bytes in
      let b_split := eq_rect valulen word b
        (this_block_bytes*8 + (block_bytes - this_block_bytes) * 8) (block_byte_match_1 _) in
      let bytes_split := eq_rect ((length bytes) * 8) word (list2word bytes)
        (this_block_bytes*8 + (length bytes - this_block_bytes) * 8) (block_byte_match_2 _ _) in
      (split1 (this_block_bytes*8) ((block_bytes - this_block_bytes)*8) b_split =
       split1 (this_block_bytes*8) ((length bytes - this_block_bytes)*8) bytes_split) /\
      block_byte_match blocks'
      (word2list bbits (length bytes - this_block_bytes) (split2 (this_block_bytes*8) ((length bytes - this_block_bytes)*8) bytes_split))
    end.

  Definition rep (bytes : list byte) (bfattr : BFILE.bfattr) : @pred nat eq_nat_dec valu :=
    (exists blocks,
     [[ length bytes = # (bfattr.(INODE.ISize)) ]] *
     arrayN 0 blocks *
     [[ block_byte_match blocks bytes ]])%pred.

End BYTEFILE.
