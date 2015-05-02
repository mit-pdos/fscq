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

Definition byte_bits := 8.
Definition byte := word byte_bits.

Module BYTEFILE.

  Definition block_bytes := valulen / byte_bits.

  Fixpoint list2word (l : list byte) : word (length l * byte_bits).
    refine
      match l with
      | nil => $0
      | x :: l' => _
      end.
    exact (Word.combine x (list2word l')).
  Defined.

  Fixpoint word2list nbytes (w : word (nbytes * byte_bits)) : list byte.
    refine
     (match nbytes as n' return (nbytes = n' -> list byte) with
      | 0 => fun _ => nil
      | S nbytes' => _
      end eq_refl).
    intros; subst.
    refine (split1 byte_bits (nbytes' * byte_bits) w :: _).
    exact (word2list nbytes' (split2 byte_bits (nbytes' * byte_bits) w)).
  Defined.

  Theorem length_word2list : forall nbytes (w : word (nbytes * byte_bits)),
    length (word2list nbytes w) = nbytes.
  Proof.
    induction nbytes; simpl; auto.
  Qed.

  Theorem length_word2list_8 : forall nbytes (w : word (nbytes * byte_bits)),
    nbytes * byte_bits = length (word2list nbytes w) * byte_bits.
  Proof.
    intros; rewrite length_word2list; auto.
  Qed.

  Opaque byte_bits.

  Theorem list2word2list : forall l,
    word2list (length l) (list2word l) = l.
  Proof.
    unfold word2list, list2word, eq_rec_r, eq_rec.
    induction l.
    reflexivity.
    simpl in *.
    f_equal.
    rewrite split1_combine; auto.
    rewrite split2_combine; auto.
  Qed.

  Theorem word2list2word : forall nbytes (w : word (nbytes * byte_bits)),
    list2word (word2list nbytes w) =
    eq_rect (nbytes*byte_bits) word w (length (word2list nbytes w) * byte_bits) (length_word2list_8 _ _).
  Proof.
    induction nbytes; simpl; intros.
    rewrite word0; reflexivity.
    rewrite IHnbytes; clear IHnbytes.
    rewrite eq_rect_split2.
    admit.
  Admitted.

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
      (word2list (length bytes - this_block_bytes) (split2 (this_block_bytes*8) ((length bytes - this_block_bytes)*8) bytes_split))
    end.

  Definition rep (bytes : list byte) (bfattr : BFILE.bfattr) : @pred nat eq_nat_dec valu :=
    (exists blocks,
     [[ length bytes = # (bfattr.(INODE.ISize)) ]] *
     arrayN 0 blocks *
     [[ block_byte_match blocks bytes ]])%pred.

End BYTEFILE.
