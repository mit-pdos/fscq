Require Import Word.
Require Import Arith.
Require Import Eqdep_dec.
Require Import AsyncDisk.
Require Import List ListUtils.
Require Import Omega.
Require Import FunctionalExtensionality.
Import EqNotations.

Set Implicit Arguments.



Definition byte := word 8.
Definition bytes n := word (n * 8).

Definition word2bytes nbits nbytes (H : nbits = nbytes * 8) (w : word nbits) : bytes nbytes :=
  eq_rect nbits word w (nbytes*8) H.
  
Definition byte0 := natToWord 8 0.
Definition bytes0 := (word2bytes 0 eq_refl WO).
  
Definition byte2bytes (b: byte) : bytes 1 := word2bytes 1 eq_refl b.

Definition bcombine (sz1 : nat) (bs1 : bytes sz1) (sz2 : nat) (bs2 : bytes sz2) : bytes (sz1 + sz2).
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (Word.combine bs1 bs2).
Defined.

Definition bsplit1 (sz1 sz2 : nat) (bs : bytes (sz1 + sz2)) : bytes sz1.
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (split1 _ _ bs).
Defined.

Definition bsplit2 (sz1 sz2 : nat) (bs : bytes (sz1 + sz2)) : bytes sz2.
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (split2 _ _ bs).
Defined.

Definition bsplit1_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz1 :=
  bsplit1 sz1 sz2 (eq_rect sz bytes v _ H).

Definition bsplit2_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz2 :=
  bsplit2 sz1 sz2 (eq_rect sz bytes v _ H).

Hint Rewrite Word.combine_split : bytehints.
Hint Rewrite split1_combine : bytehints.
Hint Rewrite split2_combine : bytehints.
Hint Rewrite eq_rect_nat_double : bytehints.
Hint Rewrite <- (eq_rect_eq_dec eq_nat_dec) : bytehints.

Theorem bcombine_bsplit : forall sz1 sz2 (bs : bytes (sz1 + sz2)),
  bcombine (bsplit1 sz1 sz2 bs) (bsplit2 sz1 sz2 bs) = bs.
Proof.
  unfold bcombine, bsplit1, bsplit2, eq_rec_r, eq_rec.
  intros.
  autorewrite with bytehints.
  reflexivity.
Qed.

Theorem bsplit1_bcombine : forall sz1 sz2 (bs : bytes sz1) (z : bytes sz2),
  bsplit1 sz1 sz2 (bcombine bs z) = bs.
Proof.
  unfold bcombine, bsplit1, bsplit2, eq_rec_r, eq_rec.
  intros.
  autorewrite with bytehints.
  reflexivity.
Qed.

Theorem bsplit2_bcombine : forall sz1 sz2 (bs : bytes sz1) (z : bytes sz2),
  bsplit2 sz1 sz2 (bcombine bs z) = z.
Proof.
  unfold bcombine, bsplit1, bsplit2, eq_rec_r, eq_rec.
  intros.
  autorewrite with bytehints.
  reflexivity.
Qed.

Program Fixpoint bsplit_list sz (w: bytes sz) : list byte :=
    match sz with
    | O => nil
    | S sz => bsplit1_dep 1 sz w _ :: bsplit_list (bsplit2_dep 1 sz w _)
    end.

Program Fixpoint bcombine_list (l: list byte): bytes (length l) :=
match l with
 | nil => bytes0
 | h::l' => bcombine (byte2bytes h) (bcombine_list l')
end.

Theorem list2bytes2list: forall (l: list byte), bsplit_list (bcombine_list l) = l.
Proof.
  induction l.
  unfold bsplit_list, bcombine_list. reflexivity.
  simpl; unfold bsplit2_dep.
  simpl; rewrite bsplit2_bcombine.
  rewrite IHl.
  unfold bsplit1_dep.
  simpl; rewrite bsplit1_bcombine.
  unfold byte2bytes.
  reflexivity.
Qed.

Lemma bsplit_list_len: forall sz (b: bytes sz), length (bsplit_list b) = sz.
Proof.
  intros; unfold bsplit_list.
  induction sz. 
  reflexivity. 
  simpl; rewrite IHsz. 
  reflexivity.
Qed.

Lemma bsplit_list_preserve: forall sz (b1 b2: bytes sz), b1 = b2 -> bsplit_list b1 = bsplit_list b2.
Proof. intros. rewrite H. reflexivity. Qed.

Theorem bytes2list2bytes: forall sz (b: bytes sz) H, 
bcombine_list (bsplit_list b) = rew H in b.
Proof.
intros.
induction sz; simpl.
eq_rect_simpl.
unfold bytes0.
simpl.
rewrite word0.
reflexivity.

simpl in H.
inversion H.
rewrite IHsz with (H:= H1).
destruct H1.
unfold byte2bytes.
simpl.
unfold bsplit1_dep, bsplit2_dep; simpl.
rewrite bcombine_bsplit.
eq_rect_simpl.
reflexivity.
Qed.

Notation "'valubytes'" := (Valulen.valubytes).
Notation "'valubytes_is'" := (Valulen.valubytes_is).

Definition valu2bytes (v : valu) : bytes valubytes.
  refine (@word2bytes valulen valubytes _ v).
  rewrite valulen_is. rewrite valubytes_is. reflexivity.
Defined.

Definition bytes2valu (v : bytes valubytes) : valu.
  rewrite valulen_is.
  unfold bytes in *.
  rewrite valubytes_is in *.
  exact v.
Defined.

Theorem bytes2valu2bytes : forall v, valu2bytes (bytes2valu v) = v.
Proof.
  unfold valu2bytes, bytes2valu, eq_rec_r, eq_rec.
  intros.
  rewrite eq_rect_word_mult.
  rewrite eq_rect_nat_double.
  generalize dependent v.
  rewrite valubytes_is.
  rewrite valulen_is.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Theorem valu2bytes2valu : forall v, bytes2valu (valu2bytes v) = v.
Proof.
  unfold valu2bytes, bytes2valu, eq_rec_r, eq_rec.
  intros.
  rewrite eq_rect_word_mult.
  rewrite eq_rect_nat_double.
  generalize dependent v.
  rewrite valubytes_is.
  rewrite valulen_is.
  intros.
  rewrite <- (eq_rect_eq_dec eq_nat_dec).
  reflexivity.
Qed.

Lemma valu2bytes_preserve: forall v1 v2, v1 = v2 -> valu2bytes v1 = valu2bytes v2.
Proof. intros. rewrite H. reflexivity. Qed.

Lemma bcombine_list_contr: forall a l, 
bcombine (byte2bytes a) (bcombine_list l) = bcombine_list (a::l).
Proof. intros; reflexivity. Qed.

Lemma selN_O_bsplit_list: forall sz (bs: bytes (1 + sz)) def,
selN (bsplit_list bs) 0 def = bsplit1 1 sz bs.
Proof.
intros.
simpl.
unfold bsplit1_dep.
reflexivity.
Qed.

Lemma byte2bytes_eq: forall b,
byte2bytes b = b.
Proof.
  intros.
  unfold byte2bytes.
  unfold word2bytes.
  eq_rect_simpl.
  reflexivity.
Qed.
  
