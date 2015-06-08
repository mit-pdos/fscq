Require Import Word.
Require Import Arith.
Require Import Eqdep_dec.

Set Implicit Arguments.

Definition byte := word 8.
Definition bytes n := word (n * 8).

Definition word2bytes nbits nbytes (H : nbits = nbytes * 8) (w : word nbits) : bytes nbytes :=
  eq_rect nbits word w (nbytes*8) H.

Definition bcombine (sz1 : nat) (bs1 : bytes sz1) (sz2 : nat) (bs2 : bytes sz2) : bytes (sz1 + sz2).
  unfold bytes in *.
  rewrite Nat.mul_add_distr_r in *.
  exact (combine bs1 bs2).
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

Hint Rewrite combine_split : bytehints.
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
