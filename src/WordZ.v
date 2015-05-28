Require Import Word.
Require Import ZArith.

Set Implicit Arguments.

Definition wordToZ sz (w : word sz) : Z := Z.of_N (wordToN w).
Definition ZToWordTrunc sz (z : Z) : word sz :=
  match z with
  | Z0 => $0
  | Zpos p => posToWord sz p
  | Zneg p => wneg (posToWord sz p)
  end.

Definition ZToWord sz (z : Z) : option (word sz) :=
  match z with
  | Z0 => Some $0
  | Zpos p =>
    match Z.compare z (2 ^ (Z.of_nat sz))%Z with
    | Lt => Some (posToWord sz p)
    | _ => None
    end
  | Zneg p => None
  end.

Theorem wordToZ_nat : forall sz (w : word sz), wordToZ w = Z_of_nat (wordToNat w).
Proof.
  unfold wordToZ.
  intros.
  rewrite wordToN_nat.
  unfold Z.of_N, N.of_nat, Z.of_nat.
  destruct # (w); auto.
Qed.

Theorem ZToWordTrunc_wordToZ : forall sz w,
  ZToWordTrunc sz (wordToZ w) = w.
Proof.
  intros.
  rewrite wordToZ_nat.
  unfold Z.of_nat.
  case_eq (# w); simpl; intros.
  - rewrite <- natToWord_wordToNat.
    congruence.
  - rewrite posToWord_nat.
    rewrite SuccNat2Pos.id_succ.
    rewrite <- natToWord_wordToNat.
    congruence.
Qed.

Lemma Z_pow_Npow2 : forall p,
  Z.pow 2 (Z.of_nat p) = Z.of_N (Npow2 p).
Proof.
  intros.
  rewrite pow2_N.
  rewrite nat_N_Z.
  induction p; auto.
  rewrite Nat2Z.inj_succ.
  rewrite Z.pow_succ_r.
  rewrite IHp.
  rewrite Z.mul_comm.
  rewrite <- Zplus_diag_eq_mult_2.
  simpl.
  rewrite Nat2Z.inj_add.
  rewrite <- plus_n_O.
  reflexivity.
  replace (0%Z) with (Z.of_nat 0) by reflexivity.
  apply inj_le.
  omega.
Qed.

Theorem wordToZ_ZToWordTrunc_idempotent : forall sz z,
  (0 <= z < (2 ^ (Z.of_nat sz)))%Z -> wordToZ (ZToWordTrunc sz z) = z.
Proof.
  intros.
  rewrite wordToZ_nat.
  destruct z; simpl.
  - rewrite roundTrip_0. reflexivity.
  - rewrite posToWord_nat.
    rewrite wordToNat_natToWord_idempotent.
    rewrite positive_nat_Z; reflexivity.
    rewrite positive_nat_N.
    inversion H.
    apply N2Z.inj_lt.
    rewrite positive_N_Z.
    rewrite Z_pow_Npow2 in H1.
    auto.
  - inversion H.
    compute in *.
    congruence.
Qed.

Lemma wordToZ_bound : forall sz (w : word sz),
  (0 <= wordToZ w < (2 ^ (Z.of_nat sz)))%Z.
Proof.
  unfold wordToZ; split.
  - apply N2Z.is_nonneg.
  - rewrite wordToN_nat.
    rewrite Z_pow_Npow2.
    rewrite <- (Nnat.N2Nat.id (Npow2 sz)).
    rewrite Npow2_nat.
    repeat rewrite nat_N_Z.
    apply Nat2Z.inj_lt.
    apply wordToNat_bound.
Qed.

Theorem ZToWord_wordToZ : forall sz w,
  ZToWord sz (wordToZ w) = Some w.
Proof.
  intros.
  pose proof (ZToWordTrunc_wordToZ w).
  destruct (wordToZ_bound w).
  remember (wordToZ w).
  destruct z.
  - simpl in *; congruence.
  - unfold ZToWord.
    replace (Z.compare (Z.pos p) (2 ^ Z.of_nat sz)%Z) with (Lt).
    unfold ZToWordTrunc in H; congruence.
  - pose proof (Pos2Z.neg_is_neg p).
    apply Zle_not_lt in H0.
    congruence.
Qed.

Theorem wordToZ_ZToWord : forall sz w z,
  ZToWord sz z = Some w ->
  wordToZ w = z.
Proof.
  unfold ZToWord; intros.
  destruct z.
  - inversion H. unfold wordToZ.
    rewrite wordToN_nat. rewrite roundTrip_0. reflexivity.
  - destruct (Z.compare (Z.pos p) (2 ^ Z.of_nat sz))%Z eqn:Heq; try congruence.
    assert (Z.pos p < 2 ^ Z.of_nat sz)%Z by (apply Z.compare_lt_iff; auto).
    inversion H.
    replace (posToWord sz p) with (ZToWordTrunc sz (Z.pos p)) by reflexivity.
    rewrite wordToZ_ZToWordTrunc_idempotent; auto.
    split; auto.
    apply Zle_0_pos.
  - congruence.
Qed.
