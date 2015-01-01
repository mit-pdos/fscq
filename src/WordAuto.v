Require Import Arith Omega NArith Nomega Word.


Theorem f_neq : forall {A B : Type} (f : A -> B) x y, f x <> f y -> x <> y.
  intros. unfold not. intro He. rewrite He in H. auto.
Qed.

Create HintDb W2Nat discriminated. (* Straightforward simplifications *)

Hint Rewrite Npow2_nat : W2Nat.

Lemma N2Nat_word : forall sz n, (n < Npow2 sz)%N -> wordToNat (NToWord sz n) = N.to_nat n.
Proof.
  intros. rewrite NToWord_nat. apply wordToNat_natToWord_idempotent.
  rewrite N2Nat.id. assumption.
Qed.
Lemma N2Nat_word'
   : forall sz n, N.to_nat n < pow2 sz -> wordToNat (NToWord sz n) = N.to_nat n.
Proof.
  intros. rewrite N2Nat_word. trivial. rewrite <- Npow2_nat in H. nomega.
Qed.
Hint Rewrite NToWord_nat : W2Nat.
Lemma wordToNat_N : forall sz (w:word sz), N.to_nat (wordToN w) = wordToNat w.
Proof.
  intros. rewrite wordToN_nat. autorewrite with N. trivial.
Qed.
Hint Rewrite wordToNat_N : W2Nat.

Theorem plus_ovf_l : forall sz x y, $ (wordToNat (natToWord sz x) + y) = natToWord sz (x + y).
Proof.
  intros.
  destruct (wordToNat_natToWord sz x) as [? [Heq ?]]; rewrite Heq.
  replace (x - x0 * pow2 sz + y) with (x + y - x0 * pow2 sz) by omega.
  apply drop_sub; omega.
Qed.
Theorem plus_ovf_r : forall sz x y, $ (x + wordToNat (natToWord sz y)) = natToWord sz (x + y).
Proof.
  intros.
  destruct (wordToNat_natToWord sz y) as [? [Heq ?]]; rewrite Heq.
  replace (x + (y - x0 * pow2 sz)) with (x + y - x0 * pow2 sz) by omega.
  apply drop_sub; omega.
Qed.

Hint Rewrite plus_ovf_l plus_ovf_r : W2Nat.

Theorem mul_ovf_l : forall sz x y, $ (wordToNat (natToWord sz x) * y) = natToWord sz (x * y).
Proof.
  intros.
  destruct (wordToNat_natToWord sz x) as [? [Heq ?]]; rewrite Heq.
  rewrite Nat.mul_sub_distr_r.
  replace (x0 * pow2 sz * y) with (x0 * y * pow2 sz) by ring.
  apply drop_sub.
  replace (x0 * y * pow2 sz) with (x0 * pow2 sz * y) by ring.
  apply mult_le_compat_r; auto.
Qed.
Theorem mul_ovf_r : forall sz x y, $ (x * wordToNat (natToWord sz y)) = natToWord sz (x * y).
Proof.
  intros.
  destruct (wordToNat_natToWord sz y) as [? [Heq ?]]; rewrite Heq.
  rewrite Nat.mul_sub_distr_l.
  rewrite mult_assoc.
  apply drop_sub.
  rewrite <- mult_assoc.
  apply mult_le_compat_l; auto.
Qed.

Hint Rewrite mul_ovf_l mul_ovf_r : W2Nat.

(* XXX subtraction *)

Theorem Wneq_out : forall sz (n m:word sz),
  n <> m -> wordToNat n <> wordToNat m.
Proof.
  intuition. apply wordToNat_inj in H0; tauto.
Qed.

(* The standard library should really define this... *)
Lemma Ninj_div : forall a a' : N, N.to_nat (a / a') = N.to_nat a / N.to_nat a'. admit. Qed.
Lemma Ninj_mod : forall a a' : N, N.to_nat (a mod a') = (N.to_nat a) mod (N.to_nat a'). admit. Qed.
Hint Rewrite Ninj_div Ninj_mod N2Nat.inj_mul N2Nat.inj_add N2Nat.inj_sub : W2Nat.

Lemma wordToNat_mult : forall sz (n m:word sz),
  NToWord sz (wordToN n * wordToN m)%N = $ (wordToNat n * wordToNat m).
Proof.
  intros.
  replace (NToWord sz (wordToN n * wordToN m)) with (n ^* m) by auto.
  replace n with (natToWord sz (wordToNat n)) at 1 by (apply natToWord_wordToNat).
  replace m with (natToWord sz (wordToNat m)) at 1 by (apply natToWord_wordToNat).
  rewrite <- natToWord_mult. auto.
Qed.

Hint Rewrite wordToNat_mult : W2Nat.

Lemma div_le : forall a b, b <> 0 -> a / b <= a.
Proof.
  intros.
  destruct (Nat.eq_dec a 0).
  rewrite e. rewrite Nat.div_0_l by assumption. omega.
  destruct (Nat.eq_dec b 1).
  rewrite e. rewrite Nat.div_1_r. omega.
  apply Nat.lt_le_incl.
  apply Nat.div_lt; omega.
Qed.



Theorem wordToNat_div : forall sz (a b : word sz), wordToNat b <> 0 ->
  wordToNat (NToWord sz (wordToN a / wordToN b)) = wordToNat a / wordToNat b.
Proof.
  intros.
  rewrite N2Nat_word.
  rewrite Ninj_div.
  repeat rewrite wordToNat_N. trivial.
  apply Nlt_in.
  autorewrite with W2Nat.
  apply le_lt_trans with (m := wordToNat a).
  apply div_le; assumption.
  apply wordToNat_bound.
Qed.


Lemma lt_ovf : forall sz x y, x < wordToNat (natToWord sz y) -> x < y /\ x < pow2 sz.
Proof.
  intros.
  destruct (lt_dec y (pow2 sz)); [
    (* Either there's no overflow... *)
    rewrite wordToNat_natToWord_idempotent' in H |
    (* ... or it's true even without the hypothesis *)
    generalize (wordToNat_bound (natToWord sz y))];
  intuition; omega.
Qed.


Lemma zero_lt_pow2 : forall sz, 0 < pow2 sz.
Proof.
  induction sz; simpl; omega.
Qed.

Ltac word2nat_simpl :=
  try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in); simpl;
  unfold wplus, wminus, wmult, wdiv, wmod, wordBin in *;
  repeat match goal with
  | [ H : _ <> _ |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); nsimp H
  | [ H : _ = _ -> False |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); nsimp H
  | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H || apply (f_equal wordToNat) in H
             || apply Nlt_out in H || apply Nge_out in H); nsimp H
  end;
  autorewrite with W2Nat in *;
  repeat match goal with
  | [ H : _ < _ |- _ ] => apply lt_ovf in H; destruct H
  end.

(* XXX this should probably word2nat_auto side goals -- mutual recursion? *)
Ltac word2nat_solve := omega || ((apply div_le; [| word2nat_solve] || apply zero_lt_pow2 || apply wordToNat_bound || (eapply le_lt_trans; [(apply div_le || apply Nat.mod_le) |]; word2nat_solve) || idtac); solve [auto]).


(* XXX does this actually rewrite from the inside out? *)
Check wordToNat_div.
Ltac word2nat_rewrites :=
  repeat ((match goal with
  | H : context[wordToNat (natToWord ?sz ?n)] |- _ =>
    rewrite (@wordToNat_natToWord_idempotent' sz n) in H; [|clear H]
  | H : context[wordToNat (NToWord ?sz ?n)] |- _ =>
    rewrite (@N2Nat_word' sz n) in H; [|clear H]
  | H : context[wordToNat (NToWord ?sz (wordToN ?a / wordToN ?b))] |- _ =>
    rewrite (@wordToNat_div sz a b); [|clear H]
  end
  || rewrite wordToNat_natToWord_idempotent'
  || rewrite N2Nat_word'
  || rewrite wordToNat_div); autorewrite with W2Nat in *).

Ltac word2nat_auto :=
  intros; word2nat_simpl; word2nat_rewrites; try word2nat_solve.

Lemma wdiv_lt_upper_bound :
  forall sz (a b c:word sz), b <> $0 -> (a < b ^* c)%word -> (a ^/ b < c)%word.
Proof.
  word2nat_auto.
  apply Nat.div_lt_upper_bound; intuition.
Qed.

Lemma wmod_upper_bound :
  forall sz (a b:word sz), b <> $0 -> (a ^% b < b)%word.
Proof.
  word2nat_auto.
  apply Nat.mod_upper_bound; assumption.
Qed.

Lemma wlt_mult_inj : forall sz (a b c:word sz),
  (a < b ^* c)%word -> wordToNat a < wordToNat b * wordToNat c.
Proof.
  word2nat_auto.
Qed.
