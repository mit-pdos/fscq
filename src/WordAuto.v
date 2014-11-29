Require Import Arith Omega NArith Nomega Word.

Theorem f_neq : forall {A B : Type} (f : A -> B) x y, f x <> f y -> x <> y.
  intros. unfold not. intro He. rewrite He in H. auto.
Qed.

Create HintDb W2Nat discriminated. (* Straightforward simplifications *)
Create HintDb W2Nat' discriminated. (* Also simplifications generating side conditions *)

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
Hint Rewrite NToWord_nat N2Nat_word' : W2Nat'.
Lemma wordToNat_N : forall sz (w:word sz), N.to_nat (wordToN w) = wordToNat w.
Proof.
  intros. rewrite wordToN_nat. autorewrite with N. trivial.
Qed.
Hint Rewrite wordToNat_N : W2Nat W2Nat'.

Check wordToNat_natToWord_idempotent.

Lemma wordToNat_natToWord_idempotent'
   : forall sz n:nat, n < pow2 sz -> wordToNat (natToWord sz n) = n.
Proof.
  intros. apply wordToNat_natToWord_idempotent. rewrite pow2_N. nomega.
Qed.
Hint Rewrite wordToNat_natToWord_idempotent' : W2Nat'.

Theorem Wneq_out : forall sz (n m:word sz),
  n <> m -> wordToNat n <> wordToNat m.
Proof.
  intuition. apply wordToNat_inj in H0; tauto.
Qed.

(* The standard library should really define this... *)
Lemma Ninj_div : forall a a' : N, N.to_nat (a / a') = N.to_nat a / N.to_nat a'. admit. Qed.
Hint Rewrite Ninj_div : W2Nat W2Nat'.

Lemma wordToNat_mult : forall sz (n m:word sz), wordToNat n * wordToNat m < pow2 sz ->
  wordToNat (n ^* m) = wordToNat n * wordToNat m.
Proof.
  intros.
  replace n with (natToWord sz (wordToNat n)) at 1 by (apply natToWord_wordToNat).
  replace m with (natToWord sz (wordToNat m)) at 1 by (apply natToWord_wordToNat).
  rewrite <- natToWord_mult. rewrite wordToNat_natToWord_idempotent. trivial.
  apply Nlt_in. autorewrite with N. rewrite Npow2_nat. assumption.
Qed.

Hint Rewrite wordToNat_mult : W2Nat'.

(* XXX this needs some restructuring *)
Ltac word2nat_with tac :=
  try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in); simpl;
    repeat (progress autorewrite with W2Nat in *; simpl);
    unfold wplus, wminus, wmult, wdiv, wordBin;
    tac;
    repeat match goal with
           (* XXX the 1 and 2 here are fragile -- is there a better way? *)
           | [ H : _ <> $ _ |- _ ] => rewrite <- natToWord_wordToNat in H at 1; apply (f_neq (natToWord _)) in H
           | [ H : $ _ <> _ |- _ ] => rewrite <- natToWord_wordToNat in H at 2; apply (f_neq (natToWord _)) in H
           (* XXX need more of these *)
           | [ H : _ <> _ |- _ ] => apply Nneq_out in H; nsimp H
           | [ H : _ = _ -> False |- _ ] => apply Nneq_out in H; nsimp H
           | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H
             || apply Nlt_out in H || apply Nge_out in H); nsimp H
           end;
    repeat (progress autorewrite with W2Nat in *; simpl).

(* These tactics try to convert statements about words into statements about nats *)
Ltac word2nat := word2nat_with idtac.

Ltac word2nat' := word2nat_with ltac:(autorewrite with W2Nat' in *).

Ltac womega := word2nat'; omega.