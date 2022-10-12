Require Import Arith Omega NArith Nomega Word.


Ltac set_evars :=
  repeat match goal with
              | [ |- context[?e] ] => is_evar e; let H := fresh in set (H := e)
            end.

Ltac subst_evars :=
  repeat match goal with
              | [ H := ?e |- _ ] => is_evar e; subst H
            end.

Ltac set_evars_in H :=
  repeat match type of H with
              | context[?e] => is_evar e; let E := fresh in set (E := e) in H
            end.



Theorem f_neq : forall {A B : Type} (f : A -> B) x y, f x <> f y -> x <> y.
Proof.
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
   : forall sz n, goodSize sz (N.to_nat n) -> wordToNat (NToWord sz n) = N.to_nat n.
Proof.
  intros. rewrite N2Nat_word. trivial. unfold goodSize in H. rewrite <- Npow2_nat in H. nomega.
Qed.
Hint Rewrite NToWord_nat : W2Nat.

Lemma wordToNat_N : forall sz (w:word sz), N.to_nat (wordToN w) = wordToNat w.
Proof.
  intros. rewrite wordToN_nat. autorewrite with N. trivial.
Qed.
Hint Rewrite wordToNat_N : W2Nat.

Hint Rewrite natToWord_wordToNat : W2Nat.

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
  rewrite plus_comm.
  rewrite plus_ovf_l.
  rewrite plus_comm.
  auto.
Qed.

Theorem plus_ovf_lN : forall sz x y, NToWord sz (wordToN (NToWord sz x) + y) = NToWord sz (x + y).
Proof.
  intros.
  repeat rewrite NToWord_nat.
  repeat rewrite wordToN_nat.
  rewrite <- (N2Nat.id y) at 1.
  rewrite <- Nat2N.inj_add.
  rewrite Nat2N.id.
  rewrite N2Nat.inj_add.
  apply plus_ovf_l.
Qed.

Theorem plus_ovf_rN : forall sz x y, NToWord sz (x + wordToN (NToWord sz y)) = NToWord sz (x + y).
Proof.
  intros.
  rewrite N.add_comm.
  rewrite plus_ovf_lN.
  rewrite N.add_comm.
  auto.
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
  rewrite mult_comm.
  rewrite mul_ovf_l.
  rewrite mult_comm.
  auto.
Qed.

Theorem mul_ovf_lN : forall sz x y, NToWord sz (wordToN (NToWord sz x) * y) = NToWord sz (x * y).
Proof.
  intros.
  repeat rewrite NToWord_nat.
  repeat rewrite wordToN_nat.
  rewrite <- (N2Nat.id y) at 1.
  rewrite <- Nat2N.inj_mul.
  rewrite Nat2N.id.
  rewrite N2Nat.inj_mul.
  apply mul_ovf_l.
Qed.

Theorem mul_ovf_rN : forall sz x y, NToWord sz (x * wordToN (NToWord sz y)) = NToWord sz (x * y).
Proof.
  intros.
  rewrite N.mul_comm.
  rewrite mul_ovf_lN.
  rewrite N.mul_comm.
  auto.
Qed.

Hint Rewrite mul_ovf_l mul_ovf_r : W2Nat.

(* XXX subtraction *)

Theorem Wneq_out : forall sz (n m:word sz),
  n <> m -> wordToNat n <> wordToNat m.
Proof.
  intuition. apply wordToNat_inj in H0; tauto.
Qed.

Lemma divmod_Ndiv_eucl :
  forall a b Sb,
    Pos.to_nat Sb = S b ->
    N.to_nat (fst (N.pos_div_eucl a (N.pos Sb))) =
    fst (Nat.divmod (Pos.to_nat a) b 0 b) /\
    N.to_nat (snd (N.pos_div_eucl a (N.pos Sb))) =
    b - snd (Nat.divmod (Pos.to_nat a) b 0 b).
Proof.
  intros.
  (* Remember the specs of divmod and pow_div_eucl... *)
  generalize (N.pos_div_eucl_spec a (N.pos Sb)); intro HN.
  generalize (N.pos_div_eucl_remainder a (N.pos Sb)); intro HNR.
  remember (N.pos_div_eucl a (N.pos Sb)) as DN; destruct DN.
  generalize (Nat.divmod_spec (Pos.to_nat a) b 0 b); intro HNat.
  remember (Nat.divmod (Pos.to_nat a) b 0 b) as DNat; destruct DNat.
  simpl.
  destruct HNat; auto.
  (* ... and show that they are equivalent *)
  apply (f_equal nat_of_N) in HN.
  rewrite nat_of_Nplus in HN.
  rewrite nat_of_Nmult in HN.
  repeat rewrite positive_N_nat in HN.
  rewrite H in HN.
  rewrite Nat.mul_0_r in H0.
  rewrite Nat.sub_diag in H0.
  repeat rewrite Nat.add_0_r in H0.
  rewrite Nat.mul_comm in H0.
  clear HeqDN. clear HeqDNat.
  rewrite H0 in HN.
  clear H0.
  assert (N.pos Sb <> 0%N).
  apply Nneq_in. simpl.
  generalize (Pos2Nat.is_pos Sb).
  omega.
  apply Nlt_out in HNR; [|auto].
  rewrite positive_N_nat in HNR.
  simpl in HNR.
  assert (N.to_nat n = n1).
  destruct (lt_eq_lt_dec (N.to_nat n) n1); [destruct s; auto|]; [
    remember (n1 - N.to_nat n) as d;
    assert (n1 = d + N.to_nat n) as He by omega |
    remember (N.to_nat n - n1) as d;
    assert (N.to_nat n = d + n1) as He by omega
  ]; assert (d > 0) by omega;
     rewrite He in HN;
     rewrite Nat.mul_add_distr_r in HN;
     destruct (mult_O_le (S b) d); omega.
  intuition.
Qed.

(* The standard library should really define this... *)
Lemma Ninj_div : forall a a' : N, N.to_nat (a / a') = N.to_nat a / N.to_nat a'.
Proof.
  destruct a.
  destruct a'; [|rewrite Nat.div_0_l]; auto.
  replace 0 with (N.to_nat 0) by auto.
  apply Nneq_out; discriminate.
  unfold N.div, Nat.div.
  intro a'.
  case_eq (N.to_nat a').
  + intro He.
    destruct a'.
    reflexivity.
    inversion He.
    generalize (Pos2Nat.is_pos p0).
    omega.
  + intros.
    simpl.
    destruct a'; try discriminate.
    rewrite positive_N_nat in H.
    apply divmod_Ndiv_eucl; auto.
Qed.

Lemma Ninj_mod : forall a a' : N, N.to_nat a' <> 0 ->
  N.to_nat (a mod a') = (N.to_nat a) mod (N.to_nat a').
Proof.
  destruct a.
  destruct a'; [|rewrite Nat.mod_0_l]; auto.
  replace 0 with (N.to_nat 0) by auto.
  apply Nneq_out. discriminate.
  unfold Nmod, Nat.modulo.
  intros.
  case_eq (N.to_nat a').
  omega.
  simpl.
  destruct a'; try discriminate.
  intro n.
  apply divmod_Ndiv_eucl; auto.
Qed.

Hint Rewrite Ninj_div N2Nat.inj_mul N2Nat.inj_add N2Nat.inj_sub : W2Nat.

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


Lemma lt_ovf : forall sz x y, x < wordToNat (natToWord sz y) -> x < y /\ goodSize sz x.
Proof.
  intros.
  destruct (lt_dec y (pow2 sz)); [
    (* Either there's no overflow... *)
    rewrite wordToNat_natToWord_idempotent' in H |
    (* ... or it's true even without the hypothesis *)
    generalize (wordToNat_bound (natToWord sz y))];
  intuition; unfold goodSize in *; omega.
Qed.


Ltac autorewrite_fast_goal_w2nat :=
  set_evars; (rewrite_strat (topdown (hints W2Nat))); subst_evars;
  try autorewrite_fast_goal_w2nat.

Ltac autorewrite_fast_w2nat :=
  match goal with
  | [ H: _ |- _ ] =>
    set_evars_in H; (rewrite_strat (topdown (hints W2Nat)) in H); subst_evars;
    [ try autorewrite_fast_w2nat | try autorewrite_fast_goal_w2nat .. ]
  | [ |- _ ] => autorewrite_fast_goal_w2nat
  end.

(* Do some substitutions [subst] won't. XXX: this doesn't seem very principled; I should think it through *)
Ltac nat_subst :=
  repeat match goal with
  | [ H: # _ = # _ |- _ ] => idtac
  | [ H: # _ = _ |- _ ] => rewrite H
  | [ H: _ = # _ |- _ ] => rewrite <- H
  end.

Ltac goodsizes := idtac;
  repeat match goal with
  | [ w: word ?sz |- _ ] =>
    match goal with
    | [ H: goodSize sz (wordToNat w) |- _ ] => fail 1
    | _ => idtac
    end;
    assert (goodSize sz (wordToNat w)) by (apply wordToNat_bound)
  end.

Ltac word2nat_simpl :=
  try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in || apply N2Nat.inj || apply wordToNat_inj); (* XXX still causes hangs: simpl; *)
  unfold wplus, wminus, wmult, wdiv, wmod, wordBin in *;
  repeat match goal with
  | [ H : _ <> _ |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); nsimp H
  | [ H : _ = _ -> False |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); nsimp H
  | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H || apply (f_equal (@wordToNat _)) in H
             || apply Nlt_out in H || apply Nge_out in H); nsimp H
  end;
  try autorewrite_fast_w2nat;
  repeat match goal with
  | [ H : _ < _ |- _ ] => apply lt_ovf in H; destruct H
  end;
  nat_subst;
  goodsizes.

Ltac word2nat_solve := unfold goodSize in *; subst;
  (omega ||
   congruence ||
   (apply f_equal; word2nat_solve) ||
   ((apply div_le; [| word2nat_auto] ||
     apply zero_lt_pow2 ||
     apply wordToNat_bound || apply wordToNat_good ||
     apply Nat.mod_upper_bound ||
     idtac
    ); solve [auto]
   ) ||
   (apply Nat.div_lt_upper_bound; solve [word2nat_auto]) ||
   (eapply le_lt_trans; [(apply div_le || apply Nat.mod_le) |]; solve [word2nat_auto])
  )

(* XXX does this actually rewrite from the inside out? *)
with word2nat_rewrites :=
  repeat ((match goal with
  | H : context[wordToNat (natToWord ?sz ?n)] |- _ =>
    rewrite (@wordToNat_natToWord_idempotent' sz n) in H; [|clear H]
  | H : context[wordToNat (NToWord ?sz ?n)] |- _ =>
    rewrite (@N2Nat_word' sz n) in H; [|clear H]
  | H : context[wordToNat (NToWord ?sz (wordToN ?a / wordToN ?b))] |- _ =>
    rewrite (@wordToNat_div sz a b); [|clear H]
  | H : context[N.to_nat (?a mod ?b)] |- _ =>
    rewrite (Ninj_mod a b); [|clear H]
  end
  || rewrite wordToNat_natToWord_idempotent'
  || rewrite N2Nat_word'
  || rewrite wordToNat_div
  || rewrite Ninj_mod); word2nat_simpl)

with word2nat_auto :=
  intros; word2nat_simpl; word2nat_rewrites; try word2nat_solve;
  repeat match goal with
  | [ H : _ |- _ ] => apply wordToNat_inj in H
  end.

Lemma wdiv_lt_upper_bound :
  forall sz (a b c:word sz), b <> $0 -> (a < b ^* c)%word -> (a ^/ b < c)%word.
Proof.
  word2nat_auto.
Qed.

Lemma wmod_upper_bound :
  forall sz (a b:word sz), b <> $0 -> (a ^% b < b)%word.
Proof.
  word2nat_auto.
Qed.

Lemma wlt_mult_inj : forall sz (a b c:word sz),
  (a < b ^* c)%word -> wordToNat a < wordToNat b * wordToNat c.
Proof.
  word2nat_auto.
Qed.

Lemma test_1: forall sz (a: word sz), a = a ^+ $ 0.
Proof.
  word2nat_auto.
Qed.
