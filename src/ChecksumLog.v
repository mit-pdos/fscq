Require Import Prog.
Require Import Word.
Require Import FSLayout.
Require Import Log.
Require Import BasicProg.
Require Import Compare.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import GenSep.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import EqdepFacts.
Require Import Arith.

Set Implicit Arguments.


Definition default_valu : valu := $0.

Definition hash2 sz1 sz2 (a : word sz1) (b : word sz2) :=
  hash_fwd (Word.combine a b).

Inductive hash_list_rep : (list valu) -> word hashlen -> Prop :=
  | HL_nil : forall hl,
      hl = hash_fwd default_valu ->
      hash_inv hl = existT _ _ default_valu ->
      hash_list_rep nil hl
  | HL_cons : forall values hvalues hvalues' x,
      hash_list_rep values hvalues ->
      hvalues' = hash2 x hvalues ->
      hash_inv hvalues' = existT _ _ (Word.combine x hvalues) ->
      hash_list_rep (x :: values) hvalues'.


(* Program that hashes a list of values into a single hash value. *)
Definition hash_list T values rx : prog T :=
    default_hash <- Hash default_valu;
    let^ (hash) <- For i < $ (length values)
    Ghost [ crash ]
    Loopvar [ hash ]
    Continuation lrx
    Invariant
      [[ hash_list_rep (rev (firstn #i values)) hash ]]
    OnCrash crash
    Begin
      hash <- Hash (Word.combine (sel values i default_valu) hash);
      lrx ^(hash)
    Rof ^(default_hash);
    rx hash.


Theorem hash_list_ok : forall values,
  {< (_ : unit) ,
  PRE
    emp * [[ goodSize addrlen (length values) ]]
  POST RET:hash
    emp * [[ hash_list_rep (rev values) hash ]]
  CRASH
    emp
  >} hash_list values.
Proof.
  unfold hash_list.
  step.
  step.
  constructor; auto.
  step.
  step.

  assert (Hlength: length (rev (firstn # (m ^+ $ (1)) values)) = S (# (m))).
    rewrite rev_length.
    rewrite firstn_length.
    erewrite wordToNat_plusone; eauto.
    destruct (le_dec (S (# m)) (length values)).
      apply Min.min_l. auto.

      apply not_lt in n.
      apply wlt_lt in H.
      rewrite wordToNat_natToWord_idempotent' in H; auto.
      intuition.

  (* Loop invariant. *)
  - destruct (rev (firstn # (m ^+ $ (1)) values)) eqn:Hrev_values.
    + simpl in Hlength. inversion Hlength.
    + assert (Hl: rev l = (firstn # (m) values)).
        replace l with (rev (rev l)) in Hrev_values;
          try apply rev_involutive.
        rewrite <- rev_unit in Hrev_values.
        erewrite wordToNat_plusone in Hrev_values; eauto.
        apply rev_injective in Hrev_values.

        rewrite <- removelast_firstn;
          try (apply lt_word_lt_nat; auto).
        replace (rev l) with (rev l ++ removelast (w :: nil)).
        rewrite <- removelast_app.
        rewrite Hrev_values.
        auto.

        intuition. inversion H3.
        simpl. rewrite app_nil_r. auto.

      rewrite <- rev_involutive in Hl.
      apply rev_injective in Hl.
      rewrite Hl. eauto.
      assert (Hw: selN (firstn # (m ^+ $ (1)) values) (# m) default_valu = w).
        rewrite <- rev_involutive in Hrev_values.
        apply rev_injective in Hrev_values.
        rewrite Hrev_values.
        simpl. apply selN_last. rewrite rev_length.
        simpl in Hlength. apply eq_add_S in Hlength.
        auto.
      rewrite selN_firstn in Hw;
        try (erewrite wordToNat_plusone; eauto).
      eapply HL_cons; subst; eauto.

  (* Loop invariant implies post-condition. *)
  - step.
    assert (Hfirstn: firstn # (natToWord addrlen (length values)) values = values).
      rewrite wordToNat_natToWord_idempotent'; auto.
      apply firstn_oob. auto.
    rewrite <- Hfirstn. auto.

  Grab Existential Variables.
  all: eauto.
Qed.

Hint Extern 1 ({{_}} progseq (hash_list _) _) => apply hash_list_ok : prog.

Ltac existT_wordsz_neq H :=
  inversion H as [ Hvalulen ];
  rewrite <- plus_0_r in Hvalulen;
  apply plus_reg_l in Hvalulen;
  inversion Hvalulen.

Ltac existT_wordsz_eq H :=
  pose proof (eq_sigT_snd H);
  autorewrite with core in *.

Theorem hash_list_injective : forall l1 l2 hv,
  hash_list_rep l1 hv -> hash_list_rep l2 hv -> l1 = l2.
Proof.
  induction l1;
    intros;
    inversion H; inversion H0;
    unfold hash2 in *; intuition;
    subst; auto.

  - rewrite H6 in H2. existT_wordsz_neq H2.
  - rewrite H6 in H8. existT_wordsz_neq H8.
  - rewrite H9 in H6.
    existT_wordsz_eq H6.
    apply combine_inj in H1.
    intuition.
    apply IHl1 in H7; congruence.
Qed.