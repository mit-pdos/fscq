Require Import Prog.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import Word.
Require Import FSLayout.
Require Import BasicProg.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import EqdepFacts.
Require Import Arith.
Require Import ListUtils.

Set Implicit Arguments.


Definition hash_list T values rx : prog T :=
  hash <- Hash default_valu;
  let^ (hash) <- For i < $ (length values)
  Hashmap hm'
  Ghost [ crash ]
  Loopvar [ hash ]
  Continuation lrx
  Invariant
    [[ hash_list_rep (rev (firstn #i values)) hash hm' ]]
  OnCrash crash
  Begin
    hash <- Hash (Word.combine (sel values i default_valu) hash);
    lrx ^(hash)
  Rof ^(hash);
  rx hash.


Theorem hash_list_ok : forall values,
  {< (_ : unit) ,
  PRE:hm
    emp * [[ goodSize addrlen (length values) ]]
  POST:hm' RET:hash
    emp * [[ hash_list_rep (rev values) hash hm' ]]
  CRASH:hm'
    emp * [[ exists i hash, hash_list_rep (rev (firstn i values)) hash hm' ]]
  >} hash_list values.
Proof.
  unfold hash_list.
  step.
  step; try apply HL_nil; auto.

  assert (Hlength: length (rev (firstn # (m ^+ $ (1)) values)) = S (# (m))).
    rewrite rev_length.
    rewrite firstn_length.
    erewrite wordToNat_plusone; eauto.
    destruct (le_dec (S (# m)) (length values)).
      apply Min.min_l. auto.

      apply not_lt in n.
      apply wlt_lt in H0.
      rewrite wordToNat_natToWord_idempotent' in H0; auto.
      intuition.

  step.
  step.

  (* Loop invariant. *)
  - destruct (rev (firstn # (m ^+ $ (1)) values)) eqn:Hrev_values.
    + simpl in Hlength. inversion Hlength.
    + assert (Hl: rev l2 = (firstn # (m) values)).
        replace l2 with (rev (rev l2)) in Hrev_values;
          try apply rev_involutive.
        rewrite <- rev_unit in Hrev_values.
        erewrite wordToNat_plusone in Hrev_values; eauto.
        apply rev_injective in Hrev_values.

        rewrite <- removelast_firstn;
          try (apply lt_word_lt_nat; auto).
        replace (rev l2) with (rev l2 ++ removelast (w :: nil)).
        rewrite <- removelast_app.
        rewrite Hrev_values.
        auto.

        intuition. inversion H7.
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
      subst.

      econstructor.
      apply hash_list_rep_upd; eauto.
      auto.
      unfold sel in *.
      apply upd_hashmap'_eq.
      intuition.
      unfold hash_safe in *.
      rewrite H7 in H16.
      inversion H16 as [ Hdef | Hdef ];
      contradict_hashmap_get_default Hdef hm0.

  (* Loop invariant implies post-condition. *)
  - step.
    assert (Hfirstn: firstn # (natToWord addrlen (length values)) values = values).
      rewrite wordToNat_natToWord_idempotent'; auto.
      apply firstn_oob. auto.
    rewrite <- Hfirstn. auto.

  - repeat eexists. instantiate (i:=0). econstructor. eauto.
  - repeat eexists. instantiate (i:=0). econstructor. eauto.

  Grab Existential Variables.
  all: eauto; unfold DecEq; apply weq.
Qed.

Hint Extern 1 ({{_}} progseq (hash_list _) _) => apply hash_list_ok : prog.


Theorem hash_list_injective : forall l1 l2 hv hm,
  hash_list_rep l1 hv hm -> hash_list_rep l2 hv hm -> l1 = l2.
Proof.
  induction l1;
    intros;
    inversion H; inversion H0;
    unfold hash2 in *; intuition;
    subst; auto.

  contradict_hashmap_get_default H6 hm.

  rewrite H8 in H7.
  contradict_hashmap_get_default H7 hm.

  rewrite H7 in H10.
  inversion H10.
  existT_wordsz_eq H2.
  intuition.
  apply IHl1 in H8; congruence.
Qed.
