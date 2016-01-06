Require Import Prog.
Require Import Word.
Require Import FSLayout.
Require Import Log.
Require Import BasicProg.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import GenSepAuto.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import EqdepFacts.
Require Import Arith.
Require Import AsyncDisk.
Require Import ListUtils.

Set Implicit Arguments.


Definition hash2 sz1 sz2 (a : word sz1) (b : word sz2) :=
  hash_fwd (Word.combine a b).

Inductive hash_list_rep : (list valu) -> word hashlen -> hashmap -> Prop :=
  | HL_nil : forall hl hm,
      hl = hash_fwd default_valu ->
      hash_list_rep nil hl hm
  | HL_cons : forall l hl hl' x hm,
      hash_list_rep l hl hm ->
      hl' = hash2 x hl ->
      hashmap_get hm hl' = Some (existT _ _ (Word.combine x hl)) ->
      hash_list_rep (x :: l) hl' hm.

Inductive hashmap_subset : list (word hashlen * {sz : nat & word sz}) -> hashmap -> hashmap -> Prop  :=
  | HS_nil : forall hm,
      hashmap_subset nil hm hm
  | HS_cons : forall h sz (k : word sz) l hm hm',
      hashmap_subset l hm hm' ->
      hash_safe hm' h k ->
      hashmap_subset ((h, (existT _ _ k)) :: l) hm (upd_hashmap' hm' h k).


Ltac existT_wordsz_neq H :=
  let Hx := fresh in
  inversion H as [ Hx ];
  rewrite <- plus_0_r in Hx at 1;
  apply plus_reg_l in Hx;
  inversion Hx.

Ltac existT_wordsz_eq H :=
  let Hx := fresh in
  pose proof (eq_sigT_snd H) as Hx;
  autorewrite with core in Hx;
  try apply combine_inj in Hx.

Ltac contradict_hashmap_get_default H hm :=
  let Hx := fresh in
  contradict H;
  destruct hm; unfold hashmap_get, default_hash;
  destruct (weq (hash_fwd default_valu) (hash_fwd default_valu));
  intro Hx; try existT_wordsz_neq Hx;
  intuition.

Theorem hashmap_get_default : forall hm,
  hashmap_get hm default_hash = Some (existT _ _ default_valu).
Proof.
  unfold hashmap_get.
  destruct hm; destruct (weq default_hash default_hash);
  intuition.
Qed.

Theorem hash_list_rep_upd : forall l hl hm h sz (k : word sz),
  hash_list_rep l hl hm ->
  hash_safe hm h k ->
  hash_list_rep l hl (upd_hashmap' hm h k).
Proof.
  induction l; intros.
  constructor. inversion H. auto.
  inversion H.
  eapply HL_cons; eauto.

  unfold upd_hashmap', hashmap_get.
  destruct (weq hl default_hash) eqn:Hhl.
  - rewrite e in H7.
    rewrite hashmap_get_default in H7.
    auto.
  - destruct (weq h hl) eqn:Hhl'; auto.
    subst.
    unfold hash_safe in H0.
    inversion H0 as [ Hget | Hget ];
      rewrite Hget in H7;
      inversion H7; auto.
Qed.

Theorem hash_list_rep_subset : forall hkl l hl hm hm',
  hashmap_subset hkl hm hm' ->
  hash_list_rep l hl hm ->
  hash_list_rep l hl hm'.
Proof.
  induction hkl; intros.
  inversion H. congruence.

  inversion H. subst.
  apply hash_list_rep_upd; auto.
  eapply IHhkl; eauto.
Qed.


Definition hash_list T values hm rx : prog T :=
  let^ (default_hash, hm') <- Hash default_valu hm;
  let^ (hash, hm') <- For i < $ (length values)
  Ghost [ crash ]
  Loopvar [ hash hm' ]
  Continuation lrx
  Invariant
    [[ hash_list_rep (rev (firstn #i values)) hash hm' ]] *
    [[ exists l, hashmap_subset l hm hm' ]]
  OnCrash crash
  Begin
    let^ (hash, hm') <- Hash (Word.combine (sel values #i default_valu) hash) hm';
    lrx ^(hash, hm')
  Rof ^(default_hash, hm');
  rx ^(hash, hm').


Theorem hash_list_ok : forall values hm,
  {< (_ : unit) ,
  PRE
    emp * [[ goodSize addrlen (length values) ]]
  POST RET:^(hash, hm')
    emp * [[ hash_list_rep (rev values) hash hm' ]] *
          [[ exists l, hashmap_subset l hm hm' ]]
  CRASH
    emp
  >} hash_list values hm.
Proof.
  unfold hash_list.
  step.
  step; try apply HL_nil; auto.

  rewrite H7.
  exists ((a, existT _ _ default_valu) :: nil).
  econstructor; eauto. constructor.

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

  step.
  step.

  (* Loop invariant. *)
  - destruct (rev (firstn # (m ^+ $ (1)) values)) eqn:Hrev_values.
    + simpl in Hlength. inversion Hlength.
    + assert (Hl: rev l0 = (firstn # (m) values)).
        replace l0 with (rev (rev l0)) in Hrev_values;
          try apply rev_involutive.
        rewrite <- rev_unit in Hrev_values.
        erewrite wordToNat_plusone in Hrev_values; eauto.
        apply rev_injective in Hrev_values.

        rewrite <- removelast_firstn;
          try (apply lt_word_lt_nat; auto).
        replace (rev l0) with (rev l0 ++ removelast (w :: nil)).
        rewrite <- removelast_app.
        rewrite Hrev_values.
        auto.

        intuition. inversion H6.
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
      apply upd_hashmap'_eq.
      intuition.
      unfold hash_safe in H14.
      rewrite H6 in H14.
      inversion H14 as [ Hdef | Hdef ];
      contradict_hashmap_get_default Hdef a2.

  - eexists. subst.
    econstructor; eauto.

  (* Loop invariant implies post-condition. *)
  - step.
    assert (Hfirstn: firstn # (natToWord addrlen (length values)) values = values).
      rewrite wordToNat_natToWord_idempotent'; auto.
      apply firstn_oob. auto.
    rewrite <- Hfirstn. auto.

  Grab Existential Variables.
  all: constructor.
Qed.

Hint Extern 1 ({{_}} progseq (hash_list _ _) _) => apply hash_list_ok : prog.


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
