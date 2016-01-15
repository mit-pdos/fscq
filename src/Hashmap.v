Require Import Word.
Require Import Prog.
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
