Require Import Word.
Require Import Prog.
Require Import EqdepFacts.
Require Import Arith.
Require Import AsyncDisk.
Require Import ListUtils.
Require Import List.

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

Theorem hash_safe_eq : forall hm h1 h2 sz (k1 k2 : word sz),
  hash_safe hm h1 k1 ->
  hash_safe (upd_hashmap' hm h1 k1) h2 k2 ->
  h1 = h2 ->
  k1 = k2.
Proof.
  unfold hash_safe, upd_hashmap'; intros. subst.
  destruct (weq h2 default_hash) eqn:Hdef.

  destruct hm;
    (unfold hashmap_get in *; rewrite Hdef in *;
    destruct H as [ H' | H' ]; inversion H';
    destruct H0 as [ H0' | H0' ]; inversion H0';
    rewrite H2 in H3; pose proof (eq_sigT_snd H3); autorewrite with core in *; auto).

  subst.
  rewrite upd_hashmap_eq in H0; auto.
  destruct H0 as [ H0' | H0' ]; inversion H0'.
  pose proof (eq_sigT_snd H1). autorewrite with core in *. auto.
Qed.

Lemma hashmap_subset_safe : forall hm2 l h k hm1,
  hashmap_subset l hm1 hm2 ->
  In (h, k) l ->
  hashmap_get hm2 h = Some k.
Proof.
  induction hm2; intros.
  inversion H. subst.
  inversion H0.

  inversion H; subst.
  inversion H0.

  destruct H0; subst.
  - inversion H0.
    destruct (weq h default_hash); subst.
    unfold hash_safe in *.
    intuition.
    contradict_hashmap_get_default H1 hm2.
    rewrite hashmap_get_default in *; auto.

    rewrite upd_hashmap_eq; auto.
  - eapply IHhm2 in H5; eauto.
    destruct (weq h default_hash); subst.
    rewrite hashmap_get_default in *; auto.
    unfold hashmap_get. destruct (weq h default_hash); intuition.
    destruct (weq w h); subst.
    unfold hash_safe in *. intuition;
    rewrite H1 in H5; inversion H5; auto.

    unfold hashmap_get in H5; auto.
Qed.


Theorem hashmap_subset_trans : forall hm3 l1 l2 hm1 hm2,
  hashmap_subset l1 hm1 hm2 ->
  hashmap_subset l2 hm2 hm3 ->
  hashmap_subset (l2 ++ l1) hm1 hm3.
Proof.
  induction hm3; intros;
  inversion H0; subst; auto.

  rewrite <- app_comm_cons.
  constructor; eauto.
Qed.

(** Chains together hashmap_subset patterns until it solves the goal.
  If the goal's larger hashmap isn't instantiated yet, try to match
  it to the largest possible hashmap. *)
Ltac solve_hashmap_subset_trans :=
  match goal with
  | [ H: hashmap_subset _ ?hm ?hm2, H2: hashmap_subset _ ?hm2 _ |- hashmap_subset _ ?hm _ ]
    => eapply hashmap_subset_trans;
        [ exact H | try solve_hashmap_subset_trans ]
  | [ |- hashmap_subset _ _ _ ]
    => eauto
  end.

Ltac solve_hashmap_subset :=
  match goal with
  | [ |- exists _, hashmap_subset _ _ _ ]
    => eexists; solve_hashmap_subset
  | [ |- hashmap_subset _ _ _ ]
    => subst; solve [ solve_hashmap_subset_trans | repeat (eauto; econstructor) ]
  end.

Ltac solve_hash_list_rep :=
  try match goal with
  | [ H: hash_list_rep _ ?h ?hm, Htrans: hashmap_subset _ ?hm _ |-
      hash_list_rep _ ?h _ ]
    => eapply hash_list_rep_subset; [ | exact H ];
        try solve_hashmap_subset
  | [ H: hash_list_rep ?l _ ?hm, Htrans: hashmap_subset _ ?hm _ |-
      hash_list_rep ?l _ _ ]
    => eapply hash_list_rep_subset; [ | exact H ];
        try solve_hashmap_subset
  end.
