Require Import Mem Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import GenSepN.
Require Import ListPred.
Require Import List ListUtils.
Require Import Bytes.
Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Prog ProgLoop ProgList.
Require Import ProgAuto.
Require Import DestructPair.
Require Import DiskSecDef.
Import ListNotations.

Set Implicit Arguments.

  Lemma exec_same_except_finished:
  forall T (p: prog T) pr d d' bm bm' hm t d1 bm1 hm1 r1 tr,
    exec pr d bm hm p (Finished d1 bm1 hm1 r1) tr ->
    same_except t d d' ->
    blockmem_same_except t bm bm' ->
    only_public_operations tr ->
    t <> Public ->
    exists d2 bm2,
      exec pr d' bm' hm p (Finished d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 /\
      blockmem_same_except t bm1 bm2.
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [do 2 eexists; split; try econstructor; eauto].
    {
      specialize (H1 r1) as Hx; split_ors; cleanup; try congruence.
      specialize (H0 n) as Hx; split_ors; cleanup; try congruence.
      destruct x0.
      do 2 eexists; split; try econstructor; eauto.
      destruct tb, t0; unfold vsmerge in *;  simpl in *.
      inversion H7; subst; simpl in *; clear H7; subst.
      inversion H8; subst; simpl in *; clear H8; subst.
      destruct (tag_dec t0 t); subst.
      apply blockmem_same_except_upd_same; auto.
      rewrite H10; eauto.
      apply blockmem_same_except_upd_eq; auto.
    }
    {
      destruct tb; cleanup.
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      destruct x0; simpl in *; cleanup.
      specialize (H0 n) as Hx; split_ors; cleanup; try congruence.
      destruct x, x0, t0, t2; simpl in *.
      do 2 eexists; split; try econstructor; eauto.
      inversion H7; subst; simpl in *; clear H7; subst.
      destruct (tag_dec t1 t); subst.
      eapply same_except_upd_same; eauto.
      rewrite H6; eauto.
      eapply same_except_upd_eq; eauto.
    }
    {
      specialize (H1 r1) as Hx; split_ors; cleanup; try congruence.
      do 2 eexists; split; try econstructor; eauto.
      apply blockmem_same_except_upd_eq; auto.
    }
    {
      destruct tb; cleanup.
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      do 2 eexists; split; try econstructor; eauto.
      destruct x0; cleanup.
      simpl fst in *; subst.
      eapply ExecUnseal.
      simpl in *; cleanup.
      rewrite H6; intuition.
    }
    {
      do 2 eexists; split; try econstructor; eauto.
      apply same_except_sync_mem; auto.
    }
    {
      apply only_public_operations_app in H3; cleanup.
      specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H6)(5:=H4); cleanup.
      specialize H with (1:=H5)(2:=H8)(3:=H9)(4:=H3)(5:=H4); cleanup.
      do 2 eexists; split; try econstructor; eauto.
    }
  Qed.


  Lemma exec_same_except_crashed:
  forall T (p: prog T) pr d d' bm bm' hm t d1 bm1 hm1 tr,
    exec pr d bm hm p (Crashed d1 bm1 hm1) tr ->
    same_except t d d' ->
    blockmem_same_except t bm bm' ->
    only_public_operations tr ->
    t <> Public ->
    exists d2 bm2,
      exec pr d' bm' hm p (Crashed d2 bm2 hm1) tr /\
      same_except t d1 d2 /\
      blockmem_same_except t bm1 bm2.
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [do 2 eexists; split; try econstructor; eauto].
    split_ors; cleanup.
    {
      specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H3)(5:=H4); cleanup.
      do 2 eexists; split; try econstructor; eauto.
    }
    {
      apply only_public_operations_app in H3; cleanup.
      eapply exec_same_except_finished in H0; eauto; cleanup.
      specialize H with (1:=H5)(2:=H7)(3:=H8)(4:=H3)(5:=H4); cleanup.
      do 2 eexists; split; try econstructor; eauto.
    }
  Qed.

  Lemma exec_same_except_failed:
  forall T (p: prog T) pr d d' bm bm' hm t d1 bm1 hm1 tr,
    exec pr d bm hm p (Failed d1 bm1 hm1) tr ->
    same_except t d d' ->
    blockmem_same_except t bm bm' ->
    only_public_operations tr ->
    t <> Public ->
    exists d2 bm2,
      exec pr d' bm' hm p (Failed d2 bm2 hm1) tr /\
      same_except t d1 d2 /\
      blockmem_same_except t bm1 bm2.
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [do 2 eexists; split; try econstructor; eauto].
    {
      specialize (H0 n) as Hx; split_ors; cleanup; try congruence.
      do 2 eexists; split; try econstructor; eauto.
    }
    {
      split_ors;
      [ specialize (H1 h) as Hx; split_ors; cleanup; try congruence
      | specialize (H0 n) as Hx; split_ors; cleanup; try congruence ];
      do 2 eexists; split; try econstructor; eauto.
    }
    {
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      do 2 eexists; split; try econstructor; eauto.
    }    
    split_ors; cleanup.
    {
      specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H3)(5:=H4); cleanup.
      do 2 eexists; split; try econstructor; eauto.
    }
    {
      apply only_public_operations_app in H3; cleanup.
      eapply exec_same_except_finished in H0; eauto; cleanup.
      specialize H with (1:=H5)(2:=H7)(3:=H8)(4:=H3)(5:=H4); cleanup.
      do 2 eexists; split; try econstructor; eauto.
    }
  Qed.

  Lemma exec_same_except:
  forall T (p: prog T) pr d d' bm bm' hm t out tr,
    exec pr d bm hm p out tr ->
    same_except t d d' ->
    blockmem_same_except t bm bm' ->
    only_public_operations tr ->
    t <> Public ->
    
    (exists d1 bm1 hm1 r1 d2 bm2,
      out = Finished d1 bm1 hm1 r1 /\
      exec pr d' bm' hm p (Finished d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 /\
      blockmem_same_except t bm1 bm2) \/

    (exists d1 bm1 hm1 d2 bm2,
      out = Crashed d1 bm1 hm1 /\
      exec pr d' bm' hm p (Crashed d2 bm2 hm1) tr /\
      same_except t d1 d2 /\
      blockmem_same_except t bm1 bm2) \/
    
    (exists d1 bm1 hm1 d2 bm2,
      out = Failed d1 bm1 hm1 /\
      exec pr d' bm' hm p (Failed d2 bm2 hm1) tr /\
      same_except t d1 d2 /\
      blockmem_same_except t bm1 bm2).
  Proof.
    intros; destruct out.
    - eapply exec_same_except_finished in H; eauto; cleanup.
      left; repeat eexists; eauto.
    - eapply exec_same_except_crashed in H; eauto; cleanup.
      right; left; repeat eexists; eauto.
    - eapply exec_same_except_failed in H; eauto; cleanup.
      right; right; repeat eexists; eauto.
  Qed.