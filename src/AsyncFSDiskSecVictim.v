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
Import ListNotations.

Set Implicit Arguments.

Parameter can_access_dec: forall pr t, {can_access pr t}+{~can_access pr t}.


Definition equivalent_for tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 = tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).


Definition blockmem_equivalent_for tag (bm1 bm2: block_mem) :=
  forall a,
    (bm1 a = None /\ bm2 a = None) \/
    (exists v1 v2,
       bm1 a = Some v1 /\ bm2 a = Some v2 /\
       fst v1 = fst v2 /\
       (fst v1 = tag -> snd v1 = snd v2)).


Definition same_except tag (d1 d2: rawdisk) :=
  forall a,
    (d1 a = None /\ d2 a = None) \/
    (exists vs1 vs2,
       d1 a = Some vs1 /\ d2 a = Some vs2 /\
       Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) (vsmerge vs1) (vsmerge vs2) /\
       Forall2 (fun tb1 tb2 => fst tb1 <> tag -> snd tb1 = snd tb2) (vsmerge vs1) (vsmerge vs2)).

Definition blockmem_same_except tag (bm1 bm2: block_mem) :=
  forall a,
    (bm1 a = None /\ bm2 a = None) \/
    (exists v1 v2,
       bm1 a = Some v1 /\ bm2 a = Some v2 /\
       fst v1 = fst v2 /\
       (fst v1 <> tag -> snd v1 = snd v2)).

Lemma exec_blockmem_subset_upd:
        forall T (p: prog T) pr d bm hm h v d1 bm1 hm1 r1 tr,
          exec pr d (upd bm h v) hm p (Finished d1 bm1 hm1 r1) tr ->
          exists bm1', bm1 = upd bm1' h v /\ (bm h = None -> bm1' h = None). 
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [ eexists; intuition eauto ];
    try solve [ destruct (handle_eq_dec h r1); subst;
    [ rewrite upd_eq in *; eauto; congruence
    | rewrite upd_comm; eauto; eexists;
      intuition eauto; rewrite upd_ne; eauto] ].
    specialize IHp with (1:=H0); cleanup.
    specialize H with (1:=H1); cleanup.
    eexists; intuition eauto.
  Qed.

  Fixpoint only_public_operations tr :=
    match tr with
    | nil => True
    | op::tr' =>
      match op with
      | Uns t => t = Public
      | Sea t => t = Public
      end /\ only_public_operations tr'
    end.

  Lemma only_public_operations_app:
    forall tr1 tr2,
      only_public_operations (tr1++tr2) ->
      only_public_operations tr1 /\ only_public_operations tr2.
  Proof.
    induction tr1; simpl; intuition;
    specialize IHtr1 with (1:= H1); cleanup; auto.
  Qed.

  Lemma blockmem_same_except_upd_same:
    forall t bm bm' h b b0,
      blockmem_same_except t bm bm' ->
      blockmem_same_except t (upd bm h (t, b)) (upd bm' h (t, b0)).
  Proof.
    unfold blockmem_same_except; intros.
    destruct (handle_eq_dec h a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    simpl in *; intuition.
    repeat rewrite upd_ne in *; eauto.
  Qed.

  Lemma blockmem_same_except_upd_eq:
    forall t bm bm' h v,
      blockmem_same_except t bm bm' ->
      blockmem_same_except t (upd bm h v) (upd bm' h v).
  Proof.
    unfold blockmem_same_except; intros.
    destruct (handle_eq_dec h a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    repeat rewrite upd_ne in *; eauto.
  Qed.


  Lemma same_except_upd_same:
    forall t d d' n b b0 b1 b2 t2 l l0,
      same_except t d d' ->
      Forall2 (fun tb1 tb2 => fst tb1 <> t -> snd tb1 = snd tb2)
              (vsmerge (t2, b1, l)) (vsmerge (t2, b2, l0)) ->
      Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) l l0 ->
      same_except t (upd d n (t, b, vsmerge (t2, b1, l)))
                  (upd d' n (t, b0, vsmerge (t2, b2, l0))).
  Proof.
    unfold same_except; intros.
    destruct (addr_eq_dec n a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    unfold vsmerge in *; simpl in *; intuition.
    unfold vsmerge in *; simpl in *; intuition.
    repeat rewrite upd_ne in *; eauto. 
  Qed.


  Lemma same_except_upd_eq:
    forall t d d' n b b1 b2 t1 t2 l l0,
      same_except t d d' ->
      Forall2 (fun tb1 tb2 => fst tb1 <> t -> snd tb1 = snd tb2)
              (vsmerge (t2, b1, l)) (vsmerge (t2, b2, l0)) ->
      Forall2 (fun tb1 tb2 => fst tb1 = fst tb2) l l0 ->
      same_except t (upd d n (t1, b, vsmerge (t2, b1, l)))
                  (upd d' n (t1, b, vsmerge (t2, b2, l0))).
  Proof.
    unfold same_except; intros.
    destruct (addr_eq_dec n a); subst.
    repeat rewrite upd_eq; eauto.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    unfold vsmerge in *; simpl in *; intuition.
    unfold vsmerge in *; simpl in *; intuition.
    repeat rewrite upd_ne in *; eauto. 
  Qed.

  Lemma same_except_sync_mem:
    forall t d d',
      same_except t d d' ->
      same_except t (sync_mem d) (sync_mem d').
  Proof.
    unfold sync_mem, same_except; intros.
    specialize (H a); split_ors; cleanup; eauto.
    destruct x, x0; simpl in *.
    right.
    simpl in *; do 2 eexists; intuition eauto.
    unfold vsmerge in *; simpl in *; intuition.
    inversion H1; eauto.
    unfold vsmerge in *; simpl in *; intuition.
    inversion H2; eauto.
  Qed.
  
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
