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
    same_except t d d' hm ->
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    exists d2 bm2,
      exec pr d' bm' hm p (Finished d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1.
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [do 2 eexists; split; try econstructor; eauto].
    { (** Read **)
      specialize (H1 r1) as Hx; split_ors; cleanup; try congruence.
      specialize (H0 n) as Hx; split_ors; cleanup; try congruence.
      destruct x0.
      do 2 eexists; split; try econstructor; eauto.
      destruct x, t0; unfold vsmerge in *;  simpl in *.
      inversion H6; subst; simpl in *; clear H6; subst.
      inversion H7; subst; simpl in *; clear H7; subst.
      destruct t1; simpl in *.
      destruct (hm1 n0) eqn:D; eauto.      
      destruct (tag_dec t0 t); subst.
      apply blockmem_same_except_upd_same; auto.
      rewrite H9; eauto.
      apply blockmem_same_except_upd_eq; auto.
      congruence.
      rewrite H9; eauto.
      apply blockmem_same_except_upd_eq; auto.
      congruence.
    }
    { (** Write **)
      destruct bs; cleanup.
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      destruct x0; simpl in *; cleanup.
      specialize (H0 n) as Hx; split_ors; cleanup; try congruence.
      destruct x, x1, t0, t1; simpl in *.
      do 2 eexists; split; try econstructor; eauto.
      inversion H7; subst; simpl in *; clear H7; subst.
      destruct (hm1 n0) eqn:D; eauto.  
      destruct (tag_dec t0 t); subst.
      eapply same_except_upd_same; eauto.
      rewrite H6; eauto.
      eapply same_except_upd_eq; eauto.
      congruence.
      rewrite H6; eauto.
      eapply same_except_upd_eq; eauto.
      congruence.
    }
    { (** Seal **)
      specialize (H1 r1) as Hx; split_ors; cleanup; try congruence.
      do 2 eexists; split; try econstructor; eauto.
      apply blockmem_same_except_upd_eq; auto.
    }
    { (** Unseal **)
      destruct b; cleanup.
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      do 2 eexists; split; try econstructor; eauto.
      destruct x0; cleanup.
      simpl fst in *; subst.
      simpl in *; cleanup.
      rewrite H6; intuition.
      cleanup; congruence.
    }
    { (** Sync **)
      do 2 eexists; split; try econstructor; eauto.
      apply same_except_sync_mem; auto.
    }
    { (** ChDom **)
      do 2 eexists; split; try econstructor; eauto.
      {
        unfold same_except in *; intros; eauto.
        simpl in *; cleanup.
        specialize (H0 a); split_ors; cleanup; eauto.
        destruct x, x0; simpl in *.
        unfold vsmerge in *;  simpl in *.
        inversion H4; subst; simpl in *; clear H4; subst.
        inversion H5; subst; simpl in *; clear H5; subst.
        right; do 2 eexists; repeat (split; eauto).
        simpl; subst; constructor; eauto.
        - destruct (addr_eq_dec n (fst t1)); subst; eauto.
          + rewrite upd_eq; eauto.
            intros; cleanup; eauto.
            apply H8.
            intros Hn; cleanup; congruence.
          + rewrite upd_ne; eauto.
        - eapply forall_forall2.
          rewrite Forall_forall; intros.
          destruct (addr_eq_dec n (fst (fst x))); subst.
          + cleanup.
            rewrite upd_eq in H5; eauto.
            cleanup.
            eapply forall2_forall in H12; rewrite Forall_forall in H12; eauto.
            eapply H12; eauto.
            intros Hn; cleanup; eauto.
            setoid_rewrite H15 in Hn; cleanup; congruence.
        + rewrite Mem.upd_ne in H5; eauto.
          cleanup.
          eapply forall2_forall in H12; rewrite Forall_forall in H12; eauto.
        + eapply forall2_length; eauto.
      }
      {
        unfold blockmem_same_except in *; intros; eauto.
        simpl in *; cleanup.
        specialize (H1 a); split_ors; cleanup; eauto.
        destruct x, x0; simpl in *.
        right; do 2 eexists; repeat (split; eauto).
        simpl; destruct (addr_eq_dec n n0); subst.
        rewrite upd_eq; eauto.
        intros; cleanup; eauto.
        apply H5.
        intros Hn; cleanup; congruence.

        rewrite upd_ne; eauto.
      }
    }
    { (** Bind **)
      apply only_public_operations_app in H3; cleanup.
      specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H6)(5:=H4); cleanup.
      specialize H with (1:=H5)(2:=H8)(3:=H9)(4:=H3)(5:=H4); cleanup.
      do 2 eexists; split; try econstructor; eauto.
    }
  Qed.


  Lemma exec_same_except_crashed:
  forall T (p: prog T) pr d d' bm bm' hm t d1 bm1 hm1 tr,
    exec pr d bm hm p (Crashed d1 bm1 hm1) tr ->
    same_except t d d' hm ->
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    exists d2 bm2,
      exec pr d' bm' hm p (Crashed d2 bm2 hm1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1.
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
  forall T (p: prog T) pr d d' bm bm' hm t tr,
    exec pr d bm hm p Failed tr ->
    same_except t d d' hm ->
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    exec pr d' bm' hm p Failed tr.
  Proof.
    induction p; intros; inv_exec_perm;
    try solve [try econstructor; eauto].
    { (** Read **)
      specialize (H0 n) as Hx; split_ors; cleanup; try congruence.
      try econstructor; eauto.
    }
    { (** Write **)
      split_ors;
      [ specialize (H1 h) as Hx; split_ors; cleanup; try congruence
      | specialize (H0 n) as Hx; split_ors; cleanup; try congruence ];
      try econstructor; eauto.
    }
    { (** Unseal **)
      split_ors.
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      try econstructor; eauto.
      specialize (H1 h) as Hx; split_ors; cleanup; try congruence.
      try econstructor; eauto.
      right; eexists; split; eauto.
      rewrite <- H7; eauto.
    }
    { (** Bind **)
      split_ors; cleanup.
      {
        specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H3)(5:=H4); cleanup.
        try econstructor; eauto.
      }
      {
        apply only_public_operations_app in H3; cleanup.
        eapply exec_same_except_finished in H0; eauto; cleanup.
        specialize H with (1:=H5)(2:=H7)(3:=H8)(4:=H3)(5:=H4); cleanup.
        try econstructor; eauto.
      }
    }
  Qed.

  Lemma exec_same_except:
  forall T (p: prog T) pr d d' bm bm' hm t out tr,
    exec pr d bm hm p out tr ->
    same_except t d d' hm ->
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    
    (exists d1 bm1 hm1 r1 d2 bm2,
      out = Finished d1 bm1 hm1 r1 /\
      exec pr d' bm' hm p (Finished d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1) \/

    (exists d1 bm1 hm1 d2 bm2,
      out = Crashed d1 bm1 hm1 /\
      exec pr d' bm' hm p (Crashed d2 bm2 hm1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1) \/
    
    ( out = Failed /\
      exec pr d' bm' hm p Failed tr).
  Proof.
    intros; destruct out.
    - eapply exec_same_except_finished in H; eauto; cleanup.
      left; repeat eexists; eauto.
    - eapply exec_same_except_crashed in H; eauto; cleanup.
      right; left; repeat eexists; eauto.
    - eapply exec_same_except_failed in H; eauto; cleanup.
  Qed.

  

   Lemma exec_same_except_rfinished:
  forall T T' (p1: prog T) (p2: prog T') pr d d' bm bm' hm t d1 bm1 hm1 r1 tr,
    exec_recover pr d bm hm p1 p2 (RFinished T' d1 bm1 hm1 r1) tr ->
    same_except t d d' hm ->
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    exists d2 bm2,
      exec_recover pr d' bm' hm p1 p2 (RFinished T' d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1.
  Proof.
    intros.
    inversion H; subst.
    eapply exec_same_except_finished in H15; eauto; cleanup.
    do 2 eexists; intuition eauto.
    econstructor; eauto.
  Qed.

  Lemma exec_same_except_rfailed:
  forall T T' (p1: prog T) (p2: prog T') pr d d' bm bm' hm t tr,
    exec_recover pr d bm hm p1 p2 (RFailed T T') tr ->
    same_except t d d' hm ->
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    exec_recover pr d' bm' hm p1 p2 (RFailed T T') tr.
  Proof.
    intros.
    inversion H; subst.
    eapply exec_same_except_failed in H4; eauto; cleanup.
    econstructor; eauto.
  Qed.


    Lemma exec_same_except_recover:
  forall T T' (p1: prog T) (p2: prog T') pr d bm hm out tr,
    exec_recover pr d bm hm p1 p2 out tr ->
  forall t d',
    same_except t d d' hm ->
  forall bm',  
    blockmem_same_except t bm bm' hm ->
    only_public_operations tr ->
    t <> Public ->
    
    (exists d1 bm1 hm1 r1 d2 bm2,
      out = RFinished T' d1 bm1 hm1 r1 /\
      exec_recover pr d' bm' hm p1 p2 (RFinished T' d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1) \/
    
    ( out = RFailed T T' /\
      exec_recover pr d' bm' hm p1 p2 (RFailed T T') tr) \/
    
    (exists d1 bm1 hm1 r1 d2 bm2,
      out = RRecovered T d1 bm1 hm1 r1 /\
      exec_recover pr d' bm' hm p1 p2 (RRecovered T d2 bm2 hm1 r1) tr /\
      same_except t d1 d2 hm1 /\
      blockmem_same_except t bm1 bm2 hm1).
  Proof.
    induction 1; intros.
    { (** p1 finished **)
      left; eapply exec_same_except_finished in H; eauto; cleanup.
      do 6 eexists; intuition eauto.
      econstructor; eauto.
    }
    { (** p1 failed **)
      right; left; eapply exec_same_except_failed in H; eauto; cleanup.
      intuition eauto.
      econstructor; eauto.
    }
    { (** p1 crashed then p2 finished **)
      clear IHexec_recover.
      inversion H1; subst; clear H1.
      apply only_public_operations_app in H4; cleanup.
      eapply exec_same_except_crashed in H; eauto; cleanup.
      eapply possible_crash_same_except in H6 as Hx; eauto; cleanup.
      eapply exec_same_except_finished in H17 as Hp2; eauto; cleanup.
      right; right; do 6 eexists; repeat split; eauto.
      repeat (econstructor; eauto).
      unfold blockmem_same_except, empty_mem; simpl; eauto.
    }
    { (** p1 crashed then p2 crashed **)
      apply only_public_operations_app in H4; cleanup.
      eapply exec_same_except_crashed in H; eauto; cleanup.
      eapply possible_crash_same_except in H7 as Hx; eauto; cleanup.
      edestruct IHexec_recover; eauto.
      eassign (@empty_mem handle handle_eq_dec tagged_block).      
      unfold blockmem_same_except, empty_mem; simpl; eauto.
      repeat split_ors; cleanup; try congruence.
      repeat split_ors; cleanup; try congruence.
      inversion H11; subst; clear H11.
      right; right; do 6 eexists; repeat split; eauto.
      eapply XRCrashedRecovered; eauto.
    }
  Qed.