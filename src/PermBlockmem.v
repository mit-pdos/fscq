Require Import Mem.
Require Export PermProg.

Definition block_mem_subset (bm' bm: block_mem) :=
  forall h, (bm h = None -> bm' h = None) /\ (forall b, bm' h = Some b -> bm h = Some b).

Infix "c=" := block_mem_subset (at level 1, left associativity).

Lemma block_mem_subset_refl:
  forall bm, bm c= bm.
Proof.
  unfold block_mem_subset; intuition eauto.
Qed.

Lemma block_mem_subset_trans:
  forall bm bm' bm'',
    bm c= bm' ->
    bm' c= bm'' ->
    bm c= bm''.
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h); destruct H0;
  specialize (H h); destruct H; eauto.
Qed.

Lemma block_mem_subset_upd_none:
  forall bm bm' h v,
    bm h = None ->
    bm' c= bm ->
    bm' c= (upd bm h v).
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h0); destruct H0.
  destruct (handle_eq_dec h h0); subst; auto.
  rewrite upd_ne in H1; eauto.
  destruct (handle_eq_dec h h0); subst; auto.
  specialize (H0 H); congruence.
  rewrite upd_ne; eauto.
Qed.

Lemma block_mem_subset_upd_nop:
  forall bm bm' h v,
    bm h = Some v ->
    bm' c= bm ->
    bm' c= (upd bm h v).
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h0); destruct H0.
  destruct (handle_eq_dec h h0); subst; auto.
  rewrite upd_eq in H1; congruence.
  rewrite upd_ne in H1; eauto.
  destruct (handle_eq_dec h h0); subst; auto.
  specialize (H2 _ H1).
  rewrite H2 in H; inversion H; rewrite upd_eq; eauto.
  specialize (H2 _ H1).
  rewrite upd_ne; eauto.
Qed.

Lemma block_mem_subset_upd_irrel:
  forall bm bm' h v,
    bm' h = None ->
    bm' c= bm ->
    bm' c= (upd bm h v).
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h0); destruct H0.
  destruct (handle_eq_dec h h0); subst; auto.
  rewrite upd_ne in H1; eauto.
  destruct (handle_eq_dec h h0); subst; auto.
  congruence.
  rewrite upd_ne; eauto.
Qed.

Lemma block_mem_subset_extract_none:
  forall bm bm' h,
    bm h = None ->
    bm' c= bm ->
    bm' h = None.
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h); destruct H0; auto.
Qed.

Lemma block_mem_subset_extract_some:
  forall bm bm' h v,
    bm' h = Some v ->
    bm' c= bm ->
    bm h = Some v.
Proof.
  unfold block_mem_subset; intuition eauto;
  specialize (H0 h); destruct H0; auto.
Qed.

Hint Resolve block_mem_subset_refl block_mem_subset_upd_none
     block_mem_subset_upd_nop block_mem_subset_upd_irrel
     block_mem_subset_extract_none block_mem_subset_extract_some
     block_mem_subset_trans.