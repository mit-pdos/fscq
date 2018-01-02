Require Import Mem List ListUtils Omega.
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

Fixpoint extract_blocks (bm: block_mem) hl :=
  match hl with
  | nil => nil
  | h::t => match bm h with
           | None => extract_blocks bm t
           | Some tb => tb::extract_blocks bm t
           end
  end.


Lemma extract_blocks_app:
  forall l1 l2 bm,
    extract_blocks bm (l1 ++ l2) = extract_blocks bm l1 ++ extract_blocks bm l2.
Proof.
  induction l1; intros; simpl; auto.
  destruct (bm a).
  rewrite IHl1, app_comm_cons; auto.
  auto.
Qed.

Lemma extract_blocks_length_le:
  forall bm l,
    length (extract_blocks bm l) <= length l.
Proof.
  induction l; simpl in *; intros; eauto.
  destruct (bm a); simpl; omega.
Qed.

Lemma extract_blocks_length_lt:
  forall l h bm,
    List.In h l ->
    bm h = None ->
    length (extract_blocks bm l) < length l.
Proof.
  induction l; simpl in *; intros; intuition.
  subst; rewrite H0.
  pose proof (extract_blocks_length_le bm l); omega.
  specialize (IHl _ _ H1 H0).
  destruct (bm a); simpl; omega.
Qed.

Lemma extract_blocks_rev_length_eq:
  forall bm l,
    length (extract_blocks bm l) =
    length (extract_blocks bm (rev l)).
Proof.
  induction l; simpl; intuition.
  rewrite extract_blocks_app; simpl.
  destruct (bm a); simpl;
  rewrite IHl, app_length; simpl; omega.
Qed.

Lemma extract_blocks_upd_not_in:
  forall l h tb bm,
    ~List.In h l ->
    extract_blocks (upd bm h tb) l = extract_blocks bm l.
Proof.
  induction l; simpl in *; intros; intuition.
  rewrite upd_ne; auto.
  rewrite IHl; eauto.
Qed.

Lemma extract_blocks_selN:
  forall bm l a def deftb,
    length l = length (extract_blocks bm l) ->
    a < length l ->
    bm (selN l a def) = Some (selN (extract_blocks bm l) a deftb).
Proof.
  induction l; simpl; intros; try omega.
  destruct a0;
  destruct (bm a); simpl; auto.
  pose proof (extract_blocks_length_le bm l); omega.
  simpl in *.
  apply IHl; omega.
  pose proof (extract_blocks_length_le bm l); omega.
Qed.


Lemma extract_blocks_subset:
  forall bm bm' hl,
    length (extract_blocks bm hl) = length hl ->
    bm c= bm' ->
    extract_blocks bm hl = extract_blocks bm' hl.
Proof.
  unfold block_mem_subset; induction hl; intros; simpl in *; auto.
  destruct (bm a) eqn:D;
  specialize (H0 a) as Hx; destruct Hx.
  erewrite H2; eauto.
  rewrite IHhl; eauto.
  pose proof (extract_blocks_length_le bm hl).
  omega.
Qed.

Lemma extract_blocks_selN_inside:
  forall bm l a def deftb,
    length l = length (extract_blocks bm l) ->
    a < length l ->
    selN (extract_blocks bm l) a deftb::nil = extract_blocks bm (selN l a def :: nil).
Proof.
  induction l; simpl; intros; try omega.
  destruct a0; destruct (bm a); simpl in *; auto.
  pose proof (extract_blocks_length_le bm l); omega.
  erewrite IHl; try omega; auto.
  pose proof (extract_blocks_length_le bm l); omega.
Qed.

Lemma extract_blocks_firstn_length:
  forall bm l n,
    length l = length (extract_blocks bm l) ->
    length (firstn n l) = length (extract_blocks bm (firstn n l)).
Proof.
  induction l; simpl; intros; try omega.
  rewrite firstn_nil; auto.
  destruct n; simpl; auto.
  destruct (bm a); simpl in *; auto.
  pose proof (extract_blocks_length_le bm l); omega.
Qed.