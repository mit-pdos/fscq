Require Import Word.
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
Require Import DiskSecDef DiskSecAttacker DiskSecVictim.
(* Require Import CopyFile. *)

Set Implicit Arguments.

Import ListNotations.

Definition equivalent_for_principal u d0 bm0 d1 bm1 hm:=
  (forall tag, can_access u tag ->
  equivalent_for tag d0 d1 hm /\
  blockmem_equivalent_for tag bm0 bm1 hm).

Definition ret_noninterference {T} (p: prog T):=
  forall u d0 bm0 hm0 d0' bm0' hm0' ret tr0 d1 bm1,
    exec u d0 bm0 hm0 p (Finished d0' bm0' hm0' ret) tr0 ->
    equivalent_for_principal u d0 bm0 d1 bm1 hm0 ->
    exists d1' bm1' tr1,
      exec u d1 bm1 hm0 p (Finished d1' bm1' hm0' ret) tr1.

Definition equivalent_state_for_principal {T} u (res0 res1: @result T) :=
  exists d0 bm0 hm d1 bm1,
    equivalent_for_principal u d0 bm0 d1 bm1 hm /\
    ((res0 = Crashed d0 bm0 hm /\ res1 = Crashed d1 bm1 hm) \/
     (res0 = Failed /\ res1 = Failed) \/
     (exists v0 v1, res0= Finished d0 bm0 hm v0 /\ res1 = Finished d1 bm1 hm v1)).

Definition state_noninterference {T} (p: prog T):=
  forall viewer caller d0 bm0 hm0 res0 tr0 d1 bm1,
    exec caller d0 bm0 hm0 p res0 tr0 ->
    equivalent_for_principal viewer d0 bm0 d1 bm1 hm0 ->
    exists res1 tr1,
      exec caller d1 bm1 hm0 p res1 tr1 /\
      equivalent_state_for_principal viewer res0 res1.

Definition unseal_safe {T} (p:prog T) :=
  forall u d bm hm res tr,
    exec u d bm hm p res tr ->
    forall perm,
      In perm tr -> op_secure u perm.

Definition op_public op:=
  match op with
  | Uns t => t = Public
  | Chd t _ => t = Public
  end.

Definition unseal_public {T} (p:prog T) :=
  forall u d bm hm res tr,
    exec u d bm hm p res tr ->
    forall perm,
      In perm tr -> op_public perm.

Lemma unseal_safe_to_trace_secure:
  forall T (p: prog T),
    unseal_safe p ->
    (forall u d bm hm res tr,
        exec u d bm hm p res tr ->
        trace_secure u tr).
Proof.
  unfold unseal_safe; intros.
  specialize H with (1:= H0).
  clear H0.
  generalize dependent tr.
  induction tr; intros; simpl; auto.
  specialize (H a (in_cons_head tr a)) as Hx.
  unfold op_secure in Hx.
  split.
  destruct a; auto.
  eapply IHtr; intros.
  eapply H; apply in_cons; auto.
Qed.

Lemma unseal_public_to_only_public_operations:
  forall T (p: prog T),
    unseal_public p ->
    (forall u d bm hm res tr,
        exec u d bm hm p res tr ->
        only_public_operations tr).
Proof.
  unfold unseal_public; intros.
  specialize H with (1:= H0).
  clear H0.
  generalize dependent tr.
  induction tr; intros; simpl; auto.
  specialize (H a (in_cons_head tr a)) as Hx.
  unfold op_public in Hx.
  split.
  destruct a; auto.
  eapply IHtr; intros.
  eapply H; apply in_cons; auto.
Qed.

Theorem unseal_safe_to_ret_noninterference:
  forall T (p: prog T),
    unseal_safe p -> ret_noninterference p.
Proof.
  unfold ret_noninterference, equivalent_for_principal; intros.
  cleanup.
  eapply unseal_safe_to_trace_secure in H; eauto.
  eapply exec_equivalent_finished in H0; eauto.
  cleanup; repeat eexists; apply H0.
  intros t Ht; specialize (H1 t Ht); intuition.
  intros t Ht; specialize (H1 t Ht); intuition.
Qed.

Theorem unseal_public_to_state_noninterference:
  forall T (p: prog T),
    unseal_public p -> state_noninterference p.
Proof.
  unfold state_noninterference, equivalent_state_for_principal, equivalent_for_principal; intros.
  cleanup.
  eapply unseal_public_to_only_public_operations in H; eauto.
  eapply exec_equivalent_for_viewer in H0 as Hx; eauto.
  repeat split_ors; cleanup.
  do 2 eexists; repeat split; eauto.
  do 5 eexists; split.
  2: { right; right; repeat eexists; eauto. }
  split; eauto.
  
  do 2 eexists; repeat split; eauto.
  do 5 eexists; split.
  2: { left; repeat eexists; eauto. }
  split; eauto.

  do 2 eexists; repeat split; eauto.
  do 5 eexists; split.
  2: { right; left; repeat eexists; eauto. }
  split; eauto.

  edestruct H1; eauto.
  edestruct H1; eauto.
  intros t Ht; specialize (H1 t Ht); intuition.
  intros t Ht; specialize (H1 t Ht); intuition.
Qed.

Theorem chdom_equivalent_for_viewer :
  forall viewer caller d bm hm d' bm' d1 bm1 hm1 r1 tr1 domid new_tag,
  exec caller d bm hm (ChDom domid new_tag) (Finished d1 bm1 hm1 r1) tr1 ->
  equivalent_for_principal viewer d bm d' bm' hm ->
  (same_for_domainid domid d bm d' bm' \/ ~can_access viewer new_tag) ->
  
   exists d2 bm2 tr2,
     exec caller d' bm' hm (ChDom domid new_tag) (Finished d2 bm2 hm1 r1) tr2 /\
     equivalent_for_principal viewer d1 bm1 d2 bm2 hm1 /\
     (same_for_domainid domid d bm d' bm' -> same_for_domainid domid d1 bm1 d2 bm2) /\
     (~can_access viewer new_tag -> equivalent_for_principal viewer d1 bm1 d2 bm2 hm).
Proof.
  intros.
  inv_exec_perm.
  do 3 eexists; split; eauto.
  econstructor; eauto.
  split; eauto.
  unfold equivalent_for_principal in *; eauto.
  intros; eauto.
  specialize (H0 _ H).
  split_ors.
  {
    split.
    {
      unfold equivalent_for, same_for_domainid, same_for_domainid_disk in *; intros.
      specialize (H0 a); split_ors; cleanup; eauto.
      specialize (H1 a _ _ H0 H4).
      right; do 2 eexists; repeat split; eauto.
      eapply forall_forall2.      
      apply forall2_forall in H5.
      apply forall2_forall in H6.
      apply forall2_forall in H1.
      rewrite Forall_forall in *; intros.
      destruct (addr_eq_dec domid (fst (fst x1))).
      eapply H1; eauto.
      erewrite <- H5; eauto.
      rewrite Mem.upd_ne in H8; eauto.
      eapply forall2_length; eauto.
    }
    {
      unfold blockmem_equivalent_for, same_for_domainid, same_for_domainid_mem in *; intros.
      specialize (H2 a); split_ors; cleanup; eauto.
      specialize (H3 a _ _ H2 H4).
      right; do 2 eexists; repeat split; eauto.
      intros; destruct (addr_eq_dec domid (fst x)).
      eapply H3; eauto.
      erewrite <- H5; eauto.
      rewrite Mem.upd_ne in H7; eauto.
    }
  }
  {
    destruct (tag_dec tag new_tag); subst; intuition.
    {
      unfold equivalent_for in *; intros.
      specialize (H0 a); split_ors; cleanup; eauto.
      right; do 2 eexists; repeat split; eauto.
      eapply forall_forall2.      
      apply forall2_forall in H4.
      apply forall2_forall in H5.
      rewrite Forall_forall in *; intros.
      destruct (addr_eq_dec domid (fst (fst x1))); subst.
      rewrite Mem.upd_eq in H7; eauto.
      cleanup; congruence.
      rewrite Mem.upd_ne in H7; eauto.
      eapply forall2_length; eauto.
    }
    {
      unfold blockmem_equivalent_for in *; intros.
      specialize (H2 a); split_ors; cleanup; eauto.
      right; do 2 eexists; repeat split; eauto.
      intros; destruct (addr_eq_dec domid (fst x)); subst.
      rewrite Mem.upd_eq in H6; eauto.
      cleanup; congruence.
      rewrite Mem.upd_ne in H6; eauto.
    }
  }
Qed.
