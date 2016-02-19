Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import List.
Require Import FunctionalExtensionality.
Require Import Morphisms.

Set Implicit Arguments.


Notation "a |=> v" := (a |-> ((v, nil) : valuset))%pred (at level 35) : pred_scope.
Notation "a |~> v" := (exists old, a |-> ((v, old) : valuset))%pred (at level 35) : pred_scope.

(* if [p] was true before a crash, then [crash_xform p] is true after a crash *)
Definition crash_xform {AT : Type} {AEQ : DecEq AT} (p : pred) : @pred AT AEQ (const valuset) :=
  fun m => exists m', p m' /\ possible_crash m' m.


(* Specialized relations for [@pred valuset], to deal with async IO *)

Theorem crash_xform_apply : forall AT AEQ (p : @pred AT AEQ (const valuset)) (m m' : @mem AT AEQ (fun _ => valuset)), possible_crash m m'
  -> p m
  -> crash_xform p m'.
Proof.
  unfold crash_xform; eauto.
Qed.

Theorem possible_crash_mem_union : forall AT AEQ (ma mb m' : @mem AT AEQ _), possible_crash (mem_union ma mb) m'
  -> mem_disjoint ma mb
  -> exists ma' mb', m' = mem_union ma' mb' /\ mem_disjoint ma' mb' /\
                     possible_crash ma ma' /\ possible_crash mb mb'.
Proof.
  intros.
  exists (fun a => match ma a with | None => None | Some v => m' a end).
  exists (fun a => match mb a with | None => None | Some v => m' a end).
  repeat split.

  - unfold mem_union; extensionality x.
    case_eq (ma x); case_eq (mb x); case_eq (m' x); auto.
    intros; unfold possible_crash in *.
    destruct (H x).
    destruct H4; congruence.
    repeat deex. unfold mem_union in H5.
    rewrite H2 in H5. rewrite H3 in H5. congruence.
  - unfold mem_disjoint; intro; repeat deex.
    case_eq (ma a); case_eq (mb a); intros.
    firstorder.
    rewrite H1 in H3; congruence.
    rewrite H4 in H2; congruence.
    rewrite H4 in H2; congruence.
  - unfold possible_crash in *; intro a.
    case_eq (ma a); intros; [right|left]; auto.
    pose proof (mem_union_addr a H0 H1).
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
  - unfold possible_crash in *; intro a.
    case_eq (mb a); intros; [right|left]; auto.
    rewrite mem_disjoint_comm in H0.
    pose proof (mem_union_addr a H0 H1); rewrite mem_union_comm in H2 by auto.
    destruct (H a); destruct H3; try congruence.
    repeat deex; repeat eexists; eauto.
    congruence.
Qed.

Theorem possible_crash_disjoint : forall AT AEQ (ma mb ma' mb' : @mem AT AEQ _), mem_disjoint ma' mb'
  -> possible_crash ma ma'
  -> possible_crash mb mb'
  -> mem_disjoint ma mb.
Proof.
  unfold mem_disjoint, possible_crash; intros.
  intro Hnot.
  repeat deex.
  destruct (H0 a); destruct (H1 a); try intuition congruence.
  repeat deex.
  apply H.
  do 3 eexists; eauto.
Qed.

Theorem possible_crash_union : forall AT AEQ (ma mb ma' mb' : @mem AT AEQ _), possible_crash ma ma'
  -> possible_crash mb mb'
  -> possible_crash (mem_union ma mb) (mem_union ma' mb').
Proof.
  unfold possible_crash, mem_union; intros.
  destruct (H a); destruct (H0 a).
  - destruct H1. destruct H2.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    intuition.
  - destruct H1. repeat deex.
    rewrite H1 in *; rewrite H2 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H2 in *.
    right. do 2 eexists. intuition.
  - repeat deex.
    rewrite H1 in *; rewrite H3 in *; rewrite H4 in *.
    right. do 2 eexists. intuition.
Qed.

Theorem possible_crash_trans : forall AT AEQ (ma mb mc : @mem AT AEQ _),
  possible_crash ma mb ->
  possible_crash mb mc ->
  possible_crash ma mc.
Proof.
  unfold possible_crash; intros.
  specialize (H a).
  specialize (H0 a).
  intuition; repeat deex; try congruence.
  right; repeat eexists; intuition eauto.
  rewrite H0 in H1.
  inversion H1; subst; clear H1.
  inversion H3.
  simpl in H1; subst; auto.
  inversion H1.
Qed.

Theorem crash_xform_idem : forall AT AEQ (p : @pred AT AEQ _), crash_xform (crash_xform p) =p=> crash_xform p.
Proof.
  unfold crash_xform, pimpl; intros.
  repeat deex; eexists; intuition eauto.
  eapply possible_crash_trans; eauto.
Qed.

Theorem crash_xform_sep_star_dist : forall AT AEQ (p q : @pred AT AEQ _),
  crash_xform (p * q) <=p=> crash_xform p * crash_xform q.
Proof.
  unfold_sep_star; unfold crash_xform, piff, pimpl; split; intros; repeat deex.
  - edestruct possible_crash_mem_union; try eassumption; repeat deex.
    do 2 eexists; intuition; eexists; eauto.
  - eexists; split.
    do 2 eexists; intuition; [| eassumption | eassumption].
    eapply possible_crash_disjoint; eauto.
    apply possible_crash_union; eauto.
Qed.

Theorem crash_xform_or_dist : forall AT AEQ (p q : @pred AT AEQ _),
  crash_xform (p \/ q) <=p=> crash_xform p \/ crash_xform q.
Proof.
  firstorder.
Qed.

Theorem crash_xform_lift_empty : forall AT AEQ (P : Prop),
  @crash_xform AT AEQ [[ P ]] <=p=> [[ P ]].
Proof.
  unfold crash_xform, lift_empty, possible_crash; intros; split;
    intros m H; repeat deex.
  specialize (H1 a); destruct H1; intuition.
  repeat deex; congruence.
  eexists; intuition.
Qed.

Theorem crash_xform_sep_star_apply : forall AT AEQ (p q : @pred AT AEQ _) (m m' : mem), possible_crash m m'
  -> (p * q)%pred m
  -> (crash_xform p * crash_xform q)%pred m'.
Proof.
  unfold_sep_star; intros; repeat deex.
  edestruct possible_crash_mem_union; try eassumption; repeat deex.
  do 2 eexists; repeat split; auto; unfold crash_xform; eexists; split; eauto.
Qed.

Theorem crash_xform_exists_comm : forall AT AEQ T (p : T -> @pred AT AEQ _),
  crash_xform (exists x, p x) =p=> exists x, crash_xform (p x).
Proof.
  unfold crash_xform, exis, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem crash_xform_forall_comm : forall AT AEQ T (p : T -> @pred AT AEQ _),
  crash_xform (foral x, p x) =p=> foral x, crash_xform (p x).
Proof.
  unfold crash_xform, foral_, pimpl; intros.
  repeat deex; repeat eexists; intuition eauto.
Qed.

Theorem crash_xform_ptsto: forall AT AEQ a v,
  (@crash_xform AT AEQ) (a |-> v) =p=> exists v', [[ In v' (valuset_list v) ]] * a |=> v'.
Proof.
  unfold crash_xform, possible_crash, ptsto, pimpl; intros.
  repeat deex; destruct (H1 a).
  intuition; congruence.
  repeat deex; rewrite H in H3; inversion H3; subst.
  repeat eexists.
  apply lift_impl.
  intros; eauto.
  split; auto.
  intros.
  destruct (H1 a').
  intuition.
  repeat deex.
  specialize (H2 a' H4).
  congruence.
Qed.

Theorem crash_xform_pimpl : forall AT AEQ (p q : @pred AT AEQ _), p =p=>q
  -> crash_xform p =p=> crash_xform q.
Proof.
  firstorder.
Qed.

Instance crash_xform_pimpl_proper {AT AEQ} :
  Proper (pimpl ==> pimpl) (@crash_xform AT AEQ).
Proof.
  firstorder.
Qed.

Instance crash_xform_flip_pimpl_proper {AT AEQ} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl) (@crash_xform AT AEQ).
Proof.
  firstorder.
Qed.

Instance crash_xform_piff_proper {AT AEQ} :
  Proper (piff ==> piff) (@crash_xform AT AEQ).
Proof.
  firstorder.
Qed.

Theorem crash_invariant_emp: forall AT AEQ,
  (@crash_xform AT AEQ) emp =p=> emp.
Proof.
  unfold crash_xform, possible_crash, emp, pimpl; repeat deex; intuition; repeat deex.
  destruct (H1 a); [ intuition | repeat deex; congruence ].
Qed.

Theorem crash_invariant_ptsto: forall AT AEQ a v,
  (@crash_xform AT AEQ) (a |=> v) =p=> a |=> v.
Proof.
  unfold crash_xform, pimpl, possible_crash, ptsto; intros.
  deex; intuition eauto.
  { destruct (H1 a).
    + intuition; congruence.
    + repeat deex.
      inversion H5; subst; rewrite H in H3; inversion H3; subst; [ auto | inversion H4 ]. }
  { destruct (H1 a').
    + intuition.
    + repeat deex.
      assert (m' a' = None) by eauto; congruence.
  }
Qed.

Lemma ptsto_synced_valid:
  forall AT AEQ a v F (m : @mem AT AEQ _),
  (a |=> v * F)%pred m
  -> m a = Some (v, nil).
Proof.
  intros.
  eapply ptsto_valid with (V := const valuset); eauto.
Qed.

Lemma ptsto_cur_valid:
  forall AT AEQ a v F (m : @mem AT AEQ _),
  (a |~> v * F)%pred m
  -> exists l, m a = Some (v, l).
Proof.
  unfold ptsto; unfold_sep_star; intros.
  repeat deex.
  eexists.
  apply mem_union_addr with (V := const valuset); eauto.
Qed.

Lemma crash_xform_diskIs: forall A AEQ (m: @mem A AEQ (const valuset)),
  crash_xform (diskIs m) =p=> exists m', [[ possible_crash m m' ]] * diskIs m'.
Proof.
  unfold crash_xform, pimpl, diskIs.
  intros.
  destruct H; intuition; subst.
  exists m0.
  unfold_sep_star.
  exists (fun a => None).
  exists m0.
  intuition.
  unfold mem_disjoint; intuition.
  repeat deex; discriminate.
  unfold lift_empty; intuition.
Qed.

Hint Rewrite crash_xform_sep_star_dist : crash_xform.
Hint Rewrite crash_xform_or_dist : crash_xform.
Hint Rewrite crash_xform_exists_comm : crash_xform.
Hint Rewrite crash_xform_forall_comm : crash_xform.
Hint Rewrite crash_xform_lift_empty : crash_xform.
Hint Rewrite crash_xform_ptsto : crash_xform.
Hint Rewrite crash_xform_diskIs : crash_xform.
Hint Rewrite crash_invariant_ptsto : crash_xform.

Hint Resolve crash_invariant_emp.

Lemma pred_apply_crash_xform : forall AT AEQ (p : @pred AT AEQ (const valuset)) m m',
  possible_crash m m' -> p m -> (crash_xform p) m'.
Proof.
  unfold pimpl, crash_xform; eauto.
Qed.

Lemma pred_apply_crash_xform_pimpl : forall AT AEQ (p q : @pred AT AEQ (const valuset)) m m',
  possible_crash m m' -> p m -> crash_xform p =p=> q -> q m'.
Proof.
  intros.
  apply H1.
  eapply pred_apply_crash_xform; eauto.
Qed.
