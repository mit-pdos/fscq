Require Import EventCSL.
Require Import Locking.
Require Import ForwardChaining.
Require Import FunctionalExtensionality.
Import List.
Import List.ListNotations.

Set Implicit Arguments.

(* TODO: this file is organized terribly, combining the very general pred_domain
with the state/locking-specific preservation concept *)
Section Preservation.

Variable AT:Type.
Variable AEQ:DecEq AT.
Variable V:AT -> Type.

Implicit Type m:@mem AT AEQ V.
Implicit Type F:@pred AT AEQ V.

Definition preserves_frames R F F' :=
  forall P m m',
    (F * P)%pred m ->
    R m m' ->
    (F' * P)%pred m'.

Section State.

Variable S:Type.
Variable proj: S -> @mem AT AEQ V.
Variable lock: S -> AT -> BusyFlagOwner.

Definition preserves (R : S -> S -> Prop) F F' :=
  forall P s s',
    (F * P)%pred (proj s) ->
    R s s' ->
    (F * P)%pred (proj s').

Definition pred_domain F (dom: list AT) :=
  (forall m, F m -> forall a v, m a = Some v -> In a dom) /\
  (forall m, F m -> forall a, In a dom -> m a <> None).

Lemma pred_domain_exists : forall F dom,
  pred_domain F dom <->
  forall m, F m ->
  (forall a, (exists v, m a = Some v) <-> In a dom).
Proof.
  unfold pred_domain.
  split.
  - split; intros; repeat deex; eauto.
    case_eq (m a); intros; eauto; firstorder.
  - split; intros.
    firstorder.
    intro.
    pose proof (H _ H0 a); firstorder.
    congruence.
Qed.

Hint Unfold pred_domain : pred.

Ltac start := repeat autounfold with pred; intros; repeat deex; intuition;
  repeat match goal with
  | [ H: forall (_:mem), ?F _ -> _, H': ?F _ |- _ ] =>
    learn that (H _ H')
  end.

Ltac dispatch := repeat split; intros;
  repeat deex;
  intuition eauto;
  try congruence.

Lemma exact_domain_oneside : forall F,
  (forall m1 m2, F m1 -> F m2 ->
    forall a, m1 a = None -> m2 a = None) ->
  exact_domain F.
Proof.
  start; dispatch.
Qed.

Remark pred_domain_exact_domain : forall F dom,
  pred_domain F dom -> exact_domain F.
Proof.
  start.
  apply exact_domain_oneside; dispatch.
  destruct (in_dec AEQ a dom).
  firstorder.
  case_eq (m2 a); intros;
    try match goal with
    | [ |- Some _ = None ] => exfalso
    end; eauto.
Qed.

Lemma mem_union_some : forall m1 m2 a v,
  mem_union m1 m2 a = Some v ->
  m1 a = Some v \/ m2 a = Some v.
Proof.
  unfold mem_union; start.
  destruct (m1 a); dispatch.
Qed.

Lemma mem_union_none : forall m1 m2 a,
  mem_union m1 m2 a = None ->
  m1 a = None /\ m2 a = None.
Proof.
  unfold mem_union; intros.
  destruct (m1 a); dispatch.
Qed.

Theorem pred_domain_combine : forall F F' dom dom',
  pred_domain F dom ->
  pred_domain F' dom' ->
  pred_domain (F * F') (dom ++ dom').
Proof.
  unfold_sep_star; start; dispatch.
  eapply in_or_app.
  destruct (mem_union_some _ _ H4); dispatch.
  eapply mem_union_none in H5; intuition.
  destruct (in_app_or _ _ _ H4); dispatch.
Qed.

Theorem pred_domain_ptsto : forall a v,
  pred_domain (a |-> v) [a].
Proof.
  unfold ptsto; start.
  destruct (AEQ a a0); subst.
  constructor; auto.
  specialize (H1 a0); intuition; congruence.

  inversion H; subst; eauto.
  specialize (H1 a0); dispatch.
Qed.

(* to learn something from pred_domain, need a memory to have
F true, but F might be false in every memory *)
Definition realizable F :=
  exists m, F m.

Lemma ptsto_single_mem : forall a v,
  (a |-> v)%pred (@upd AT AEQ V empty_mem a v).
Proof.
  unfold ptsto, upd, empty_mem; start.
  destruct (AEQ a a); dispatch.
  unfold eq_rect_r.
  rewrite <- Eqdep_dec.eq_rect_eq_dec; dispatch.

  destruct (AEQ a' a); dispatch.
Qed.

Hint Unfold realizable : pred.

Corollary realizable_ptsto : forall a v,
  realizable (a |-> v).
Proof.
  unfold realizable; intros.
  eauto using ptsto_single_mem.
Qed.

Theorem realizable_star_witness : forall F F' m,
  (F * F')%pred m ->
  realizable F.
Proof.
  unfold_sep_star; start; dispatch.
Qed.

Corollary realizable_star_witness' : forall F F' m,
  (F * F')%pred m ->
  realizable F'.
Proof.
  intros.
  apply sep_star_comm in H.
  eauto using realizable_star_witness.
Qed.

Theorem pred_domain_unique : forall F ls ls',
  pred_domain F ls ->
  pred_domain F ls' ->
  (* must actually exist a mem in which F is true *)
  realizable F ->
  (forall a, In a ls -> In a ls').
Proof.
  start.

  case_eq (m a); intros; dispatch.
  firstorder.
Qed.

Theorem pred_domain_ptsto_in : forall F a v ls,
  pred_domain (F * a |-> v) ls ->
  realizable (F * a |-> v) ->
  In a ls.
Proof.
  start; dispatch.
  eauto using ptsto_valid'.
Qed.

Definition precise_domain F :=
  forall m1 m1' m2 m2',
  mem_union m1 m1' = mem_union m2 m2' ->
  mem_disjoint m1 m1' ->
  mem_disjoint m2 m2' ->
  F m1 ->
  F m2 ->
  (forall a, m1 a = None -> m2 a = None).

Hint Unfold precise precise_domain : pred.

Theorem precise_to_precise_domain : forall F,
  precise F <->
  precise_domain F.
Proof.
  start; dispatch.
  - assert (m1 = m2) by eauto; subst; eauto.
  - assert (forall a, m1 a = None -> m2 a = None) by eauto.
    assert (forall a, m2 a = None -> m1 a = None) by eauto.
    extensionality a.
    assert (mem_union m1 m1' a = mem_union m2 m2' a) by congruence.
    unfold mem_union in *.
    case_eq (m1 a); case_eq (m2 a); intros;
      replace (m1 a) in *;
      replace (m2 a) in *; eauto.
    assert (m1 a = None) by eauto; congruence.
    assert (m2 a = None) by eauto; congruence.
Qed.

(* at least the locks in dom are held *)
Definition locked tid ls : S -> Prop :=
  fun s =>
  forall a, In a ls -> lock s a = Owned tid.

Definition locked_frame tid F (ls: list AT) : S -> Prop :=
  fun s =>
    F (proj s) /\
    pred_domain F ls /\
    locked tid ls s.

Definition split_frames tid F LF (ls: list AT) : S -> Prop :=
  fun s =>
    (F * LF)%pred (proj s) /\
    pred_domain LF ls /\
    locked tid ls s.

Hint Unfold split_frames locked : pred.

Theorem split_frame_ptsto_locked : forall tid F LF a v ls s,
  split_frames tid F (LF * a |-> v) ls s ->
  lock s a = Owned tid.
Proof.
  start; dispatch.
  unfold sep_star in H0 at 1.
  rewrite sep_star_is in H0.
  unfold sep_star_impl in H0.
  repeat deex.

  eauto using ptsto_valid'.
Qed.

Theorem split_frame_indifferent : forall tid F LF ls s s',
  split_frames tid F LF ls s ->
  (forall a, lock s a = Owned tid -> lock s' a = Owned tid) ->
  proj s' = proj s ->
  split_frames tid F LF ls s'.
Proof.
  start; dispatch.
Qed.

End State.

End Preservation.