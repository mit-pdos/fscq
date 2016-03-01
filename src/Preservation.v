Require Import EventCSL.
Require Import Locking.
Import List.
Import List.ListNotations.

Set Implicit Arguments.

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
  forall m, F m ->
  (forall a, (exists v, m a = Some v) <-> In a dom).

Lemma pred_domain_universal : forall F dom,
  pred_domain F dom <->
  (forall m a v, F m -> m a = Some v -> In a dom) /\
  (forall m a, F m -> In a dom -> m a <> None).
Proof.
  unfold pred_domain.
  split.
  - split; intros.
    firstorder.
    intro.
    pose proof (H _ H0 a); firstorder.
    congruence.
  - split; intros; repeat deex; eauto.
    case_eq (m a); intros; eauto; firstorder.
Qed.

Lemma exact_domain_oneside : forall F,
  (forall m1 m2, F m1 -> F m2 ->
    forall a, m1 a = None -> m2 a = None) ->
  exact_domain F.
Proof.
  unfold exact_domain.
  split; intros; eauto.
Qed.

Remark pred_domain_exact_domain : forall F dom,
  pred_domain F dom -> exact_domain F.
Proof.
  intros; apply exact_domain_oneside; intros.
  apply pred_domain_universal in H; destruct H.
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
  unfold mem_union; intros.
  destruct (m1 a); eauto.
Qed.

Lemma mem_union_none : forall m1 m2 a,
  mem_union m1 m2 a = None ->
  m1 a = None /\ m2 a = None.
Proof.
  unfold mem_union; intros.
  destruct (m1 a); eauto; congruence.
Qed.

Theorem pred_domain_combine : forall F F' dom dom',
  pred_domain F dom ->
  pred_domain F' dom' ->
  pred_domain (F * F') (dom ++ dom').
Proof.
  unfold_sep_star.
  intros.
  rewrite pred_domain_universal in *; intuition; repeat deex.
  eapply in_or_app.
  destruct (mem_union_some _ _ H4); eauto.
  eapply mem_union_none in H5; intuition.
  eapply in_app_or in H4.
  destruct H4; eauto.
Qed.

Theorem pred_domain_ptsto : forall a v,
  pred_domain (a |-> v) [a].
Proof.
  unfold ptsto; intros.
  rewrite pred_domain_universal; intuition.
  destruct (AEQ a a0); subst.
  constructor; auto.
  specialize (H2 a0); intuition; congruence.

  inversion H0; subst; eauto.
  specialize (H3 a0); intuition; congruence.
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

End State.

End Preservation.