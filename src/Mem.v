Require Import FunctionalExtensionality.
Import EqNotations.
Require Import Eqdep_dec.

Set Universe Polymorphism.
Set Implicit Arguments.

Definition DecEq (T : Type) := forall (a b : T), {a=b}+{a<>b}.
Definition mem {A : Type} {eq : DecEq A} {V: A -> Type} := forall a, option (V a).
Definition upd {A : Type} {eq : DecEq A} {V: A -> Type}
           (m : @mem A eq V) (a : A) (v : V a) : @mem A eq V.
Proof.
  intro a'.
  destruct (eq a' a); intros.
  rewrite e.
  exact (Some v).
  exact (m a').
Defined.

Definition upd_none {A : Type} {eq : DecEq A} {V : A -> Type} (m : @mem A eq V) (a : A) : @mem A eq V :=
  fun a' => if eq a' a then None else m a'.

Definition empty_mem {AT : Type} {AEQ : DecEq AT} {V : AT -> Type} : @mem AT AEQ V := fun a => None.

Section GenMem.

Variable A : Type.
Variable V : A -> Type.
Variable aeq : DecEq A.

Theorem upd_eq : forall m (a : A) (v:V a),
  @upd A aeq V m a v a = Some v.
Proof.
  intros; subst; unfold upd.
  destruct (aeq a a); try congruence.
  unfold eq_rect_r.
  (* assumption-free proof using UIP for decidable equality *)
  rewrite <- eq_rect_eq_dec; auto.
Qed.

Theorem upd_ne : forall m (a : A) (v:V a) a',
  a' <> a
  -> @upd A aeq V m a v a' = m a'.
Proof.
  intros; subst; unfold upd.
  destruct (aeq a' a); tauto.
Qed.

Ltac simpl_upd :=
  subst;
  repeat (rewrite upd_eq) ||
         (rewrite upd_ne by auto).

Theorem upd_repeat: forall m (a : A) (v v':V a),
  @upd A aeq V (@upd A aeq V m a v') a v = upd m a v.
Proof.
  intros.
  extensionality a'.
  case_eq (aeq a a'); intros; now simpl_upd.
Qed.

Lemma upd_same : forall (m: @mem A aeq V) a v,
    m a = Some v ->
    upd m a v = m.
Proof.
  intros.
  extensionality a'.
  case_eq (aeq a a'); intros; now simpl_upd.
Qed.

Theorem upd_comm: forall m (a0 : A) (v0:V a0) a1 v1, a0 <> a1
  -> @upd A aeq V (@upd A aeq V m a0 v0) a1 v1 = @upd A aeq V (upd m a1 v1) a0 v0.
Proof.
  intros; extensionality a'.
  case_eq (aeq a1 a'); case_eq (aeq a0 a'); intros; try congruence; now simpl_upd.
Qed.

End GenMem.

Require Import Basics.

Corollary upd_eq_eqn : forall AT AEQ V
  (m: @mem AT AEQ (const V)) a a' v,
  a = a' ->
  upd m a v a' = Some v.
Proof.
  intros; subst; apply upd_eq.
Qed.

(* existential variable hint *)
Hint Immediate empty_mem.

Hint Rewrite upd_eq : upd.
Hint Rewrite upd_eq_eqn using (solve [ auto ] ) : upd.
Hint Rewrite upd_ne using (solve [ auto ]) : upd.
Hint Rewrite upd_repeat : upd.
Hint Rewrite upd_same using (solve [ auto ]) : upd.

Tactic Notation "simpl_upd" :=
  try subst;
  autorewrite with upd.

Tactic Notation "simpl_upd" "in" hyp(H) :=
  try subst;
  autorewrite with upd in H.

Tactic Notation "simpl_upd" "in" "*" :=
  try subst;
    autorewrite with upd in *.
