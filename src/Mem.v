Require Import FunctionalExtensionality.

Set Implicit Arguments.


Definition DecEq (T : Type) := forall (a b : T), {a=b}+{a<>b}.
Definition mem {A : Type} {eq : DecEq A} {V: Type} := A -> option V.
Definition upd {A : Type} {eq : DecEq A} {V: Type} (m : @mem A eq V) (a : A) (v : V) : @mem A eq V :=
  fun a' => if eq a' a then Some v else m a'.
Definition upd_none {A : Type} {eq : DecEq A} {V : Type} (m : @mem A eq V) (a : A) : @mem A eq V :=
  fun a' => if eq a' a then None else m a'.

Definition empty_mem {AT : Type} {AEQ : DecEq AT} {V : Type} : @mem AT AEQ V := fun a => None.


Section GenMem.

Variable V : Type.
Variable A : Type.
Variable aeq : DecEq A.

Theorem upd_eq : forall m (a : A) (v:V) a',
  a' = a
  -> @upd A aeq V m a v a' = Some v.
Proof.
  intros; subst; unfold upd.
  destruct (aeq a a); tauto.
Qed.

Theorem upd_ne : forall m (a : A) (v:V) a',
  a' <> a
  -> @upd A aeq V m a v a' = m a'.
Proof.
  intros; subst; unfold upd.
  destruct (aeq a' a); tauto.
Qed.

Theorem upd_repeat: forall m (a : A) (v v':V),
  upd (@upd A aeq V m a v') a v = upd m a v.
Proof.
  intros; apply functional_extensionality; intros.
  case_eq (aeq a x); intros; subst.
  repeat rewrite upd_eq; auto.
  repeat rewrite upd_ne; auto.
Qed.

Theorem upd_comm: forall m (a0 : A) (v0:V) a1 v1, a0 <> a1
  -> upd (@upd A aeq V m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
Proof.
  intros; apply functional_extensionality; intros.
  case_eq (aeq a1 x); case_eq (aeq a0 x); intros; subst; try congruence;
  repeat ( ( rewrite upd_ne by auto ) || ( rewrite upd_eq by auto ) ); auto.
Qed.

End GenMem.

(* existential variable hint *)
Hint Immediate empty_mem.