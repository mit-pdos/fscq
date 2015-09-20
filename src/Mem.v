Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition EqDec (T : Type) := forall (a b : T), {a = b} + {a <> b}.

(* generalized memory of any address / value type *)

Definition mem {A : Type} {AEQ : EqDec A} {V : Type} := A -> option V.

Section GENMEM.
  Variable A : Type.
  Variable V : Type.
  Variable AEQ : EqDec A.

  Definition upd (m : @mem A AEQ V) (a : A) (v : V) : @mem A AEQ V :=
    fun a' => if AEQ a' a then Some v else m a'.

  Definition upd_none (m : @mem A AEQ V) (a : A) : @mem A AEQ V :=
    fun a' => if AEQ a' a then None else m a'.

  Definition empty_mem : @mem A AEQ V := fun a => None.

  Theorem upd_eq : forall m (a : A) (v : V) a',
    a' = a -> upd m a v a' = Some v.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a a); tauto.
  Qed.

  Theorem upd_ne : forall m (a : A) (v : V) a',
    a' <> a
    -> upd m a v a' = m a'.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a' a); tauto.
  Qed.

  Theorem upd_repeat: forall m (a : A) (v v':V),
    upd (upd m a v') a v = upd m a v.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a x); intros; subst.
    repeat rewrite upd_eq; auto.
    repeat rewrite upd_ne; auto.
  Qed.

  Theorem upd_comm: forall m (a0 : A) (v0 : V) a1 v1, a0 <> a1
    -> upd (upd m a0 v0) a1 v1 = upd (upd m a1 v1) a0 v0.
  Proof.
    intros; apply functional_extensionality; intros.
    case_eq (AEQ a1 x); case_eq (AEQ a0 x); intros; subst; try congruence;
    repeat ( ( rewrite upd_ne by auto ) || ( rewrite upd_eq by auto ) ); auto.
  Qed.

End GENMEM.
