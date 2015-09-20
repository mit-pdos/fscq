Require Import Arith.
Require Import Word.
Require Import Eqdep_dec.
Require Import FunctionalExtensionality.

Set Implicit Arguments.

Definition EqDec (T : Type) := forall (a b : T), {a = b} + {a <> b}.

(* generalized memory of any address / value type *)

Section GENMEM.
  Variable A : Type.
  Variable V : Type.
  Variable AEQ : EqDec A.

  Definition mem := A -> option V.
  Definition upd (m : mem) (a : A) (v : V) : mem :=
    fun a' => if AEQ a' a then Some v else m a'.

  Definition upd_none (m : mem) (a : A) : mem :=
    fun a' => if AEQ a' a then None else m a'.

  Definition empty_mem : mem := fun a => None.

  Theorem upd_eq : forall m (a : A) (v : V) a',
    a' = a -> upd m a v a' = Some v.
  Proof.
    intros; subst; unfold upd.
    destruct (AEQ a a); tauto.
  Qed.

  Theorem upd_ne : forall m (a : A) (v:V) a',
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



(* Disk value and address types  *)

Notation "'valubytes_real'" := 4096. (* 4KB *)
Notation "'valulen_real'" := (valubytes_real * 8)%nat.

Module Type VALULEN.
  Parameter valulen : nat.
  Parameter valubytes : nat.
  Axiom valulen_is : valulen = valulen_real.
  Axiom valubytes_is : valubytes = valubytes_real.
End VALULEN.

Module Valulen : VALULEN.
  Definition valulen := valulen_real.
  Definition valubytes := valubytes_real.
  Theorem valulen_is: valulen = valulen_real.
  Proof.
    auto.
  Qed.
  Theorem valubytes_is: valubytes = valubytes_real.
  Proof.
    auto.
  Qed.
End Valulen.

Definition addrlen := 64.
Notation "'valulen'" := (Valulen.valulen).
Notation "'valulen_is'" := (Valulen.valulen_is).
Notation "'valu'" := (word valulen).

Theorem valulen_wordToNat_natToWord : # (natToWord addrlen valulen) = valulen.
Proof.
  rewrite valulen_is.
  compute.
  reflexivity.
Qed.

(* tight bound for valulen *)
Theorem valulen_bound : valulen < pow2 16.
Proof.
  eapply Nat.lt_le_trans with (m := pow2 15 + 1).
  rewrite valulen_is.
  compute; auto.
  apply pow2_le_S.
Qed.


Notation "'addr'" := nat.
Notation "'waddr'" := (word addrlen).

Definition addr_eq_dec := Nat.eq_dec.
Definition waddr_eq_dec := @weq addrlen.

Definition waddrring := wring addrlen.
Add Ring waddrring : waddrring (decidable (weqb_sound addrlen), constants [wcst]).

