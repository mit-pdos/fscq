Require Import Mem.
Require Import Pred.
Require Import Hlist.
Require Import Automation.
Require Import FunctionalExtensionality.
Import Eqdep.EqdepTheory.

Set Implicit Arguments.

Inductive haddress (types:list Type) :=
| haddr : forall (A:Type), member A types -> haddress types.

Theorem member_index_eq : forall (types: list Type) t (m m': member t types),
    member_index m = member_index m' ->
    m = m'.
Proof.
  intros.
  apply indices_eq in H.
  destruct H.
  rewrite <- eq_rect_eq in H.
  auto.
Qed.

Theorem member_index_neq : forall (types: list Type) t (m m': member t types),
    member_index m <> member_index m' ->
    m <> m'.
Proof.
  intros.
  intro.
  apply H.
  subst; auto.
Qed.

Definition haddress_dec {types} : forall (a1 a2: haddress types),
    {a1 = a2} + {a1 <> a2}.
Proof.
  intros.
  destruct a1, a2; auto;
  try solve [ right; intro H; inversion H].
  destruct (member_index_dec m m0); [ left | right ]; intros.
  destruct (indices_eq _ _ e); subst.
  rewrite <- eq_rect_eq; auto.

  intro.
  apply n.
  inversion H; auto.
Defined.

Theorem haddr_neq : forall types t1 t2 (m1: member t1 types) (m2: member t2 types),
    haddr m1 <> haddr m2 ->
    member_index m1 <> member_index m2.
Proof.
  intros.
  intro.
  apply indices_eq in H0.
  destruct H0; subst.
  apply H.
  rewrite <- eq_rect_eq; auto.
Qed.

Definition haddr_val_type {types} (a: haddress types) : Type :=
  match a with
  | @haddr _ A _ => A
  end.

Definition type_mem types := @mem (haddress types) haddress_dec (haddr_val_type).

Definition hlistmem types (h: hlist (fun (T:Type) => T) types) :
  type_mem types :=
  fun a => match a with
         | haddr m => Some (get m h)
         end.

Definition hlistmem_emp types : type_mem types :=
  fun a => None.

Arguments hlistmem_emp types a : clear implicits.

Definition concat_hlistmem types1 types2
           (m1: type_mem types1) (m2: type_mem types2) :
  type_mem (types1 ++ types2).
Proof.
  unfold type_mem, mem; intros.
Abort.

Definition del AT AEQ V (m: @mem AT AEQ V) a : @mem _ AEQ V :=
  fun a' => if AEQ a' a then None else m a'.

Module Examples.
  Import List.ListNotations.
  Import HlistNotations.
  Require Import Word.

  Local Example types := [nat:Type; bool:Type; nat:Type].
  Local Example someValues : hlist (@id Type) types := [( 5; true; 3 )].
  Definition number : member (nat:Type) types := HNext (HNext (HFirst)).

  Theorem number_is_3 : get number someValues = 3.
  Proof. reflexivity. Qed.

  Definition someMem : @mem _ haddress_dec _ := hlistmem someValues.

  (* TODO: replace with Coercion *)
  Definition num := haddr number.

  Theorem someMem_has_3 : (any * num |-> 3)%pred someMem.
  Proof.
    unfold_sep_star; unfold ptsto.
    exists (del (hlistmem someValues) num).
    exists (upd (hlistmem_emp types) num 3).
    unfold mem_union, mem_disjoint, any, del, upd, someMem, hlistmem_emp, hlistmem.
    intuition; try solve [ destruct matches; subst; eauto ].
    extensionality a.
    destruct matches; subst.
    destruct H0.
    unfold eq_rect_r.
    inversion e; subst.
    pose proof (EqdepFacts.eq_sigT_snd H1).
    rewrite <- eq_rect_eq in H; subst.
    rewrite <- eq_rect_eq.
    reflexivity.
    repeat match goal with
           | [ H: exists _, _ |- _ ] => destruct H; intuition
           end.
    destruct (haddress_dec x num); try congruence.
    inversion H0.
    destruct (haddress_dec num num); try congruence.
    unfold eq_rect_r.
    rewrite <- eq_rect_eq; auto.
  Qed.

End Examples.

Theorem hlistupd_memupd : forall types (h: hlist (fun (T:Type) => T) types) t (m: member t types) v,
    hlistmem (set m v h) = upd (hlistmem h) (haddr m) v.
Proof.
  unfold hlistmem.
  intros.
  extensionality a.
  destruct matches; subst.
  destruct (haddress_dec (haddr m) (haddr m0)); subst.
  inversion e; subst.
  pose proof (EqdepFacts.eq_sigT_snd H1).
  rewrite <- eq_rect_eq in H; subst.
  autorewrite with upd hlist; auto.
  assert (member_index m <> member_index m0).
  auto using haddr_neq.
  autorewrite with upd hlist; auto.
Qed.