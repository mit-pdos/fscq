Require Import MemClass.
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

Instance haddress_dec {types} : EqDec (haddress types).
Proof.
  unfold EqDec; intros.
  destruct a, b; auto;
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
Definition type_pred types := @pred (haddress types) haddress_dec (haddr_val_type).

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

Theorem hlistmem_ptsto_unique : forall types (h: hlist _ types)
  a F F' v v',
  (F * a |-> v)%pred (hlistmem h) ->
  (F' * a |-> v')%pred (hlistmem h) ->
  v = v'.
Proof.
  intros.
  apply ptsto_valid' in H.
  apply ptsto_valid' in H0.
  congruence.
Qed.

Definition del AT AEQ V (m: @mem AT AEQ V) a : @mem _ AEQ V :=
  fun a' => if AEQ a' a then None else m a'.

Theorem haddr_member_eq:
  forall (types : list Type) (t1 t2 : Type) (m1 : member t1 types) (m2 : member t2 types),
   member_index m1 = member_index m2 -> haddr m1 = haddr m2.
Proof.
  intros.
  apply indices_eq in H.
  destruct H; subst.
  cbn; auto.
Qed.

Lemma haddr_eq_index : forall types t t' (m: member t types) (m': member t' types),
  haddr m = haddr m' ->
  member_index m = member_index m'.
Proof.
  intros.
  inversion H; subst; auto.
Qed.

Lemma haddr_eq : forall types t (m m': member t types),
  haddr m = haddr m' ->
  m = m'.
Proof.
  intros.
  apply member_index_eq.
  apply haddr_eq_index.
  auto.
Qed.

Theorem hlistmem_ptsto_del : forall types (h: hlist _ types)
  (F: pred) t (m: member t types),
  F (del (hlistmem h) (haddr m)) ->
  (F * haddr m |-> (get m h))%pred (hlistmem h).
Proof.
  intros.
  unfold_sep_star.
  exists (del (hlistmem h) (haddr m)).
  match goal with
  | [ |- exists (_:@mem ?AT ?AEQ ?V), _ ] =>
    exists (upd (@empty_mem AT AEQ V) (haddr m) (get m h))
  end.
  intuition.
  extensionality a'.
  destruct a'.
  unfold hlistmem, mem_union, del.
  destruct (haddress_dec (haddr m0) (haddr m)); auto.
  inversion e; subst.
  apply haddr_eq in e; subst.
  rewrite upd_eq; auto.

  unfold mem_disjoint, upd, del, empty_mem; intro; repeat deex.
  destruct a.
  destruct (haddress_dec (haddr m0) (haddr m)).
  inversion H1.
  inversion H2.

  unfold ptsto; intuition idtac.
  rewrite upd_eq; auto.
  unfold upd.
  destruct (haddress_dec a' (haddr m)).
  exfalso; eauto.
  unfold empty_mem; auto.
Qed.

Module Examples.
  Import List.ListNotations.
  Import HlistNotations.
  Require Import Word.

  Local Example types := [nat:Type; bool:Type; nat:Type].
  Local Example someValues : hlist (@id Type) types := [( 5; true; 3 )].
  Definition number : member (nat:Type) types := HNext (HNext (HFirst)).

  Theorem number_is_3 : get number someValues = 3.
  Proof. reflexivity. Qed.

  Definition someMem := hlistmem someValues.

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