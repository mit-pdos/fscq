Require Import List.
Import List.ListNotations.
Open Scope list.

Require Import Equality.
Import EqdepTheory.
Require Import Omega.

Set Implicit Arguments.

Section hlist.
  Variable A : Type.
  Variable B : A -> Type.

  Inductive hlist : list A -> Type :=
  | HNil : hlist nil
  | HCons : forall (a:A) (types: list A), B a -> hlist types -> hlist (a::types).

  Variable elm : A.

  Inductive member : list A -> Type :=
  | HFirst : forall types, member (elm :: types)
  | HNext : forall a types, member types -> member (a::types).

  Fixpoint member_index {types} (m: member types) :=
    match m with
    | HFirst _ => O
    | HNext _ m' => S (member_index m')
    end.

  (** Adapted from CPDT DataStruct hlist.

      In Coq v8.5beta2 at least, the return annotations are unnecessary. *)
  Fixpoint get_impl types (l: hlist types) : member types -> B elm :=
    match l with
    | HNil => fun mem =>
               match mem in member ls' return (match ls' with
                                               | nil => B elm
                                               | _ :: _ => unit
                                               end) with
               | HFirst _ => tt
               | HNext _ _ => tt
               end
    | HCons x mls' => fun mem =>
                       match mem in member ls' return (match ls' with
                                                       | nil => Empty_set
                                                       | x' :: ls'' =>
                                                         B x' -> (member ls'' -> B elm)
                                                         -> B elm
                                                       end) with
                       | HFirst _ => fun x _ => x
                       | HNext _ mem' => fun _ get_mls' => get_mls' mem'
                       end x (get_impl mls')
    end.

  Fixpoint set_impl types (l: hlist types) (new: B elm) : member types -> (hlist types) :=
    match l with
    | HNil => fun mem => HNil
    | HCons x mls' => fun mem =>
                       match mem in member ls' with
                       | HFirst _ => fun x _ => HCons new mls'
                       | HNext _ mem' => fun x set_mls' => HCons x (set_mls' mem')
                       end x (set_impl mls' new)
    end.

End hlist.

Definition get {A} {B: A -> Type} {types} {elm: A}
           (m: member elm types) (l: hlist B types) := get_impl l m.

Definition set {A} {B: A -> Type} {types} {elm: A}
           (m: member elm types) (new: B elm) (l: hlist B types) := set_impl l new m.

Arguments HCons [A] [B] [a] [types] el xs.
Arguments HNil [A] [B].
Arguments HFirst [A] [elm] [types].
Arguments HNext [A] [elm] [a] [types] mem.

Module Examples.

  Local Example types := [nat; bool; nat].
  Local Example someValues : hlist (fun T : Set => T) types := HCons 5 (HCons true (HCons 3 HNil)).

  Eval simpl in get HFirst someValues.
  Eval simpl in get (HNext HFirst) someValues.

  Eval simpl in set (HNext HFirst) false someValues.

End Examples.

Theorem get_set : forall A B (types: list A)
                    (l : hlist B types)
                    (elm:A) (m: member elm types) v,
    get m (set m v l) = v.
Proof.
  unfold get, set.
  induction l; intros.
  inversion m.

  dependent destruction m; simpl; eauto.
Qed.

Theorem get_set_other : forall A B (types: list A)
                          (l : hlist B types)
                          (elm1:A) (m1: member elm1 types)
                          (elm2:A) (m2: member elm2 types) v,
    member_index m1 <> member_index m2 ->
    get m2 (set m1 v l) = get m2 l.
Proof.
  unfold get, set.
  induction l; intros; eauto.

  dependent destruction m1;
    dependent destruction m2; cbn in *;
    try congruence;
    auto.
Qed.

Theorem set_get : forall A B (types: list A)
                    (l : hlist B types)
                    (elm:A) (m: member elm types) v,
    v = get m l ->
    set m v l  = l.
Proof.
  unfold get, set.
  induction l; intros; eauto; subst.

  dependent destruction m;
    cbn in *;
    auto.
  rewrite IHl; auto.
Qed.



Inductive HIn {A:Type} {B:A -> Type} (elt:A) (el:B elt) : forall (types:list A),
  hlist B types -> Prop :=
| HHere types' (rest:hlist B types') : HIn elt el (HCons el rest)
| HLater elt' (el': B elt') types' (rest:hlist B types') :
  HIn elt el rest ->
  HIn elt el (HCons el' rest).

Arguments HIn {A} {B} {elt} el {types} l.

Fixpoint hmap (A:Type) (B:A -> Type) (types:list A) (C:Type) (f: forall a, B a -> C)
         (l: hlist B types) : list C :=
  match l with
  | HNil => nil
  | @HCons _ _ a _ el l' => f a el :: (hmap f l')
  end.

Theorem hmap_length : forall A B (types:list A) C (f : forall a, B a -> C)
                        (l: hlist B types),
    length (hmap f l) = length types.
Proof.
  induction l; cbn; eauto.
Qed.

Fixpoint hmap_dep (A:Type) (B:A -> Type) (types:list A) (C:A -> Type) (f: forall a, B a -> C a)
         (l: hlist B types) : hlist C types :=
  match l with
  | HNil => HNil
  | @HCons _ _ a _ el l' => HCons (f a el) (hmap_dep C f l')
  end.

Theorem member_index_dec A (types: list A) a1
        (m1:member a1 types) a2 (m2:member a2 types) :
  {member_index m1 = member_index m2} + {member_index m1 <> member_index m2}.
Proof. decide equality. Qed.

Ltac elim_rew :=
  try lazymatch goal with
    | [ |- exists (_: _ = _), _ ] => exists eq_refl
    end;
  repeat rewrite <- Eqdep.EqdepTheory.eq_rect_eq in *;
  try congruence.

Theorem indices_eq : forall A (types: list A) t1 (m1: member t1 types) t2 (m2: member t2 types),
    member_index m1 = member_index m2 ->
    exists (H: t1 = t2), eq_rect _ (fun t => member t types) m1 _ H = m2.
Proof.
  intros.
  dependent induction types.
  inversion m1.
  dependent induction m1;
    dependent induction m2;
    cbn in *;
    try congruence.
  elim_rew.
  clear IHm1 IHm2.
  inversion H.
  destruct (IHtypes _ _ _ _ H1).
  subst.
  elim_rew.
Qed.

Theorem hin_iff_index_in : forall A (types: list A) t (m: member t types) mtypes
                             (members: hlist (fun t => member t types) mtypes),
    HIn m members <->
    In (member_index m) (hmap (fun t (m:member t types) => member_index m) members).
Proof.
  split; intros.
  - induction members; inversion H;
    repeat lazymatch goal with
      | [ H: existT _ _ _ = existT _ _ _ |- _ ] =>
        apply inj_pair2 in H
      end; cbn; subst; eauto.
  - induction members; inversion H; eauto using HLater.
    match goal with
    | [ H: member_index _ = member_index _ |- _ ] =>
      apply indices_eq in H; destruct H; subst
    end.
    elim_rew.
    constructor.
Qed.

Theorem member_index_bound : forall A (B:A -> Type) (types: list A)
                               (l: hlist B types) (a:A) (m: member a types),
    member_index m < length types.
Proof.
  intros.
  dependent induction m; cbn; try omega.
  inversion l; subst.
  intuition.
Qed.

Theorem hin_get : forall A (contents:list A) mtypes
                   (members: hlist (fun t => member t contents) mtypes)
                   t (m: member t mtypes),
    HIn (get m members) members.
Proof.
  unfold get; intros.
  dependent induction members.
  - inversion m.
  - dependent induction m; cbn;
      eauto using HHere, HLater.
Qed.

Hint Rewrite get_set : hlist.
Hint Rewrite get_set_other using (now cbn) : hlist.
Hint Rewrite set_get using (now cbn) : hlist.

(* this is the best way to use get_set without getting into trouble *)
Ltac simpl_get_set_goal :=
  autorewrite with hlist; trivial.

Ltac simpl_get_set_hyp H :=
  autorewrite with hlist in H; trivial.

Tactic Notation "simpl_get_set" := simpl_get_set_goal.
Tactic Notation "simpl_get_set" "in" hyp(H) := simpl_get_set_hyp H.

(* certainly we don't want users to reason about get_impl and set_impl *)
Global Opaque get set.
