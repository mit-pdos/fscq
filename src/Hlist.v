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

(* since get is opaque, need lemmas for its computational behavior -
we give the recursive equations it would be defined by *)
Definition get_first : forall A (B: A -> Type) types elm
                         (l: hlist B types) (v: B elm),
    get HFirst (HCons v l) = v.
Proof.
  cbn; auto.
Qed.

Definition get_next : forall A (B: A -> Type) types elm
                        (m: member elm types) (l: hlist B types) (v: B elm),
    get (HNext m) (HCons v l) = get m l.
Proof.
  cbn; auto.
Qed.

Delimit Scope hlist_scope with hlist.

Open Scope hlist_scope.

Module HlistNotations.

Notation " [( )] " := (HNil) (format "[( )]") : hlist_scope.
Notation " [( x )] " := (HCons x HNil) : hlist_scope.
Notation " [( x ; .. ; y )] " := (HCons x .. (HCons y HNil) ..) : hlist_scope.

End HlistNotations.

Local Ltac hlist_nth_member n :=
  match n with
  | O => uconstr:HFirst
  | S ?n' =>
    let rest := hlist_nth_member n' in
    uconstr:(HNext rest)
  end.

(* hget n l converts n to the nth member of l by creating an untyped
term and refining it in the context of l. The intended use case is as
a term ltac:(hget 2 l), for example.

The tactic will fail if n is
too large; the error message will complain that the type of l is not
hlist _ (a_1 :: ... :: a_k :: ... :: ?elm :: ?types), where a_1 ::
... :: a_k are the actual indices of l; this is due to the refinement
being unable to write the type indexing list as n elements. *)
Tactic Notation "hget" constr(n) constr(l) :=
  let m := hlist_nth_member n in
  let v := uconstr:(get m l) in
  refine v.

Section hget_nth.

  Hint Constructors member.
  Hint Resolve tt.

  Definition hmember A :
    forall n (types: list A),
      match nth_error types n with
      | Some a => member a types
      | None => unit
      end.
  Proof.
    induction n; intros;
    destruct types; cbn in *; auto.
    specialize (IHn types).
    destruct (nth_error types n); auto.
  Defined.

  (** Gallina definition of hget n l tactic, returning a unit if the n
  is out-of-bounds. *)
  Definition hget_n A B (types: list A) (n:nat) (l: hlist B types) :
    match nth_error types n with
    | Some a => B a
    | None => unit
    end.
  Proof.
    case_eq (nth_error types n); intros; auto.
    pose (hmember n types) as m.
    rewrite H in m.
    apply (get m l).
  Defined.

End hget_nth.

Module Examples.
  Import HlistNotations.

  Local Example types := [nat; bool; nat].
  Local Example someValues : hlist (@id Set) types := [( 5; true; 3 )].

  Example get_0 : ltac:(hget 0 someValues) = 5
    := eq_refl.

  Example get_0' : hget_n 0 someValues = 5
    := eq_refl.

  Example get_1 : ltac:(hget 1 someValues) = true
    := eq_refl.

  Example get_1' : hget_n 1 someValues = true
    := eq_refl.

  Example get_2 : set (HNext HFirst) false someValues = [( 5; false; 3 )]
                                                          := eq_refl.

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
                    (elm:A) (m: member elm types),
    set m (get m l) l = l.
Proof.
  unfold get, set.
  induction l; intros; eauto.

  dependent destruction m;
    cbn in *;
    auto.
  rewrite IHl; auto.
Qed.

Theorem set_get_eq : forall A B (types: list A)
                    (l : hlist B types)
                    (elm:A) (m: member elm types) v,
    v = get m l ->
    set m v l = l.
Proof.
  intros; subst; apply set_get.
Qed.

Theorem set_set : forall A B (types: list A)
                    (l : hlist B types)
                    (elm:A) (m: member elm types) v v',
    set m v' (set m v l) = set m v' l.
Proof.
  unfold set.
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
Proof. decide equality. Defined.

Theorem member_index_0 : forall A (types: list A) t1 (m: member t1 (t1 :: types)),
  member_index m = 0 ->
  m = HFirst.
Proof.
  intros.
  dependent induction m; auto.
  inversion H.
Qed.

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
  exists eq_refl.
  cbn; auto.
  inversion H.
  destruct (IHtypes _ _ _ _ H1).
  exists x.
  subst; cbn; eauto.
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
    cbn.
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

Theorem get_hmap_error : forall A B (types:list A) C
                        (f : forall a, B a -> C)
                        (l: hlist B types) (a:A) (m: member a types),
    Some (f a (get m l)) = nth_error (hmap f l) (member_index m).
Proof.
  intros.
  induction l;
    dependent induction m; cbn; eauto.
Qed.

Theorem get_hmap : forall A B (types:list A) C
                        (f : forall a, B a -> C)
                        (l: hlist B types) (a:A) (m: member a types)
                        (def:C),
    f a (get m l) = nth (member_index m) (hmap f l) def.
Proof.
  intros.
  induction l;
    dependent induction m; cbn; eauto.
Qed.

Hint Rewrite hmap_length : hlist.
Hint Rewrite get_set : hlist.
Hint Rewrite get_set_other using (cbn; solve [ auto 3 ]) : hlist.
Hint Rewrite set_get using (cbn; solve [ auto 3 ]) : hlist.
Hint Rewrite set_get_eq using (cbn; solve [ auto 3 ]) : hlist.
Hint Rewrite set_set using (cbn; solve [ auto 3 ]) : hlist.

(* this is the best way to use get_set without getting into trouble *)
Ltac simpl_get_set_goal :=
  autorewrite with hlist; trivial.

Ltac simpl_get_set_hyp H :=
  autorewrite with hlist in H; trivial.

(* TODO: measure that this is faster than
[autorewrite with hlist in *] *)
Ltac simpl_get_set_all :=
  repeat match goal with
      | [ H: context[get _ (set _ _ _)] |- _ ] =>
        progress simpl_get_set_hyp H
      | [ H: context[set _ (set _ _ _)] |- _ ] =>
        progress simpl_get_set_hyp H
      | [ H: context[set _ (get _ _ _)] |- _ ] =>
        progress simpl_get_set_hyp H
         end;
  simpl_get_set_goal.

Tactic Notation "simpl_get_set" := simpl_get_set_goal.
Tactic Notation "simpl_get_set" "in" hyp(H) := simpl_get_set_hyp H.
Tactic Notation "simpl_get_set" "in" "*" := simpl_get_set_all.

(* certainly we don't want users to reason about get_impl and set_impl *)
Global Opaque get set.
