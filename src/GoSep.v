Require Import FunctionalExtensionality.
Require Import PeanoNat List FMapAVL Structures.OrderedTypeEx.
Require Import RelationClasses Morphisms.
Require Import VerdiTactics.
Require Import Go.
Require Import Pred.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Go.

Class GoWrapper (WrappedType: Type) :=
  {
    wrap:      WrappedType -> Go.value;
    wrap_inj:  forall v v', wrap v = wrap v' -> v = v';
    wrapped_type: Go.type;
    wrap_type: forall v, type_of (wrap v) = wrapped_type;
  }.

Definition pred := @Pred.pred var Nat.eq_dec Go.value.

Notation "k ~> v" := (k |-> (wrap v))%pred (at level 35) : pred_scope.

Definition mem_of := ((fun m k => VarMap.find k m) : locals -> @Mem.mem var Nat.eq_dec Go.value).

Notation "m ≲ p" := (mem_of m ## p * any) (at level 70).

Module VarMapFacts := FMapFacts.WFacts_fun(Nat_as_OT)(VarMap).

Theorem add_upd :
  forall m k v,
    mem_of (VarMap.add k v m) = Mem.upd (mem_of m) k v.
Proof.
  intros.
  extensionality k0.
  unfold mem_of, Mem.upd.
  rewrite VarMapFacts.add_o.
  repeat break_match; congruence.
Qed.