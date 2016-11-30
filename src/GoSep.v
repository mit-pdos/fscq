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
    wrap_type: Go.type;
    wrap':     WrappedType -> Go.type_denote wrap_type;
    wrap_inj:  forall a1 a2, wrap' a1 = wrap' a2 -> a1 = a2;
  }.

Definition wrap T {Wr: GoWrapper T} (t : T) : Go.value := Go.Val wrap_type (wrap' t).

Definition pred := @Pred.pred var Nat.eq_dec Go.value.

Notation "k ~> v" := (k |-> (wrap v))%pred (at level 35) : pred_scope.

Definition mem_of := ((fun m k => VarMap.find k m) : locals -> @Mem.mem var Nat.eq_dec Go.value).

Notation "m ≲ p" := (mem_of m ## p * any) (at level 70).


Notation "k ~>? T" := (exists val, k |-> Val (@wrap_type T _) val)%pred (at level 35) : pred_scope.

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

Theorem remove_delete :
  forall m k,
    mem_of (VarMap.remove k m) = Mem.delete (mem_of m) k.
Proof.
  intros.
  extensionality k0.
  unfold mem_of, Mem.delete.
  rewrite VarMapFacts.remove_o.
  repeat break_match; congruence.
Qed.