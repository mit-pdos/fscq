Require Import List.
Import List.ListNotations.
Open Scope list.
Require Import Coq.Program.Equality.

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

  (** Adapted from CPDT DataStruct hlist.

      In Coq v8.5beta2 at least, the return annotations are unnecessary. *)
  Fixpoint get types (l: hlist types) : member types -> B elm :=
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
                       end x (get mls')
    end.

  Fixpoint set types (l: hlist types) (new: B elm) : member types -> (hlist types) :=
    match l with
    | HNil => fun mem => HNil
    | HCons x mls' => fun mem =>
                       match mem in member ls' with
                       | HFirst _ => fun x _ => HCons new mls'
                       | HNext _ mem' => fun x set_mls' => HCons x (set_mls' mem')
                       end x (set mls' new)
    end.

End hlist.

Arguments HCons [A] [B] [a] [types] el xs.
Arguments HNil [A] [B].
Arguments HFirst [A] [elm] [types].
Arguments HNext [A] [elm] [a] [types] mem.

Module Examples.

  Local Example types := [nat; bool; nat].
  Local Example someValues : hlist (fun T : Set => T) types := HCons 5 (HCons true (HCons 3 HNil)).

  Eval simpl in get someValues HFirst.
  Eval simpl in get someValues (HNext HFirst).

  Eval simpl in set someValues false (HNext HFirst).

End Examples.

Theorem get_set : forall A B (types: list A)
                    (l : hlist B types)
                    (elm:A) (m: member elm types) v,
    get (set l v m) m = v.
Proof.
  induction l; intros.
  inversion m.

  dependent destruction m; simpl; eauto.
Qed.

Theorem get_set_other : forall A B (types: list A)
                          (l : hlist B types)
                          (elm1:A) (m1: member elm1 types)
                          (elm2:A) (m2: member elm2 types) v,
    elm1 <> elm2 ->
    get (set l v m1) m2 = get l m2.
Proof.
  induction l; intros.
  inversion m1.

  dependent destruction m1;
    dependent destruction m2; cbn;
    try congruence; auto.
Qed.