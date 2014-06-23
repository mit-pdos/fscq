Require Import List.
Require Import Arith.
Import ListNotations.

(** File-specific automation tactic *)
Ltac t' := simpl in *;
  repeat (match goal with
            | [ H : ?x = _ |- _ ] => subst x
            | [ |- context[match ?E with pair _ _ => _ end] ] => destruct E
            | [ |- context[if eq_nat_dec ?X ?Y then _ else _] ] => destruct (eq_nat_dec X Y)
          end; simpl).
Ltac t := simpl in *; intros;
  t'; try autorewrite with core in *; intuition (eauto; try congruence); t'.


Ltac tt := simpl in *; subst; try autorewrite with core in *;
            intuition (eauto; try congruence).

Ltac cc := tt; try constructor; tt.

