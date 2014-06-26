Require Import Arith.
Require Omega.

Set Implicit Arguments.

(* general storage *)

Definition addr := nat.
Definition state := nat.
Definition storage := addr -> state.

Parameter st_init  : state -> storage.
Parameter st_write : storage -> addr -> state -> storage.
Parameter st_read  : storage -> addr -> state.

Axiom st_init_eq:
  forall a v, st_init v a = v.

Axiom st_write_eq:
  forall s a v, st_write s a v a = v.

Axiom st_write_ne:
  forall s a v a', a <> a' -> st_write s a v a' = s a'.

Axiom st_read_eq:
  forall s a, st_read s a = s a.

Hint Rewrite st_init_eq.
Hint Rewrite st_write_eq.
Hint Rewrite st_write_ne using omega.
Hint Rewrite st_read_eq.

Ltac st_rewrite :=
  match goal with
    | [ H : context[st_init _ _] |- _ ] =>
      rewrite st_init_eq in H
    | [ H : context[st_write _ ?A _ ?A] |- _ ] =>
      rewrite st_write_eq in H
    | [ H : context[st_write _ ?A1 _ ?A2] |- _ ] =>
      rewrite st_write_ne in H; [idtac | omega]
    | [ H : context[st_read _ _] |- _ ] =>
      rewrite st_read_eq in H
  end.

(* IO monad *)

Definition IO (R:Set) := storage -> (storage * R).

Definition IOret (R:Set) (r:R) : IO R :=
  fun st => (st, r).

Definition IObind (A B:Set) (a:IO A) (f:A->IO B) : IO B :=
  fun st =>
    let (st', ra) := a st in f ra st'.

Notation "ra <- a ; b" := (IObind a (fun ra => b))
  (right associativity, at level 60).

Notation "a ;; b" := (IObind a (fun _ => b))
  (right associativity, at level 60).


Definition IOinit (v:state) : IO unit :=
  fun st => (st_init v, tt).

Definition IOread (a:addr) : IO state :=
  fun st => (st, st_read st a).

Definition IOwrite (a:addr) (v:state) : IO unit :=
  fun st => (st_write st a v, tt).
