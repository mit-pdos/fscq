Require Import String.
Require Import List.

Import ListNotations.
Set Implicit Arguments.

(* example function to try extracting *)
Definition double (x : nat) := x * 2.

(* extraction infrastructure *)
Parameter go_type_is : forall (T : Type) (e : T) (gt : string), Prop.
Axiom go_type_is_nat : go_type_is nat "int"%string.
  (* XXX should really be "big.Int" *)
Hint Resolve go_type_is_nat : go_type.

(*
Fixpoint comma_join (args : list string) :=
  match args with
  | nil => ""%string
  | f :: nil => f
  | f :: rest => (f ++ ", " ++ comma_join rest)%string
  end.

Definition go_type_func_helper (args : list go_type) (rtype : go_type) :=
  ("func (" ++ (comma_join args) ++ ") " ++ rtype)%string.

Definition go_type_func1 : forall A R (a : go_type_of A) (r : go_type_of R), go_type_of (A -> R).
  intros.
  apply lock_type.
  apply unlock_type in a.
  apply unlock_type in r.
  refine (go_type_func_helper [a] r).
Defined.

Definition go_type_func2 : forall A B R (a : go_type_of A) (b : go_type_of B) (r : go_type_of R), go_type_of (A -> B -> R).
  intros.
  apply lock_type.
  apply unlock_type in a.
  apply unlock_type in b.
  apply unlock_type in r.
  refine (go_type_func_helper [a; b] r).
Defined.
*)

(* go expressions *)
Parameter go_expr_is : forall (T : Type) (e : T) (ge : string), Prop.
Axiom go_expr_is_zero : go_expr_is 0 "0"%string.
Hint Resolve go_expr_is_zero : go_expr.
Axiom go_expr_is_one : go_expr_is 1 "1"%string.
Hint Resolve go_expr_is_one : go_expr.
Axiom go_expr_is_two : go_expr_is 2 "2"%string.
Hint Resolve go_expr_is_two : go_expr.

Axiom go_expr_is_mul : forall a ag b bg,
  go_expr_is a ag ->
  go_expr_is b bg ->
  go_expr_is (a*b) (ag ++ "*" ++ bg).
Hint Resolve go_expr_is_mul : go_expr.

Axiom go_expr_is_plus : forall a ag b bg,
  go_expr_is a ag ->
  go_expr_is b bg ->
  go_expr_is (a+b) (ag ++ "+" ++ bg).
Hint Resolve go_expr_is_mul : go_expr.

Definition go_expr_test : exists goexpr, go_expr_is (1+2*2) goexpr.
  eexists.
  eapply go_expr_is_plus.
  eapply go_expr_is_one.
  eapply go_expr_is_mul.
  eapply go_expr_is_two.
  eapply go_expr_is_two.
Qed.
