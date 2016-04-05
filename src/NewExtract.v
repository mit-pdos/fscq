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
Hint Resolve go_type_is_nat : go.

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
Hint Resolve go_expr_is_zero : go.
Axiom go_expr_is_one : go_expr_is 1 "1"%string.
Hint Resolve go_expr_is_one : go.
Axiom go_expr_is_two : go_expr_is 2 "2"%string.
Hint Resolve go_expr_is_two : go.

Axiom go_expr_is_mul : forall a ag b bg,
  go_expr_is a ag ->
  go_expr_is b bg ->
  go_expr_is (a*b) (ag ++ "*" ++ bg).
Hint Resolve go_expr_is_mul : go.

Axiom go_expr_is_plus : forall a ag b bg,
  go_expr_is a ag ->
  go_expr_is b bg ->
  go_expr_is (a+b) (ag ++ "+" ++ bg).
Hint Resolve go_expr_is_plus : go.

(*
Axiom go_expr_is_fun1 : forall ArgType RetType (f : ArgType -> RetType) fg,
                                 agt rgt,
  go_type_is ArgType agt ->
  go_type_is RetType rgt ->

  f = .
"func (arg0 " ++ agt ++ ") " ++ rgt ++ " { return " ++ fg ++ " } "

Proof.
*)

Axiom go_expr_is_apply1 : forall ArgType RetType
                                 (f : ArgType -> RetType) fg
                                 (a : ArgType) ag,
  go_expr_is f fg ->
  go_expr_is a ag ->
  go_expr_is (f a) (fg ++ ag).
Hint Resolve go_expr_is_apply1 : go_expr.

Definition go_expr_of (T : Type) (e : T) := { ge : string | go_expr_is e ge }.

Definition go_expr_test : go_expr_of (1+2*2).
Proof.
  econstructor.
  eauto with go.
Defined.

Print go_expr_test.
Require Import ExtrOcamlString.
Extraction go_expr_test.

Definition go_expr_test2 : go_expr_of (double 2).
Proof.
  econstructor.
  eapply go_expr_is_apply1.
  eauto with go.
