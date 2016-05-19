Require Import String.

(* See https://golang.org/ref/spec *)

Inductive go_type :=
  | t_bool : go_type
  | t_uint64 : go_type
  | t_string : go_type
  | t_array : forall (n : nat) (elemtype : go_type), go_type
    (* XXX go_expr for number of elements? *)
  | t_slice : forall (elemtype : go_type), go_type
  | t_struct : forall (elems : list go_type), go_type
    (* XXX actual names for elements?  then need NoDups on the names *)
  | t_ptr : forall (base : go_type), go_type
  | t_func : forall (args results : list go_type), go_type
    (* XXX actual names for arguments and result values? *)
  (* XXX missing interfaces, maps, channels *)
  .

Inductive go_literal :=
  | l_int : forall (n : nat), go_literal
  | l_string : forall (s : string), go_literal
  .

Inductive go_expr :=
  | e_literal : forall (l : go_literal), go_expr
  | e_ (* XXX *)
  .