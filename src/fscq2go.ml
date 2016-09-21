(** val swap_example : Go.stmt **)
open Big
open String

open Go
open StringMap

let char_list_to_string (l : char list) =
  String.init (List.length l) (List.nth l)

let go_type (coq_go_type : Go.coq_type) =
  match coq_go_type with
  | Go.Num -> "*big.Int"
  | Go.Bool -> "bool"
  | Go.EmptyStruct -> "struct {}"
  | Go.DiskBlock -> "*big.Int"
;;

let var_name var = "val" ^ (to_string var)


let rec go_expr expr =
  match expr with
  | Go.Var (v) -> var_name v
  | Go.Const (gType, i) -> begin
      match gType with
      | Go.Num -> 
          let i = (Obj.magic i) in
          if (lt i (Big_int.power_int_positive_int 2 64)) then
                     "big.NewInt(" ^ to_string i ^ ")"
                  else
                     "big_of_string(\"" ^ to_string i ^ "\")"
      end
  | Go.Binop (op, a, b) ->
      let operator = match op with
      | Go.Plus -> "+"
      | Go.Minus -> "-"
      | Go.Times -> "*"
      in (go_expr a ^ " " ^ operator ^ " " ^ go_expr b)
;;

let rec go_stmt stmt next_var =
  match stmt with
  | Go.Seq (a, b) ->
      let (next_var', a_text) = (go_stmt a next_var) in
      let (next_var'', b_text) = (go_stmt b next_var') in
      (next_var'', a_text ^ b_text)
  | Go.Declare (gType, fn) -> 
      let var_name = var_name next_var in
      let line = "var " ^ var_name ^ " " ^ (go_type gType) ^ "\n" in
      let (next_var', text) = go_stmt (fn next_var) (succ next_var) in
      (next_var', "{\n" ^ line ^ text ^ "}\n")
  | Go.Assign (var, expr) ->
      let line = var_name var ^ " = " ^ (go_expr expr) ^ "\n" in
      (next_var, line)
  | Go.If (expr, t, f) ->
      let s_expr = go_expr expr in
      let line = "if (" ^ s_expr ^ ")" in
      let (next_var', t_text) = go_stmt t next_var in
      let (next_var'', f_text) = go_stmt f next_var' in
      (next_var'', line ^ "\n {\n" ^ t_text ^ "} else {\n" ^ f_text ^ "}\n")
  | Go.Call (rets, name, args) ->
      let go_args = List.map var_name args in
      let go_rets = List.map var_name rets in
      let go_name = char_list_to_string name in
      let call = go_name ^ "(" ^ (String.concat ", " go_args) ^ ")" in
      let assign = if (List.length go_rets > 0) then (String.concat ", " go_rets) ^ " = " else "" in
      (next_var, assign ^ call ^ "\n")
  | Go.DiskRead (var, expr) ->
      let line = var_name var ^ " = DiskRead(" ^ go_expr expr ^ ")\n" in
      (next_var, line)
  | Go.DiskWrite (value, addr) ->
      let line = "DiskWrite(" ^ go_expr value ^ ", " ^ go_expr addr ^ ")\n" in
      (next_var, line)
;;

let arg_pair_to_declaration (v : Go.coq_type * Go.var) =
  let (arg_t, arg) = v in
  var_name arg ^ " " ^ go_type arg_t

let go_func (v : StringMap.key * Go.coq_OperationalSpec) =
  let (name_chars, op_spec) = v in
  let name = char_list_to_string name_chars in
  let args = op_spec.coq_ParamVars in
  let next_var = succ (List.fold_left max zero (List.map snd args)) in
  let ret = op_spec.coq_RetParamVars in
  let body = op_spec.coq_Body in
  let (_, go_body) = go_stmt body next_var in
  "func " ^ name ^ "(" ^ (concat ", " (List.map arg_pair_to_declaration args)) ^ ") " ^
     "(" ^ (concat ", " (List.map arg_pair_to_declaration ret)) ^ ") {\n" ^
     go_body ^ "\n" ^
  "}"

let header =
"// generated header
package fscq

import (\"math/big\")

func DiskRead(addr *big.Int) *big.Int { return big.NewInt(0) }
func DiskWrite(val *big.Int, addr *big.Int) { }

// end header
"

let go_fns fn_map =
  concat "\n\n" (List.map go_func (StringMap.elements fn_map))


let  () =
  print_endline header;;
  print_endline (go_fns GoFunctions.go_functions);;
  print_endline "func main() {}"


