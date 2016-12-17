(** val swap_example : Go.stmt **)
open Big
open String
open List

open GoSemantics
open StringMap

(* utility  functions *)
let char_list_to_string (l : char list) =
  String.init (List.length l) (List.nth l)

let var_name var = "val" ^ (to_string var)

(* mutable transcriber state *)
module TranscriberState = struct
  type state = {
    mutable go_structs: (string * Go.coq_type) list;
    mutable struct_num: Big_int.big_int;
    mutable var_num: Big_int.big_int;
  }

  let add_struct_type (ts : state) (p : Go.coq_type) =
  (* TODO make sure p is not in the list *)
    match p with
    | Go.Pair (a, b) ->
      let num = ts.struct_num in
      let name = "struct" ^ (to_string num) in
      let pair = (name, p) in
      ts.struct_num <- succ ts.struct_num;
      ts.go_structs <- pair :: ts.go_structs;
      name
    ;;

  let rec get_go_type (ts : state) (coq_go_type : Go.coq_type) =
    match coq_go_type with
    | Go.Num -> "*big.Int"
    | Go.Bool -> "bool"
    | Go.EmptyStruct -> "struct {}"
    | Go.DiskBlock -> "*big.Int"
    | Go.AddrMap (a) -> "AddrMap_" ^ (get_go_type ts a)
    | Go.Pair (a, b) ->
      try
        fst (List.find (fun x -> snd x == coq_go_type) ts.go_structs)
      with Not_found ->
        add_struct_type ts coq_go_type
  ;;

  let get_new_var (ts : state) =
    ts.var_num <- succ ts.var_num;
    ts.var_num
  ;;

  let make =
    {
      go_structs = [];
      struct_num = zero;
      var_num = zero;
    }

end;;



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
  | Go.TestE (test, a, b) ->
      let operator = match test with
      | Go.Eq -> "=="
      | Go.Ne -> "!="
      | Go.Lt -> "<"
      | Go.Le -> "<="
      in (go_expr a ^ " " ^ operator ^ " " ^ go_expr b)
;;

let rec go_stmt stmt (ts : TranscriberState.state) =
  match stmt with
  | Go.Seq (a, b) ->
      let a_text = (go_stmt a ts) in
      let b_text = (go_stmt b ts) in
      a_text ^ b_text
  | Go.Declare (gType, fn) ->
      let var = TranscriberState.get_new_var ts in
      let var_name = var_name var in
      let go_type = TranscriberState.get_go_type ts gType in
      let line = "var " ^ var_name ^ " " ^ go_type ^ "\n" in
      let text = go_stmt (fn var) ts in
      line ^ text
  | Go.Assign (var, expr) ->
      var_name var ^ " = " ^ (go_expr expr) ^ "\n"
  | Go.If (expr, t, f) ->
      let s_expr = go_expr expr in
      let line = "if (" ^ s_expr ^ ")" in
      let t_text = go_stmt t ts in
      let f_text = go_stmt f ts in
      line ^ "\n {\n" ^ t_text ^ "} else {\n" ^ f_text ^ "}\n"
  | Go.Call (rets, name, args) ->
      let go_args = List.map var_name args in
      let go_rets = List.map var_name rets in
      let go_name = char_list_to_string name in
      let call = go_name ^ "(" ^ (String.concat ", " go_args) ^ ")" in
      let assign = if (List.length go_rets > 0) then (String.concat ", " go_rets) ^ " = " else "" in
      assign ^ call ^ "\n"
  | Go.DiskRead (var, expr) ->
      var_name var ^ " = DiskRead(" ^ go_expr expr ^ ")\n"
  | Go.DiskWrite (value, addr) ->
      "DiskWrite(" ^ go_expr value ^ ", " ^ go_expr addr ^ ")\n"
  | Go.Skip -> ""
  | Go.Modify (op, vars) ->
      (* TODO emit correct modify operation *)
      "Modify\n"
;;

let arg_pair_to_declaration (ts) (v : Go.coq_type * Go.var) =
  let (arg_t, arg) = v in
  var_name arg ^ " " ^ TranscriberState.get_go_type ts arg_t

let go_func (ts : TranscriberState.state) (v : StringMap.key * Go.coq_OperationalSpec) =
  let (name_chars, op_spec) = v in
  let name = char_list_to_string name_chars in
  let args = op_spec.coq_ParamVars in
  let ret = op_spec.coq_RetParamVars in
  let body = op_spec.coq_Body in
  let go_body = go_stmt body ts in

  let args_list = (List.map (arg_pair_to_declaration ts) args) in
  let ret_decls = (List.map (arg_pair_to_declaration ts) args) in
  let pre = "func " ^ name ^ "(" ^ (String.concat ", " args_list) ^ ") " in
  let rets = "(" ^ (String.concat ", " ret_decls) ^ ")" in
  pre ^ rets ^ " {\n" ^ go_body ^ "\n" ^ "}"

let header =
"// generated header
package fscq

import (\"math/big\")

func DiskRead(addr *big.Int) *big.Int { return big.NewInt(0) }
func DiskWrite(val *big.Int, addr *big.Int) { }

// end header
"

let go_fns ts fn_map =
  String.concat "\n\n" (List.map (go_func ts) (StringMap.elements fn_map))


let  () =
  print_endline header;;
  let ts = TranscriberState.make in
  print_endline (go_fns ts GoExtracted.extract_env);;
  print_endline "func main() {}"


