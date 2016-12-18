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

(* This is almost certainly not complete *)
let sanitize = Str.global_replace (Str.regexp_string ".") "_"

(* mutable transcriber state *)
module TranscriberState = struct
  type state = {
    mutable go_types: (Go.coq_type * string) list;
    mutable structs : (string * ((string * Go.coq_type) list)) list;
    mutable maps : (string * Go.coq_type) list;
    mutable var_num: Big_int.big_int;
  }

  let rec get_go_type (ts : state) (coq_go_type : Go.coq_type) =
    try
      snd (List.find (fun x -> fst x = coq_go_type) ts.go_types)
    with Not_found ->
      match coq_go_type with
      | Go.Num -> "Num"
      | Go.Bool -> "Bool"
      | Go.DiskBlock -> "Block"
      | Go.EmptyStruct -> "Empty"
      | Go.Pair (a, b) ->
        let name = "pair_" ^ (get_go_type ts a) ^ "_" ^ (get_go_type ts b) in
        ts.structs <- (name, [("fst", a); ("snd", b)]) :: ts.structs;
        ts.go_types <- (coq_go_type, name) :: ts.go_types;
        name
      | Go.AddrMap (a) ->
        let name = "AddrMap_" ^ (get_go_type ts a) in
        ts.maps <- (name, a) :: ts.maps;
        ts.go_types <- (coq_go_type, name) :: ts.go_types;
        name

  let get_new_var (ts : state) =
    let num = ts.var_num in
    ts.var_num <- succ ts.var_num;
    num

  let go_struct_types (ts : state) =
    ts.structs

  let go_map_types (ts : state) =
    ts.maps

  let set_min_var_num (ts : state) num =
    ts.var_num <- max num ts.var_num

  let make =
    {
      go_types = [];
      structs = [];
      maps = [];
      var_num = zero;
    }


end

let go_num_const i =
  if (lt i (Big_int.power_int_positive_int 2 64)) then
     "big.NewInt(" ^ to_string i ^ ")"
  else
     "big_of_string(\"" ^ to_string i ^ "\")"

let go_modify_op (ts : TranscriberState.state)
                 (modify_op : Go.modify_op)
                 (args_tuple : Go.var Go.n_tuple) =
  match modify_op with
  | Go.SplitPair ->
    let ((pair, first), second) = Obj.magic args_tuple in
    (var_name first) ^ " = " ^ (var_name pair) ^ ".fst\n" ^
    (var_name second) ^ " = " ^ (var_name pair) ^ ".snd"
  | Go.JoinPair ->
    let ((pair, first), second) = Obj.magic args_tuple in
    (var_name pair) ^ ".fst = " ^ (var_name first) ^ "\n" ^
    (var_name pair) ^ ".snd = " ^ (var_name second)
  | Go.MapAdd ->
    let ((map, key), value) = Obj.magic args_tuple in
    (var_name map) ^ "[" ^ (var_name key) ^ ".String()] = " ^ (var_name value)
  | Go.MapFind ->
    let ((map, key), rvar) = Obj.magic args_tuple in
    let v = (var_name rvar) in
"{
  in_map, val := " ^ (var_name map) ^ "[" ^ (var_name key) ^ ".String()]
  " ^ v ^ ".fst = in_map
  " ^ v ^ ".snd = DeepCopy(val)
}"
  | Go.DuplicateOp ->
    let (dst, src) = Obj.magic args_tuple in
    (var_name dst) ^ " = DeepCopy(" ^ (var_name src) ^ ")"
  | _ -> "Modify // TODO"
  ;;

let rec go_expr expr =
  match expr with
  | Go.Var (v) -> var_name v
  | Go.Const (gType, i) -> begin
      match gType with
      | Go.Num -> go_num_const (Obj.magic i)
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
      line ^ " {\n" ^ t_text ^ "} else {\n" ^ f_text ^ "}\n"
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
  | Go.While (ex, body) ->
      "for " ^ (go_expr ex) ^ " {\n" ^ (go_stmt body ts) ^ "}\n"
  | Go.Modify (op, vars) ->
    go_modify_op ts op vars ^ "\n"
;;

let arg_pair_to_declaration (ts) (v : Go.coq_type * Go.var) =
  let (arg_t, arg) = v in
  var_name arg ^ " " ^ TranscriberState.get_go_type ts arg_t

let go_func (ts : TranscriberState.state) (v : StringMap.key * Go.coq_OperationalSpec) =
  let (name_chars, op_spec) = v in
  let name = sanitize (char_list_to_string name_chars) in
  let args = op_spec.coq_ParamVars in
  let ret = op_spec.coq_RetParamVars in
  let body = op_spec.coq_Body in
  let max_arg = List.fold_left max zero (List.map snd args) in
  TranscriberState.set_min_var_num ts (succ max_arg);

  let go_body = go_stmt body ts in

  let args_list = (List.map (arg_pair_to_declaration ts) args) in
  let ret_decls = (List.map (arg_pair_to_declaration ts) ret) in
  let pre = "func " ^ name ^ "(" ^ (String.concat ", " args_list) ^ ") " in
  let rets = "(" ^ (String.concat ", " ret_decls) ^ ")" in
  pre ^ rets ^ " {\n" ^ go_body ^ "\n" ^ "}"

let header =
"// generated header
package fscq

import (\"math/big\")

// end header
"

let go_struct_defs ts =
  List.map (fun x ->
    "type " ^ (fst x) ^ " struct {" ^
    String.concat "\n" (List.map (
      fun y ->
        let go_type = TranscriberState.get_go_type ts (snd y) in
        (fst y) ^ " " ^ go_type
      ) (snd x)) ^
    "}\n"
  ) (TranscriberState.go_struct_types ts)

let go_map_defs ts =
  let maps = TranscriberState.go_map_types ts in
  List.map (fun x ->
    let (type_name, v_type) = x in
    let go_v_type = (TranscriberState.get_go_type ts v_type) in
    "type " ^ type_name ^ " map[string]" ^ go_v_type
  ) maps

let go_type_decls ts =
  "
  type Num big.Int
  type Bool bool
  type Block DiskBlock
  type Empty struct {}
  " ^
  String.concat "\n" (go_struct_defs ts) ^
  String.concat "\n" (go_map_defs ts)
  ^ "\n"

let go_fns ts fn_map =
  String.concat "\n\n" (List.map (go_func ts) (StringMap.elements fn_map))

let  () =
  print_endline header;;
  print_endline "// type definitions\n";;
  let ts = TranscriberState.make;;
  let fns = (go_fns ts GoExtracted.extract_env);;
  print_endline (go_type_decls ts);;
  print_endline fns;;
  print_endline "func main() {}"


