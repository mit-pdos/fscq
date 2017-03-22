open Big
open String
open List

open Word
open GoSemantics
open StringMap

(* utility  functions *)
let char_list_to_string (l : char list) =
  String.init (List.length l) (List.nth l)

let var_name var = "val" ^ (to_string var)

(* This is almost certainly not complete *)
let sanitize x =
  let x = Str.global_replace (Str.regexp_string ".") "_" x in
  let x = capitalize_ascii x in
  x

let rec call_args_tuple_to_list (nargs : big_int) (args_tuple : Obj.t) =
  if eq nargs (zero)
    then []
  else
    let (a, b) = Obj.magic args_tuple in
    a :: (call_args_tuple_to_list (pred nargs) b)

let mapi_bignum (f : big_int -> 'a -> 'b) (l : 'a list) =
  let rec x (i : big_int) l =
    match l with
    | [] -> []
    | v :: l -> (f i v) :: (x (succ i) l)
  in x zero l

let fail_unmatched fn_name =
  failwith ("Unmatched type in " ^ fn_name);

(* mutable transcriber state *)
module TranscriberState = struct
  type fn_state = {
    mutable var_num: Big_int.big_int;
    mutable vars : (Big_int.big_int * Go.coq_type) list;
    nargs : Big_int.big_int;
  }

  type global_state = {
    mutable go_types: (Go.coq_type * string) list;
    mutable structs : (string * ((string * Go.coq_type) list)) list;
    mutable maps : (string * Go.coq_type) list;
    mutable slices : (string * Go.coq_type) list;
  }

  type state = {
    gstate : global_state;
    fstate : fn_state;
  }

  let rec get_go_type (gs : global_state) (coq_go_type : Go.coq_type) =
    try
      snd (List.find (fun x -> Go.type_eq_dec (fst x) coq_go_type) gs.go_types)
    with Not_found ->
      match coq_go_type with
      | Go.Num -> "Num"
      | Go.Bool -> "Bool"
      | Go.Buffer -> "Buffer"
      | Go.ImmutableBuffer -> "ImmutableBuffer"
      | Go.Pair (a, b) ->
        let name = "Pair_" ^ (get_go_type gs a) ^ "_" ^ (get_go_type gs b) in
        gs.structs <- (name, [("Fst", a); ("Snd", b)]) :: gs.structs;
        gs.go_types <- (coq_go_type, name) :: gs.go_types;
        name
      | Go.AddrMap (a) ->
        let name = "AddrMap_" ^ (get_go_type gs a) in
        gs.maps <- (name, a) :: gs.maps;
        gs.go_types <- (coq_go_type, name) :: gs.go_types;
        name
      | Slice (t) ->
        let name ="Slice_" ^ (get_go_type gs t) in
        gs.slices <- (name, t) :: gs.slices;
        gs.go_types <- (coq_go_type, name) :: gs.go_types;
        name
      | Go.Struct l ->
        let name = "Struct_" ^ (String.concat "_" (List.map (get_go_type gs) l)) in
        gs.structs <- (name, List.mapi (fun i t -> ("F" ^ string_of_int i, t)) l) :: gs.structs;
        gs.go_types <- (coq_go_type, name) :: gs.go_types;
        name
      | _ ->
        fail_unmatched "get_go_type"

  let get_new_var (ts : state) (t : Go.coq_type) =
    let fstate = ts.fstate in
    let num = fstate.var_num in
    fstate.var_num <- succ num;
    fstate.vars <- (num, t) :: fstate.vars;
    num

  let go_struct_types (gs : global_state) =
    gs.structs

  let go_map_types (gs : global_state) =
    gs.maps

  let go_slice_types (gs : global_state) =
    gs.slices

  let make_new_fn (gs : global_state) nargs arg_types =
    let fs = {
      nargs = nargs;
      var_num = nargs;
      vars = mapi_bignum (fun i x -> (i, x)) arg_types;
    } in
    {
      gstate = gs;
      fstate = fs;
    }

  let get_var_type (ts : state) v =
    try
      snd (List.find (fun x -> Big_int.compare_big_int (fst x) v == 0)
        ts.fstate.vars)
    with Not_found ->
      failwith ("couldn't find variable " ^ (to_string v))

  let is_param_var (ts : state) v =
    Big_int.compare_big_int v ts.fstate.nargs < 0

  let make =
    {
      go_types = [];
      structs = [];
      maps = [];
      slices = [];
    }
end

let is_ptr_type (gType : Go.coq_type) =
  match gType with
  | Go.Num -> false
  | Go.Bool -> false
  | Go.Buffer -> true
  | Go.ImmutableBuffer -> false
  | Go.Slice _ -> false
  | Go.Pair _ -> false
  | Go.AddrMap _ -> false
  | Go.Struct _ -> false
  | Go.String -> false

(* LSB first *)
let word_to_bits (w : word) = []
(*
  let rec word_to_bits' acc w =
    match w with
    | WO -> acc
    | WS (b, _, w') -> word_to_bits' (b :: acc) w'
  in word_to_bits' [] w
  *)


let b2i b = if b then 1 else 0

(* LSB first *)
let rec bits_to_int (bits : bool list) : int =
  match bits with
  | [] -> 0
  | false :: bits' -> 2 * bits_to_int bits'
  | true :: bits' -> 1 + 2 * bits_to_int bits'

let bits_to_byte bits = Char.chr (bits_to_int bits)

let rec chunk n xs =
  let rec take k xs ys = match k, xs with
    | 0, _ -> List.rev ys :: chunk n xs
    | _, [] -> if ys = [] then [] else [ys]
    | _, x::xs' -> take (k - 1) xs' (x::ys)
  in take n xs []

(* LSB first *)
let word_to_bytes (w : word) =
  let bits = word_to_bits w in
  if length bits mod 8 == 0
  then map bits_to_byte (chunk 8 bits)
  else failwith "word length not divisible by 8"

let buf_literal (buf_bytes : char list) =
  let join = String.concat ", " in
  "[]byte{" ^ join (map (fun b -> string_of_int (Char.code b)) buf_bytes) ^ "}"

let rec go_literal (gs : TranscriberState.global_state) t x =
  let join = String.concat ", " in
  let go_type = TranscriberState.get_go_type gs t in
  match t with
  | Go.Num ->
    let v = Obj.magic x in
    if (lt v (Big_int.power_int_positive_int 2 64)) then
       "Num_of_i64(" ^ to_string v ^ ")"
    else
       failwith ("integer constant too big: " ^ to_string v)
  | Go.Bool -> if Obj.magic x then "true" else "false"
  | Go.Buffer ->
    (match Obj.magic x with
     | Go.Here v -> "(*Buffer)(&" ^ buf_literal (word_to_bytes v) ^ ")"
     | Go.Moved -> "nil")
  | Go.ImmutableBuffer ->
    (match Obj.magic x with
     | Go.Here v -> buf_literal (word_to_bytes v)
     | Go.Moved -> "ImmutableBuffer(nil)")
  | Go.Slice t1 ->
    begin match Obj.magic x with
     | Go.Here v -> go_type ^ "{" ^ join (map (go_literal gs t1) v) ^ "}"
     | Go.Moved -> "(moved)"
    end
  | Go.Pair (t1, t2) ->
    let p = Obj.magic x in
    "(" ^ (go_literal gs t1 (fst p)) ^ ", " ^ (go_literal gs t2 (snd p)) ^ ")"
  | Go.AddrMap t1 ->
    (match Obj.magic x with
     | Go.Here v ->
        go_type ^ "(AddrMap_literal(" ^
         (join
             (List.map (fun x0 ->
               let (k, t2) = x0 in
               "LiteralKeyValPair{" ^ (to_string k) ^ ", " ^ (go_literal gs t1 t2) ^ "}")
               (Go.Map.elements v))) ^ "))"
     | Go.Moved -> "(moved)"
    )
  | Go.Struct l ->
    let x0 = Obj.magic x in
    let rec struct_literal tl x =
      (match tl with
       | [] -> []
       | t :: tl' ->
         let vl = Obj.magic x in
         match vl with
         | [] -> []
         | v :: vl' ->
           (go_literal gs t v) :: struct_literal tl' vl'
      ) in
    go_type ^ "{" ^ (String.concat ", " (struct_literal l x0)) ^ "}"

let do_deep_copy go_type src dst =
  src ^ ".DeepCopy(" ^ dst ^ ")"

let val_ref gType varname =
  if (is_ptr_type gType)
  then
    "*" ^ varname
  else
    varname

let var_val_ref ts var =
  let gType = (TranscriberState.get_var_type ts var) in
  (if (is_ptr_type gType) then "*" else "") ^
  (if TranscriberState.is_param_var ts var then "*" else "") ^
  (var_name var)

let var_ref ts var =
  let name = var_name var in
  if TranscriberState.is_param_var ts var
  then "(*" ^ name ^ ")"
  else name

let go_modify_op (ts : TranscriberState.state)
                 (modify_op : Go.modify_op)
                 (args_tuple : Go.var Go.n_tuple) =
  match modify_op with
  | Go.SetConst (t, value) ->
    let (var, _) = Obj.magic args_tuple in
    (var_ref ts var) ^ " = " ^ (go_literal ts.gstate t value)
  | Go.SplitPair ->
    let (pair, (first, (second, _))) = Obj.magic args_tuple in
    let fst, snd = (var_ref ts first), (var_ref ts second) in
    fst ^ ", " ^ snd ^ " = " ^ (var_ref ts pair) ^ ".Fst, " ^ (var_ref ts pair) ^ ".Snd"
  | Go.JoinPair ->
    let (pair, (first, (second, _))) = Obj.magic args_tuple in
    (var_ref ts pair) ^ ".Fst, " ^ (var_ref ts pair) ^ ".Snd = " ^
    (var_ref ts first) ^ ", " ^ (var_ref ts second)
  | Go.PairFst ->
    let (pair, (first, _)) = Obj.magic args_tuple in
    let fst = var_ref ts first in
    fst ^ " = " ^ (var_ref ts pair) ^ ".Fst"
  | Go.PairSnd ->
    let (pair, (second, _)) = Obj.magic args_tuple in
    let snd = var_ref ts second in
    snd ^ " = " ^ (var_ref ts pair) ^ ".Snd"
  | Go.MapAdd ->
    let (map, (key, (value, _))) = Obj.magic args_tuple in
    "AddrMap(" ^ (var_ref ts map) ^ ").Insert(" ^ (var_val_ref ts key) ^ ", " ^ (var_ref ts value) ^ ")"
  | Go.MapFind ->
    let (map, (key, (rvar, _))) = Obj.magic args_tuple in
    let v_type = match (TranscriberState.get_var_type ts map) with
    | Go.AddrMap t -> t
    in
    let v_go_type = TranscriberState.get_go_type ts.gstate v_type in
    let v = (var_ref ts rvar) in
"{
  in_map, val := AddrMap(" ^ (var_ref ts map) ^ ").Find(" ^ (var_ref ts key) ^ ")
  _ = val  // prevent 'unused' error
  " ^ v ^ ".Fst = Bool(in_map)
  if in_map {
  " ^ do_deep_copy v_type ("val.(" ^ (val_ref v_type v_go_type) ^ ")") ("&" ^ v ^ ".Snd") ^ "
  }
}"
  | Go.MapRemove ->
    let (map, (key, _)) = Obj.magic args_tuple in
    "AddrMap(" ^ (var_ref ts map) ^ ").Remove(" ^ (var_val_ref ts key) ^ ")"
  | Go.MapCardinality ->
    let (map, (dst, _)) = Obj.magic args_tuple in
    (var_val_ref ts dst) ^ " = AddrMap(" ^ (var_ref ts map) ^ ").Cardinality()"
  | Go.MapElements ->
    let (map, (dst, _)) = Obj.magic args_tuple in
    let v = (var_ref ts dst) in
    let m = (var_ref ts map) in
    let v_type = match (TranscriberState.get_var_type ts map) with
    | Go.AddrMap t -> t
    in
    let v_go_type = TranscriberState.get_go_type ts.gstate v_type in
    let slice_t = (TranscriberState.get_var_type ts dst) in
    let slice_go_t = (TranscriberState.get_go_type ts.gstate slice_t) in
    let slice_el_t = match slice_t with
    | Go.Slice t -> t
    in
    let val_cast_type = (val_ref v_type v_go_type) in
    "{
      // MapElements
      pairs := AddrMap(" ^ m ^ ").Elements()
      " ^ v ^ " := make(" ^ slice_go_t ^ ", 0, len(pairs))
      for _, keyval := range pairs {
        var p " ^ TranscriberState.get_go_type ts.gstate slice_el_t ^ "
        p.Fst = keyval.key
        " ^ do_deep_copy v_type ("keyval.val.(" ^ val_cast_type ^ ")") ("&p.Snd") ^ "
        " ^ v ^ " = append(" ^ v ^ ", p)
      }
    }"
  | Go.DuplicateOp ->
    let (dst, (src, _)) = Obj.magic args_tuple in
    let go_type = TranscriberState.get_var_type ts dst in
    let source = var_ref ts src in
    let destination = "&" ^ var_ref ts dst in
    do_deep_copy go_type source destination
  | Go.MoveOp ->
    let (dst, (src, _)) = Obj.magic args_tuple in
    (var_ref ts dst) ^ " = " ^ (var_ref ts src)
  | Go.AppendOp ->
    let (lvar, (xvar, _)) = Obj.magic args_tuple in
    (var_ref ts lvar) ^ " = append(" ^ (var_ref ts lvar) ^ ", " ^ (var_ref ts xvar) ^ ")"
  | Go.Uncons ->
    let (lvar, (success_var, (xvar, (l'var, _)))) = Obj.magic args_tuple in
    (* let el_t = TranscriberState.get_var_type ts xvar in *)
    (* let el_go_t = TranscriberState.get_go_type ts el_t in *)
    let l = (var_val_ref ts lvar) in
    let s = (var_val_ref ts success_var) in
    let x = (var_ref ts xvar) in
    let l' = (var_val_ref ts l'var) in
    "{
      // Uncons
      if len(" ^ l ^ ") > 0 {
        " ^ s ^ " = true
        " ^ x ^ " = (" ^ l ^ ")[0]
        " ^ l' ^ " = (" ^ l ^ ")[1:]
      } else {
        " ^ s ^ " = false
      }
    }"
  | Go.ModifyNumOp num_op -> (
    let (dst_var, (a_var, (b_var, _))) = Obj.magic args_tuple in
    let dst = (var_ref ts dst_var) in
    let a = (var_ref ts a_var) in
    let b = (var_ref ts b_var) in
    match num_op with
    | Go.Plus -> dst ^ ".Add(" ^ a ^ ", " ^ b ^ ")"
    | Go.Minus -> dst ^ ".Subtract(" ^ a ^ ", " ^ b ^ ")"
    | Go.Times -> dst ^ ".Multiply(" ^ a ^ ", " ^ b ^ ")"
    | Go.Divide -> dst ^ ".Divide(" ^ a ^ ", " ^ b ^ ")"
    | Go.Modulo -> dst ^ ".Modulo(" ^ a ^ ", " ^ b ^ ")"
    )
  | Go.StructGet _ ->
    fail_unmatched "go_modify_op StructGet"
  | Go.StructPut _ ->
    fail_unmatched "go_modify_op StructGet"
  | Go.DeserializeNum ->
      let (dst_var, (src_var, _)) = Obj.magic args_tuple in
      let dst = var_ref ts dst_var in
      let src = var_ref ts src_var in
      dst ^ " = Num_of_ImmutableBuffer(" ^ src ^ ")"
  | Go.FreezeBuffer ->
      (* Noop! *)
      let (dst_var, (src_var, _)) = Obj.magic args_tuple in
      let dst = var_ref ts dst_var in
      let src = var_ref ts src_var in
      dst ^ " = ImmutableBuffer(*" ^ src ^ ")"
  | Go.SliceBuffer ->
      let (dst_var, (src_var, (from_var, (to_var, _)))) = Obj.magic args_tuple in
      let dst = var_ref ts dst_var in
      let src = var_ref ts src_var in
      let from = var_ref ts from_var in
      let to_ = var_ref ts to_var in
      dst ^ " = ImmutableBuffer([]byte(" ^ src ^ ")[" ^ from ^ "/8 :" ^ to_ ^ "/8])"
  ;;

let go_expr_type ts expr =
  match expr with
  | Go.Var v -> TranscriberState.get_var_type ts v
  | Go.Const (gType, _) -> gType
  | Go.TestE _ -> Bool

let rec go_expr ts expr =
  match expr with
  | Go.Var (v) -> var_val_ref ts v
  | Go.Const (gType, value) ->
      go_literal ts.gstate gType value
  | Go.TestE (test, a, b) ->
    let expr_t = go_expr_type ts a in
    let go_type = TranscriberState.get_go_type ts.gstate expr_t in
    let a_expr = go_expr ts a in
    let b_expr = go_expr ts b in
    let operator = match test with
    | Go.Eq -> "eq"
    | Go.Ne -> "ne"
    | Go.Lt -> "lt"
    | Go.Le -> "le"
    in ("test_" ^ operator ^ "_" ^ go_type ^
        "(" ^ a_expr ^ ", " ^ b_expr ^ ")")
;;

let rec go_stmt stmt (ts : TranscriberState.state) =
  match stmt with
  | Go.Seq (a, b) ->
      let a_text = (go_stmt a ts) in
      let b_text = (go_stmt b ts) in
      a_text ^ b_text
  | Go.Declare (gType, fn) ->
      let var = TranscriberState.get_new_var ts gType in
      let go_type = TranscriberState.get_go_type ts.gstate gType in
      let decl_name = var_ref ts var in
      let decl_type = if (is_ptr_type gType) then "*" ^ go_type else go_type in
      let decl_lines = "var " ^ decl_name ^ " " ^ decl_type ^ "\n" ^
                       "_ = " ^ decl_name ^ "\n" in
      let text = go_stmt (fn var) ts in
      decl_lines ^ text
  | Go.Assign (var, expr) ->
      (var_val_ref ts var) ^ " = " ^ (go_expr ts expr) ^ "\n"
  | Go.If (expr, t, f) ->
      let s_expr = go_expr ts expr in
      let line = "if (bool(" ^ s_expr ^ "))" in
      let t_text = go_stmt t ts in
      let f_text = go_stmt f ts in
      line ^ " {\n" ^ t_text ^ "} else {\n" ^ f_text ^ "}\n"
  | Go.Call (nargs, name, args_tuple) ->
      let args = call_args_tuple_to_list nargs args_tuple in
      let go_args = List.map (fun v -> "&" ^ var_ref ts v) args in
      let go_name = sanitize (char_list_to_string name) in
      let call = go_name ^ "(" ^ (String.concat ", " go_args) ^ ")" in
      call ^ "\n"
  | Go.DiskRead (vvar, avar) ->
      "DiskRead(" ^ (var_ref ts vvar) ^ ", " ^ (var_ref ts avar) ^ ")\n"
  | Go.DiskWrite (vvar, avar) ->
      "DiskWrite(" ^ (var_ref ts vvar) ^ ", " ^ (var_ref ts avar) ^ ")\n"
  | Go.DiskSync ->
      "DiskSync()\n"
  | Go.Skip -> ""
  | Go.While (ex, body) ->
      "for " ^ (go_expr ts ex) ^ " {\n" ^ (go_stmt body ts) ^ "}\n"
  | Go.Modify (op, vars) ->
    go_modify_op ts op vars ^ "\n"
  | _ -> fail_unmatched "go_stmt"
;;

let arg_pair_to_declaration (ts : TranscriberState.state) (arg_num : big_int) (arg_t : Go.coq_type) =
  (var_name arg_num) ^ " " ^
  (if (is_ptr_type arg_t) then "*" else "") ^ " *" ^
  (TranscriberState.get_go_type ts.gstate arg_t)

let go_func (gs : TranscriberState.global_state) (v : StringMap.key * Go.coq_FunctionSpec) =
  let (name_chars, op_spec) = v in
  let name = sanitize (char_list_to_string name_chars) in
  let nargs = op_spec.coq_NumParamVars in
  let arg_ts = (call_args_tuple_to_list nargs op_spec.coq_ParamVars) in
  let ts = TranscriberState.make_new_fn gs nargs arg_ts in
  let body = op_spec.coq_Body in
  let go_body = go_stmt body ts in
  let args_list = (mapi_bignum (arg_pair_to_declaration ts) arg_ts) in
  let pre = "func " ^ name ^ "(" ^ (String.concat ", " args_list) ^ ") " in
  pre ^ "() {\n" ^ go_body ^ "}"

let header =
"// generated header
package fscq

// end header
"

let go_struct_defs gs =
  List.map (fun x ->
    let (t_name, fields) = x in
    "type " ^ t_name ^ " struct {" ^
    String.concat "\n" (List.map (
      fun y ->
        let (name, typ) = y in
        let go_type = TranscriberState.get_go_type gs typ in
        if (is_ptr_type typ) then
          name ^ " *" ^ go_type
        else
          name ^ " " ^ go_type
      ) fields) ^
    "}

    func (x " ^ t_name ^ ") DeepCopy (dst *" ^ t_name ^ ") {
    " ^
    String.concat "\n" (List.map (
      fun y ->
        let (name, typ) = y in
          do_deep_copy typ ("x." ^ name) ("&dst." ^ name)
      ) fields)
    ^ "
    }\n"
  ) (TranscriberState.go_struct_types gs)

let go_map_defs ts =
  let maps = TranscriberState.go_map_types ts in
  List.map (fun x ->
    let (type_name, v_type) = x in
    let go_v_type = (TranscriberState.get_go_type ts v_type) in
    let go_v_type = if (is_ptr_type v_type)
                    then "*" ^ go_v_type
                    else go_v_type in
    "type " ^ type_name ^ " AddrMap  // " ^ go_v_type ^
    "

    func (x " ^ type_name ^ ") DeepCopy (dst *" ^ type_name ^ ") { /* TODO clear dst */
    for _, v := range AddrMap(x).Elements() {
      var v_copy " ^ go_v_type ^ "
      " ^ (do_deep_copy v_type ("v.val.(" ^ go_v_type ^ ")") ("&v_copy")) ^ "
      AddrMap(*dst).Insert(v.key, v_copy)
    }
    }\n"
  ) maps

let go_slice_defs ts =
  let maps = TranscriberState.go_slice_types ts in
  List.map (fun x ->
    let (type_name, v_type) = x in
    let go_v_type = (TranscriberState.get_go_type ts v_type) in
    let go_v_type = (val_ref v_type go_v_type) in
    "type " ^ type_name ^ " []" ^ go_v_type ^
    "

    func (x " ^ type_name ^ ") DeepCopy (dst *" ^ type_name ^ ") {
    var newSlice " ^ type_name ^ "
    for _, v := range x {
        var v_copy " ^ go_v_type ^ "
        " ^ (do_deep_copy v_type "v" "&v_copy") ^ "
        newSlice = append(newSlice, v_copy)
    }
    // TODO make this copy into dst if possible
    *dst = newSlice
    }\n"
  ) maps

let go_type_decls gs =
  String.concat "\n" (go_struct_defs gs) ^
  String.concat "\n" (go_slice_defs gs) ^
  String.concat "\n" (go_map_defs gs)
  ^ "\n"

let go_fns ts fn_map =
  String.concat "\n\n" (List.map (go_func ts) (StringMap.elements fn_map))

let  () =
  print_endline header;;
  print_endline "// type definitions\n";;
  let gs = TranscriberState.make;;
  let fns = (go_fns gs GoExtracted.extract_env);;
  print_endline (go_type_decls gs);;
  print_endline fns

