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
let sanitize x =
  let x = Str.global_replace (Str.regexp_string ".") "_" x in
  let x = capitalize x in
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
      snd (List.find (fun x -> fst x = coq_go_type) gs.go_types)
    with Not_found ->
      match coq_go_type with
      | Go.Num -> "Num"
      | Go.Bool -> "bool"
      | Go.DiskBlock -> "DiskBlock"
      | Go.EmptyStruct -> "Empty"
      | Go.Pair (a, b) ->
        let name = "pair_" ^ (get_go_type gs a) ^ "_" ^ (get_go_type gs b) in
        gs.structs <- (name, [("fst", a); ("snd", b)]) :: gs.structs;
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

  let make_new_fn (gs : global_state) num_args =
    let fs = {
      var_num = num_args;
      vars = []
    } in
    {
      gstate = gs;
      fstate = fs;
    }

  let get_var_type (ts : state) v =
    snd (List.find (fun x -> Big_int.compare_big_int (fst x) v == 0)
      ts.fstate.vars)

  let make =
    {
      go_types = [];
      structs = [];
      maps = [];
      slices = [];
    }
end


let rec go_literal (gs : TranscriberState.global_state) t x =
  let join = String.concat ", " in
  let go_type = TranscriberState.get_go_type gs t in
  match t with
  | Go.Num ->
    (match Obj.magic x with
     | Go.Here v -> to_string v
     | Go.Moved -> "(moved)")
  | Go.Bool -> if Obj.magic x then "true" else "false"
  | Go.EmptyStruct -> "Empty{}"
  | Go.DiskBlock ->
    (match Obj.magic x with
     | Go.Here v -> failwith "TODO: DiskBlock -> String"
     | Go.Moved -> "(moved)")
  | Go.Slice t1 ->
    begin match Obj.magic x with
     | Go.Here v -> join (map (go_literal gs t1) v)
     | Go.Moved -> "(moved)"
    end
  | Go.Pair (t1, t2) ->
    let p = Obj.magic x in
    "(" ^ (go_literal gs t1 (fst p)) ^ ", " ^ (go_literal gs t2 (snd p)) ^ ")"
  | Go.AddrMap t1 ->
    match Obj.magic x with
     | Go.Here v ->
        go_type ^ "{" ^
         (join
             (List.map (fun x0 ->
               let (k, t2) = x0 in
               (to_string k) ^ " : " ^ (go_literal gs t1 t2))
               (Go.Map.elements v))) ^ "}"
     | Go.Moved -> "(moved)"

let zero_val gs (t : Go.coq_type) =
  let go_type = (TranscriberState.get_go_type gs t) in
  "New_" ^ go_type ^ "()"

(* mirror of Go.can_alias in GoSemantics.v *)
let rec can_alias (t : Go.coq_type) =
  match t with
  | Num -> false
  | Bool -> true
  | EmptyStruct -> true
  | DiskBlock -> false
  | Slice _ -> false
  | Pair (t1, t2) -> can_alias t1 && can_alias t2
  | AddrMap _ -> false
;;

let val_ref gType varname =
  if (can_alias gType)
  then
    varname
  else
    "*" ^ varname

let deep_copy_ref go_type var =
  if (can_alias go_type)
  then var
  else var ^ ".DeepCopy()"

let var_val_ref ts var =
  let gType = (TranscriberState.get_var_type ts var) in
  val_ref gType (var_name var)

let go_modify_op (ts : TranscriberState.state)
                 (modify_op : Go.modify_op)
                 (args_tuple : Go.var Go.n_tuple) =
  match modify_op with
  | Go.SetConst (t, value) ->
    let (var, _) = Obj.magic args_tuple in
    (var_val_ref ts var) ^ " = " ^ (go_literal ts.gstate t value)
  | Go.SplitPair ->
    let (pair, (first, (second, _))) = Obj.magic args_tuple in
    (var_name first) ^ ", " ^ (var_name second) ^ " = " ^
      (var_name pair) ^ ".fst, " ^ (var_name pair) ^ ".snd"
  | Go.JoinPair ->
    let (pair, (first, (second, _))) = Obj.magic args_tuple in
    (var_name pair) ^ ".fst, " ^ (var_name pair) ^ ".snd = " ^
    (var_name first) ^ ", " ^ (var_name second)
  | Go.MapAdd ->
    let (map, (key, (value, _))) = Obj.magic args_tuple in
    "(" ^ (var_val_ref ts map) ^ ")[" ^ (var_name key) ^ ".String()] = " ^ (var_name value)
  | Go.MapFind ->
    let (map, (key, (rvar, _))) = Obj.magic args_tuple in
    let v_type = match (TranscriberState.get_var_type ts map) with
    | Go.AddrMap t -> t
    in
    let v = (var_name rvar) in
"{
  val, in_map := (*" ^ (var_name map) ^ ")[" ^ (var_name key) ^ ".String()]
  " ^ v ^ ".fst = in_map
  if in_map {
  " ^ v ^ ".snd = " ^ (deep_copy_ref v_type "val") ^ "
  }
}"
  | Go.MapRemove ->
    let (map, (key, _)) = Obj.magic args_tuple in
    "delete(*" ^ (var_name map) ^ ", " ^ (var_name key) ^ ".String())"
  | Go.MapCardinality ->
    let (map, (dst, _)) = Obj.magic args_tuple in
    (var_val_ref ts dst) ^ ".SetInt64(len(" ^ (var_val_ref ts map) ^ "))"
  | Go.MapElements ->
    let (map, (dst, _)) = Obj.magic args_tuple in
    let v = (var_name dst) in
    let m = (var_val_ref ts map) in
    let v_type = match (TranscriberState.get_var_type ts map) with
    | Go.AddrMap t -> t
    in
    let slice_t = (TranscriberState.get_var_type ts dst) in
    let slice_go_t = (TranscriberState.get_go_type ts.gstate slice_t) in
    "{
      // MapElements
      keys := make([]string, 0, len(" ^ m ^ "))
      for k := range " ^ m ^ " {
          keys = append(keys, k)
      }
      sort.Ints(keys)

      " ^ v ^ " := make(" ^ slice_go_t ^ ", 0, len(" ^ m ^ "))
      for  _, key := range keys {
        k := big_of_string(key)
        v := " ^ (deep_copy_ref v_type (m ^ "[key]")) ^"
        p := New_" ^ slice_go_t ^ "()
        p.fst = k
        p.snd = v
        " ^ v ^ " = append(v, p)
      }
    }"
  | Go.DuplicateOp ->
    let (dst, (src, _)) = Obj.magic args_tuple in
    (var_name dst) ^ " = " ^ (var_name src) ^ ".DeepCopy()"
  | Go.AppendOp ->
    let (lvar, (xvar, _)) = Obj.magic args_tuple in
    (var_name lvar) ^ " = append(" ^ (var_name lvar) ^ ", " ^ (var_name xvar) ^ ")"
  | Go.Uncons ->
    let (lvar, (success_var, (xvar, (l'var, _)))) = Obj.magic args_tuple in
    (* let el_t = TranscriberState.get_var_type ts xvar in *)
    (* let el_go_t = TranscriberState.get_go_type ts el_t in *)
    let l = (var_name lvar) in
    let s = (var_val_ref ts success_var) in
    let x = (var_name xvar) in
    let l' = (var_name l'var) in
    "{
      // Uncons
      if len(" ^ l ^ ") > 0 {
        " ^ s ^ " = true
        " ^ x ^ " = " ^ l ^ "[0]
        " ^ l' ^ " = " ^ l ^ "[1:]
      } else {
        " ^ s ^ " = false
      }
    }"
  | _ -> fail_unmatched "go_modify_op"
  ;;

let rec go_expr ts expr =
  match expr with
  | Go.Var (v) -> var_val_ref ts v
  | Go.Const (gType, value) ->
      go_literal ts.gstate gType value
  | Go.TestE (test, a, b) ->
      let operator = match test with
      | Go.Eq -> "=="
      | Go.Ne -> "!="
      | Go.Lt -> "<"
      | Go.Le -> "<="
      in (go_expr ts a ^ " " ^ operator ^ " " ^ go_expr ts b)
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
      let var_name = var_name var in
      let decl_type = if (can_alias gType) then  go_type else "*" ^ go_type in
      let line = "var " ^ var_name ^ " " ^ decl_type ^ " = " ^ (zero_val ts.gstate gType) ^ "\n" in
      let text = go_stmt (fn var) ts in
      line ^ text
  | Go.Assign (var, expr) ->
      (var_val_ref ts var) ^ " = " ^ (go_expr ts expr) ^ "\n"
  | Go.If (expr, t, f) ->
      let s_expr = go_expr ts expr in
      let line = "if (" ^ s_expr ^ ")" in
      let t_text = go_stmt t ts in
      let f_text = go_stmt f ts in
      line ^ " {\n" ^ t_text ^ "} else {\n" ^ f_text ^ "}\n"
  | Go.Call (nargs, name, args_tuple) ->
      let args = call_args_tuple_to_list nargs args_tuple in
      let go_args = List.map var_name args in
      let go_name = sanitize (char_list_to_string name) in
      let call = go_name ^ "(" ^ (String.concat ", " go_args) ^ ")" in
      call ^ "\n"
  | Go.DiskRead (vvar, avar) ->
      "DiskRead(" ^ (var_name vvar) ^ ", " ^ (var_name avar) ^ ")\n"
  | Go.DiskWrite (vvar, avar) ->
      "DiskWrite(" ^ (var_name vvar) ^ ", " ^ (var_name avar) ^ ")\n"
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
  var_name arg_num ^ " *" ^
  (TranscriberState.get_go_type ts.gstate arg_t)

let go_func (gs : TranscriberState.global_state) (v : StringMap.key * Go.coq_FunctionSpec) =
  let (name_chars, op_spec) = v in
  let name = sanitize (char_list_to_string name_chars) in
  let nargs = op_spec.coq_NumParamVars in
  let ts = TranscriberState.make_new_fn gs nargs in
  let arg_ts = (call_args_tuple_to_list nargs op_spec.coq_ParamVars) in
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
        if (can_alias typ) then
          name ^ " " ^ go_type
        else
          name ^ " *" ^ go_type
      ) fields) ^
    "}

    func (x " ^ t_name ^ ") DeepCopy () *" ^ t_name ^ "{
    copy := new(" ^ t_name ^ ")\n" ^
    String.concat "\n" (List.map (
      fun y ->
        let (name, typ) = y in
          "copy." ^ name ^ " = " ^ (deep_copy_ref typ ("x." ^ name))
      ) fields)
    ^ "
    return copy
    }

    func New_" ^ t_name ^ " () *" ^ t_name ^ "{
    obj := new(" ^ t_name ^ ")\n" ^
    String.concat "\n" (List.map (
      fun y ->
        let (name, typ) = y in
        let go_type = TranscriberState.get_go_type gs typ in
        "obj." ^ name ^ " = New_" ^ go_type ^ "()"
      ) fields)
    ^ "
    return obj
    }\n"
  ) (TranscriberState.go_struct_types gs)

let go_map_defs ts =
  let maps = TranscriberState.go_map_types ts in
  List.map (fun x ->
    let (type_name, v_type) = x in
    let go_v_type = (TranscriberState.get_go_type ts v_type) in
    let go_v_type = if (can_alias v_type)
                    then go_v_type
                    else "*" ^ go_v_type in
    "type " ^ type_name ^ " map[string] " ^ go_v_type ^
    "

    func (x " ^ type_name ^ ") DeepCopy () *" ^ type_name ^ "{
    newMap := make(" ^ type_name ^ ")
    for k,v := range x {
      newMap[k] = " ^ (deep_copy_ref v_type "v") ^ "
    }
    return &newMap
    }

    func New_" ^ type_name ^ " () *" ^ type_name ^ "{
    obj := make(" ^ type_name ^ ")\n
    return &obj
    }\n"
  ) maps

let go_slice_defs ts =
  let maps = TranscriberState.go_slice_types ts in
  List.map (fun x ->
    let (type_name, v_type) = x in
    let go_v_type = (TranscriberState.get_go_type ts v_type) in
    let go_v_type = (val_ref v_type go_v_type) in
    "type " ^ type_name ^ " [] " ^ go_v_type ^
    "

    func (x " ^ type_name ^ ") DeepCopy () *" ^ type_name ^ "{
    var newSlice " ^ type_name ^ "
    for _, v := range x {
        newSlice = append(newSlice, " ^ (deep_copy_ref v_type "v") ^ "
    }
    return newSlice
    }

    func New_" ^ type_name ^ " () *" ^ type_name ^ "{
    return nil
    }\n"
  ) maps

let go_type_decls gs =
  String.concat "\n" (go_struct_defs gs) ^
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

