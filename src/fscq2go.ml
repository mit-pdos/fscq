(** val swap_example : Go.stmt **)
open Go
open Big

let swap_example =
Go.Declare (Go.Num, (fun a -> Go.Declare (Go.Num, (fun b -> Go.Declare (Go.DiskBlock,
    (fun va -> Go.Declare (Go.DiskBlock, (fun vb -> Go.Seq ((Go.Assign (a, (Go.Const
        (Go.Num, (Obj.magic (Big.succ Big.zero)))))), (Go.Seq ((Go.Assign (b, (Go.Const (Go.Num,
            (Obj.magic (Big.succ (Big.succ Big.zero))))))), (Go.Seq ((Go.DiskRead (va, (Go.Var a))),
                (Go.Seq ((Go.DiskRead (vb, (Go.Var b))), (Go.Seq ((Go.DiskWrite ((Go.Var a), (Go.Var
                    vb))), (Go.DiskWrite ((Go.Var b), (Go.Var va))))))))))))))))))))
  
  
let go_type coq_go_type =
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
  | Go.If (expr, t, f) ->
      let s_expr = go_expr expr in
      let line = "if (" ^ s_expr ^ ")" in
      let (next_var', t_text) = go_stmt t next_var in
      let (next_var'', f_text) = go_stmt f next_var' in
      (next_var'', line ^ "\n {\n" ^ t_text ^ "} else {\n" ^ f_text ^ "}\n")
  | Go.Assign (var, expr) ->
      let line = var_name var ^ " = " ^ (go_expr expr) ^ "\n" in
      (next_var, line)
  | Go.DiskRead (var, expr) ->
      let line = var_name var ^ " = DiskRead(" ^ go_expr expr ^ ")\n" in
      (next_var, line)
  | Go.DiskWrite (value, addr) ->
      let line = "DiskWrite(" ^ go_expr value ^ ", " ^ go_expr addr ^ ")\n" in
      (next_var, line)
;;

let () = 
  print_endline "package main";;
  print_endline "";;
  print_endline "import (\"math/big\")";;
  print_endline "";;
  print_endline "func DiskRead(addr *big.Int) *big.Int { return big.NewInt(0) }";;
  print_endline "func DiskWrite(val *big.Int, addr *big.Int) { }";;
  print_endline "func main() {";;
  let (next_var, text) = go_stmt swap_example one in
  print_endline text;;
  print_endline "}"


