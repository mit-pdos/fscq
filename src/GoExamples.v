Require Import List String.
Require Import StringMap.
Require Import Go.
Import ListNotations.
Import Go.

Local Open Scope string_scope.

Example swap_example : stmt :=
  (Declare Num (fun a =>
   Declare Num (fun b =>
   Declare DiskBlock (fun va =>
   Declare DiskBlock (fun vb =>
     (a <~const 1;
     b <~const 2;
     DiskRead va (Var a);
     DiskRead vb (Var b);
     DiskWrite (Var a) (Var vb);
     DiskWrite (Var b) (Var va))
   )))))%go.

(* Corresponding Go:
  {
    var a Num
    {
      var b Num
      {
        var va *DiskBlock
        {
          var vb *DiskBlock
          a = 1
          b = 2
          DiskRead(va, a)
          DiskRead(vb, b)
          DiskWrite(a, vb)
          DiskWrite(b, va)
        }
      }
    }
  }
*)

Example swap_function_body : stmt :=
  (Declare DiskBlock (fun va =>
    (DiskRead va (Var 0);
     Declare DiskBlock (fun vb =>
      (DiskRead vb (Var 1);
       DiskWrite (Var 0) (Var vb);
       DiskWrite (Var 1) (Var va)))
   )))%go.

Example swap_function : OperationalSpec :=
  {|
    ParamVars := [(Go.Num, 0); (Go.Num, 1)];
    RetParamVars := [];
    Body := swap_function_body;
    args_no_dup := ltac:(auto); body_source := ltac:(repeat constructor);
  |}.

Definition empty_env : Env := StringMap.empty _.

Definition swap_env : Env :=
  StringMap.add "swap" swap_function empty_env.

(* Corresponding Go:
func swap(_0 Num, _1 Num) {
  {
    var va *DiskBlock
    {
      var vb *DiskBlock
      DiskRead(va, _0)
      DiskRead(vb, _1)
      DiskWrite(_0, vb)
      DiskWrite(_1, va)
    }
  }
}
*)

Example rot3_function_body : stmt :=
  (Declare Num (fun var0 =>
    (var0 <~const 1;
     Declare Num (fun var1 =>
      (var1 <~const 0;
       Call [] "swap" [var1; var0]))));
   Declare Num (fun var0 =>
    (var0 <~const 2;
     Declare Num (fun var1 =>
      (var1 <~const 1;
       Call [] "swap" [var1; var0])))))%go.

Example rot3_function : OperationalSpec :=
  {|
    ParamVars := [];
    RetParamVars := [];
    Body := rot3_function_body;
    args_no_dup := ltac:(auto); body_source := ltac:(repeat constructor);
  |}.

(* Corresponding Go:
func rot3() {
  {
    var var0 Num
    var0 = 1
    {
      var var1 Num
      var1 = 0
      swap(var1, var0)
    }
  }
  {
    var var0 Num
    var0 = 2
    {
      var var1 Num
      var1 = 1
      swap(var1, var0)
    }
  }
}*)

(***********************)
(*  Extract this map:  *)
(***********************)
Definition whole_env : Env :=
  StringMap.add "rot3" rot3_function swap_env.