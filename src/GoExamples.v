Require Import List String.
Require Import StringMap.
Require Import Word Prog BasicProg Pred.
Require Import GoSemantics GoHoare GoFacts GoCompilationLemmas GoExtraction.
Import ListNotations.
Import Go.

Local Open Scope string_scope.

Example append_list_in_pair : sigT (fun p => forall (a x : nat) xs,
  EXTRACT Ret (a, x :: xs)
  {{ 0 ~> (a, xs) * 1 ~> x }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? nat }} // StringMap.empty _).
Proof.
  (* This is a simple example which already seems much slower than necessary *)
  Time compile. (* 4.2 seconds *)
Defined.
Eval lazy in (projT1 append_list_in_pair).

Example match_option : sigT (fun p => forall env (o : option W) (r0 : W),
  EXTRACT match o with
  | Some t => Ret (S t)
  | None => Ret 0
  end
  {{ 0 ~> o * 1 ~> r0 }}
    p
  {{ fun ret => 1 ~> ret * 0 |->? }} // env
  ).
Proof.
  compile.
Defined.

Example find_in_map : sigT (fun p => forall env (m : Map.t W) (f0 : W),
  EXTRACT (match Map.find (S f0) m with
    | Some t => Ret (S t)
    | None => Ret 0
    end)
  {{ 0 ~> m * 1 ~> f0}}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env).
Proof.
  intros. compile.
Defined.

Eval lazy in (projT1 find_in_map).

Example add_to_map : sigT (fun p => forall env m,
  EXTRACT (Ret (Map.add 1 5 m))
  {{ 0 ~> m }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros. compile.
Defined.

Example remove_from_map : sigT (fun p => forall env (m : Map.t W),
  EXTRACT (Ret (Map.remove 1 m))
  {{ 0 ~> m }}
    p
  {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros. compile.
Defined.

(*
Instance prog_equiv_equivalence T :
  Equivalence (@prog_equiv T).
Proof.
  split; hnf; unfold prog_equiv; firstorder.
  eapply H0. eapply H. trivial.
  eapply H. eapply H0. trivial.
Qed.
*)

Example micro_add_twice : sigT (fun p => forall x,
  EXTRACT Ret (1 + (2 + x))
  {{ 0 ~> x }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Defined.
Eval lazy in projT1 micro_add_twice.

Example micro_add_use_twice : sigT (fun p => forall x,
  EXTRACT Ret (x + (2 + x))
  {{ 0 ~> x }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Defined.
Eval lazy in projT1 micro_add_use_twice.

Example compile_one_read : sigT (fun p =>
  EXTRACT Read 1
  {{ 0 ~> $0 }}
    p
  {{ fun ret => 0 ~> ret }} // StringMap.empty _).
Proof.
  compile.
Defined.
Eval lazy in projT1 (compile_one_read).

Definition swap_prog a b :=
  va <- Read a;
  vb <- Read b;
  Write a vb;;
  Write b va;;
  Ret tt.

Example extract_swap_1_2 : forall env, sigT (fun p =>
  EXTRACT swap_prog 1 2 {{ emp }} p {{ fun _ => emp }} // env).
Proof.
  intros. unfold swap_prog.
  compile.
Defined.
Eval lazy in projT1 (extract_swap_1_2 (StringMap.empty _)).

(*
Declare DiskBlock
  (fun var0 : nat =>
   (DiskRead var0 (Var 0);
    Declare DiskBlock
      (fun var1 : nat =>
       (DiskRead var1 (Var 1);
        DiskWrite (Var 0) (Var var1);
        DiskWrite (Var 1) (Var var0);
        __)))%go)
*)

Lemma extract_swap_prog : forall env, sigT (fun p =>
  forall a b F, EXTRACT swap_prog a b
  {{ 0 ~> a * 1 ~> b * F }} p {{ fun _ => 0 |->? * 1 |->? * F}} // env).
Proof.
  intros. unfold swap_prog.
  compile.
Defined.
Eval lazy in projT1 (extract_swap_prog (StringMap.empty _)).

Example extract_increment : forall env, sigT (fun p => forall i,
  EXTRACT (Ret (S i)) {{ 0 ~> i }} p {{ fun ret => 0 ~> ret }} // env).
Proof.
  intros.
  compile.
Defined.
Eval lazy in projT1 (extract_increment (StringMap.empty _)).

Example extract_for_loop : forall env, sigT (fun p =>
  forall cnt nocrash crashed,
  EXTRACT (@ForN_ W W (fun i sum => Ret (sum + i)) 1 cnt nocrash crashed 0)
  {{ 0 ~> 0 * 1 ~> cnt }} p {{ fun ret => 0 ~> ret * 1 |->? }} // env).
Proof.
  intros.
  compile.
Defined.
Eval lazy in projT1 (extract_for_loop (StringMap.empty _)).
(*
Declare Num
 (fun var : W =>
  (Modify (SetConst 1) var;
   Declare Num
     (fun one : W =>
      (Modify (SetConst 1) one;
       Declare Num
         (fun term : W =>
          (term <~dup var;
           term <~num term + 1;
           While (Var var < Var term)
               0 <~num 0 + var;
               var <~num var + one)))))%go)
*)

Opaque swap_prog.

Definition extract_swap_prog_corr env := projT2 (extract_swap_prog env).
Hint Resolve extract_swap_prog_corr : extractions.

Local Open Scope map_scope.

Definition swap_env : Env :=
  ("swap" -s> {|
     NumParamVars := 2;
     NumRetParamVars := 0;
     ParamVars := ((PassedByValue, Go.Num), (PassedByValue, Go.Num));
     RetParamVars := tt; Body := projT1 (extract_swap_prog (StringMap.empty _));
     (* ret_not_in_args := ltac:(auto); *) body_source := ltac:(repeat constructor);
   |}; (StringMap.empty _)).

Lemma swap_func : voidfunc2 "swap" swap_prog swap_env.
Proof.
  unfold voidfunc2.
  intros.
  eapply extract_voidfunc2_call; eauto with extractions.
  unfold swap_env; repeat rewrite ?StringMapFacts.add_eq_o, ?StringMapFacts.add_neq_o by congruence; reflexivity.
Qed.
Hint Resolve swap_func : funcs.

Definition call_swap :=
  swap_prog 0 1;;
  Ret tt.

Example extract_call_swap :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT call_swap {{ emp }} p {{ fun _ => emp }} // env).
Proof.
  unfold call_swap.
  intros.
  compile.
Defined.

Example extract_call_swap_top :
    sigT (fun p =>
          EXTRACT call_swap {{ emp }} p {{ fun _ => emp }} // swap_env).
Proof.
  apply extract_call_swap.
  auto with funcs.
Defined.
Eval lazy in projT1 (extract_call_swap_top).

Definition rot3_prog :=
  swap_prog 0 1;;
  swap_prog 1 2;;
  Ret tt.

Example extract_rot3_prog :
  forall env,
    voidfunc2 "swap" swap_prog env ->
    sigT (fun p =>
          EXTRACT rot3_prog {{ emp }} p {{ fun _ => emp }} // env).
Proof.
  intros.
  unfold rot3_prog.
  compile.
Defined.

Example extract_rot3_prog_top :
    sigT (fun p =>
          EXTRACT rot3_prog {{ emp }} p {{ fun _ => emp }} // swap_env).
Proof.
  apply extract_rot3_prog.
  auto with funcs.
Defined.
Eval lazy in projT1 (extract_rot3_prog_top).
(*
Declare Num
 (fun var : W =>
  Declare Num
    (fun var0 : W =>
     Declare Num
       (fun var1 : W =>
        Declare Num
          (fun var2 : W =>
           (Modify (SetConst 1) var;
            Modify (SetConst 0) var0;
            Call [] "swap" [var0; var];
            Modify (SetConst 2) var1;
            Modify (SetConst 1) var2;
            Call [] "swap" [var2; var1];
            __)%go))))
*)


Definition swap2_prog :=
  a <- Read 0;
  b <- Read 1;
  if weq a b then
    Ret tt
  else
    Write 0 b;;
    Write 1 a;;
    Ret tt.

(*
Example micro_swap2 : sigT (fun p =>
  EXTRACT swap2_prog {{ emp }} p {{ fun _ => emp }} // (StringMap.empty _)).
Proof.
  compile.

  eapply hoare_weaken_post; [ | eapply CompileIf with (condvar := "c0") (retvar := "r") ];
    try match_scopes; maps.

  apply GoWrapper_unit.
  compile. apply H.

  compile.
  eapply CompileWeq.

  shelve.
  shelve.
  shelve.

  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  intros.
  eapply hoare_strengthen_pre.
  2: eapply CompileVar.
  match_scopes.

  Unshelve.
  all: congruence.
Defined.
Eval lazy in projT1 micro_swap2.
*)

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

Definition empty_env : Env := StringMap.empty _.

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
       Call 2 0 tt "swap" (var1, var0)))));
   Declare Num (fun var0 =>
    (var0 <~const 2;
     Declare Num (fun var1 =>
      (var1 <~const 1;
       Call 2 0 tt "swap" (var1, var0))))))%go.

Example rot3_function : FunctionSpec :=
  {|
    NumParamVars := 0;
    NumRetParamVars := 0;
    ParamVars := tt;
    RetParamVars := tt;
    Body := rot3_function_body;
    body_source := ltac:(repeat constructor);
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