Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers.
Import ListNotations.
Import Go.

Local Open Scope string_scope.
Local Open Scope list_scope.
Local Open Scope pred_scope.

Ltac argtuple' pre var :=
  match pre with
  | context [var |-> (Val ?V _)] =>
    let X := argtuple' pre (S var) in
    match X with
    | (?count, ?X)  =>
      constr:(pair (S count) (pair V X))
    end
  | context [var |-> @wrap _ ?Wr _] =>
    let X := argtuple' pre (S var) in
    let P := constr:(@wrap_type _ Wr) in
    match X with
    | (?count, ?X)  => constr:(pair (S count) (pair P X))
    end
  | _ => constr:(pair 0 tt)
  end.

Ltac argtuple PRE :=
  argtuple' PRE 0.

Ltac add_to_env name P env :=
  match type of P with
  | context [EXTRACT _ {{ ?PRE }} ?body_ {{ ?POST }} // _] =>
    match POST with
    | (fun ret : ?R => ?POST) =>
      lazymatch constr:(fun ret : mark_ret R => (_:find_ret POST)) with
      | (fun ret => ?rvar) =>
        match (argtuple PRE) with
        | (?nargs, ?args) =>
          let x_ := fresh in
          set (body := body_);
          set (op := {|
            NumParamVars := nargs;
            ParamVars := args;
            Body := body;
            body_source := ltac:(eauto);
          |});
          set (env' := StringMap.add name op env);
          simpl in *; subst body; subst env;
          rename env' into env; subst op
        end
      end
    end
  end.

Ltac make_instance_step :=
  match goal with
  | [|- word ?x] => apply wzero
  | [|- immut_word ?x] => apply wzero
  | _ => econstructor
  end.

Ltac make_instance :=
  abstract (repeat make_instance_step).

Ltac add_compiled_program name compiled env :=
  let P := fresh in
  let e_ := fresh in
  let H := fresh in
  let S := fresh "src" in
  destruct compiled as [e_ P];
  match type of P with
  | Logic.and (source_stmt _) _ =>
    apply proj1 in P as S;
    apply proj2 in P
  | Logic.and _ (source_stmt _) =>
    apply proj2 in P as S;
    apply proj1 in P
  end;
  repeat match type of P with
  | forall x : ?X, ?y =>
      let x_ := fresh "v" in
      cut X; [intro x_; specialize (P x_) | make_instance ]
  end;
  (add_to_env name P env;
  (* Remove unnecessary variables *)
  clear P;
  repeat match goal with
  | [env := ?X, v : _ |- _] =>
    lazymatch type of v with
    | context [ProgOk] => fail
    | _ => clear v
    end
  end).
