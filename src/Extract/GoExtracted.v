Require Import StringMap.
Require Import GoSemantics.
Require Import FMapFacts.

Require Import ExtractCache.

About StringMap.fold.
Print StringMap.

Module StringMapUtils := WProperties_fun StringKey StringMap.

Ltac add_to_env env_extr :=
  match goal with
  | env := _ |- _ =>
    let env' := fresh "env" in
    set (env' := StringMapUtils.update env_extr env);
    subst env;
    rename env' into env
  end.

Definition extract_env : Go.Env.
  pose (env := StringMap.empty Go.FunctionSpec).
  add_to_env ExtractCache.extract_env.
  (* TODO add more environment definitions here *)
  exact env.
Defined.
