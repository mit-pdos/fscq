Require Import StringMap.
Require Import GoSemantics.
Require Import FMapFacts.

Require Import ExtractCache.
Require Import ExtractBalloc.
Require Import ExtractAsyncFS.
Require Import ExtractBFile.
Require Import ExtractDirTree.
Require Import ExtractInode.
Require Import ExtractInodeGetLen.
Require Import ExtractLog.
Require Import ExtractGroupLog.
Require Import ExtractMemLog.

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
  add_to_env ExtractBalloc.extract_env.
  add_to_env ExtractAsyncFS.extract_env.
  add_to_env ExtractBFile.extract_env.
  add_to_env ExtractDirTree.extract_env.
  add_to_env ExtractInode.extract_env.
  add_to_env ExtractInodeGetLen.extract_env.
  add_to_env ExtractLog.extract_env.
  add_to_env ExtractGroupLog.extract_env.
  add_to_env ExtractMemLog.extract_env.
  (* TODO add more environment definitions here *)
  exact env.
Defined.
