Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import MemLog.

Local Open Scope string_scope.

Transparent Cache.BUFCACHE.read_array.

Example compile_read : sigT (fun p => source_stmt p /\
  forall env lxp a ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "cache_read" Cache.BUFCACHE.read env ->
  EXTRACT MLog.read lxp a ms
  {{ 0 ~>? (MLog.memstate * (valu * unit)) *
     1 ~> lxp *
     2 ~> a *
     3 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? nat *
     3 ~>? MLog.memstate }} // env).
Proof.
  unfold MLog.read, MLog.MSCache, MLog.MSInLog, MLog.mk_memstate, Cache.BUFCACHE.read_array.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  rewrite surjective_pairing with (p := ms) at 1.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  (* TODO: [a0] is not in scope of [?B]. Need to replace references to [a0] with generic [exists _, ...] *)
Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  exact env.
Defined.
