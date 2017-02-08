Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import GroupLog.

Local Open Scope string_scope.

Example compile_read : sigT (fun p => source_stmt p /\
  forall env lxp a ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "mlog_read" MemLog.MLog.read env ->
  EXTRACT GLog.read lxp a ms
  {{ 0 ~>? (GLog.memstate * (valu * unit)) *
     1 ~> lxp *
     2 ~> a *
     3 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? nat *
     3 ~>? GLog.memstate }} // env).
Proof.
  unfold GLog.read, GLog.MSLL, GLog.mk_memstate.
  unfold MemLog.MLog.mk_memstate, MemLog.MLog.MSCache, MemLog.MLog.MSInLog.
  unfold pair_args_helper.
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

Unshelve.
  all: compile.
Defined.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "glog_read" compile_read env.
  exact env.
Defined.
