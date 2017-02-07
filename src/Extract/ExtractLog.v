Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import Log.

Local Open Scope string_scope.

Transparent LOG.begin.

Example compile_begin : sigT (fun p => source_stmt p /\
  forall env lxp ms,
  EXTRACT LOG.begin lxp ms
  {{ 0 ~>? LOG.memstate *
     1 ~> lxp *
     2 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? LOG.memstate }} // env).
Proof.
  unfold LOG.begin, LOG.MSLL, LOG.mk_memstate.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* Infinite loop extracting [MSGLog (fst ms)] *)
Admitted.

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
    "glog_read" GroupLog.GLog.read env ->
  EXTRACT LOG.read lxp a ms
  {{ 0 ~>? (LOG.memstate * valu) *
     1 ~> lxp *
     2 ~> a *
     3 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? nat *
     3 ~>? LOG.memstate }} // env).
Proof.
  unfold LOG.read, LOG.MSLL, LOG.mk_memstate.
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
Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  exact env.
Defined.
