Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import BFile.

Local Open Scope string_scope.

Example compile_getlen : sigT (fun p => source_stmt p /\
  forall env lxp ixp inum ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "inode_getlen" Inode.INODE.getlen env ->
  EXTRACT BFILE.getlen lxp ixp inum ms
  {{ 0 ~>? (BFILE.memstate * (nat * unit)) *
     1 ~> lxp *
     2 ~> ixp *
     3 ~> inum *
     4 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? FSLayout.inode_xparams *
     3 ~>? nat *
     4 ~>? BFILE.memstate }} // env).
Proof.
  unfold BFILE.getlen, BFILE.MSLL, BFILE.MSAlloc, BFILE.mk_memstate, pair_args_helper.
  compile_step.
  compile_step.
  compile_step.

  (* [CompileSnd'] not automated yet *)
  eapply hoare_weaken.
  eapply CompileSnd' with (bvar := nth_var 1 vars) (pvar := 4).
  cancel_go.
  cancel_go.

  compile_step.
  compile_step.
  compile_step.
  compile_step.

  eapply hoare_weaken.
  eapply CompileFst' with (avar := nth_var 3 vars) (pvar := 4).
  cancel_go.
  cancel_go.

  compile_step.

  eapply hoare_weaken.
  eapply CompileFst' with (avar := nth_var 4 vars) (pvar := nth_var 0 vars).
  cancel_go.
  cancel_go.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  eapply hoare_weaken.
  eapply CompileSnd' with (bvar := nth_var 7 vars) (pvar := nth_var 0 vars).
  cancel_go. cancel_go.
  cancel_go.

  compile_step.
  compile_step.
  compile_step.
 
  Unshelve.
  all: compile.
Defined.

Example compile_getattrs : sigT (fun p => source_stmt p /\
  forall env lxp ixp inum ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "inode_getattrs" Inode.INODE.getattrs env ->
  EXTRACT BFILE.getattrs lxp ixp inum ms
  {{ 0 ~>? (BFILE.memstate * ((Rec.Rec.data Inode.INODE.iattrtype) * unit)) *
     1 ~> lxp *
     2 ~> ixp *
     3 ~> inum *
     4 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? FSLayout.inode_xparams *
     3 ~>? nat *
     4 ~>? BFILE.memstate }} // env).
Proof.
  unfold BFILE.getattrs, BFILE.MSLL, BFILE.MSAlloc, BFILE.mk_memstate, pair_args_helper.
  compile_step.
  compile_step.
  compile_step.
Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "bfile_getlen" compile_getlen env.
  (* add_compiled_program "bfile_getattrs" compile_getattrs env. *)
  (* TODO add more programs here *)
  exact env.
Defined.
