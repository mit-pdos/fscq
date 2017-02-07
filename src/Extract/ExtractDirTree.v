Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import DirTree.

Local Open Scope string_scope.

Example compile_mkfile : sigT (fun p => source_stmt p /\
  forall env fsxp dnum name fms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "ialloc_alloc" Balloc.IAlloc.alloc env ->
  EXTRACT DIRTREE.mkfile fsxp dnum name fms
  {{ 0 ~>? (BFile.BFILE.memstate * (Errno.res addr * unit)) *
     1 ~> fsxp *
     2 ~> dnum *
     3 ~> name *
     4 ~> fms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.fs_xparams *
     2 ~>? addr *
     3 ~>? string *
     4 ~>? BFile.BFILE.memstate }} // env).
Proof.
  unfold DIRTREE.mkfile, DIRTREE.MSLL.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  compile_step. (* same issue as ExtractAsyncFS *)

  (* This seems to turn into an actual infinite loop; maybe a problem with extracting
   * something out of a two-level record (log_xparams inside fs_xparams)?
   *)
  (*
  repeat compile_step.
  *)

Admitted.

Example compile_getattr : sigT (fun p => source_stmt p /\
  forall env fsxp inum fms,
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
    "bfile_getattrs" BFile.BFILE.getattrs env ->
  EXTRACT DIRTREE.getattr fsxp inum fms
  {{ 0 ~>? (BFile.BFILE.memstate * (Errno.res addr * unit)) *
     1 ~> fsxp *
     2 ~> inum *
     3 ~> fms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.fs_xparams *
     2 ~>? addr *
     3 ~>? BFile.BFILE.memstate }} // env).
Proof.
  unfold DIRTREE.getattr, DIRTREE.MSLL.
  compile_step.
  compile_step.
  compile_step.

  (* This seems to turn into an actual infinite loop; maybe a problem with extracting
   * something out of a two-level record (log_xparams inside fs_xparams)?
   *)
  (*
  repeat compile_step.
  *)

Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  (* TODO add more programs here *)
  exact env.
Defined.
