Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import AsyncFS.
Require Import FSLayout.

Local Open Scope string_scope.

Ltac dbg_find_pre x:= match goal with
|- EXTRACT _ {{ ?pre }} _ {{ _ }} // _ =>
  match pre with
  | context [ptsto ?k ?y] =>
    match y with
    | context [x] =>
      idtac k y; fail 1
    end
  end || idtac
end.


Example compile_file_get_sz : sigT (fun p => source_stmt p /\
  forall env fsxp inum ams,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "log_begin" Log.LOG.begin env ->

  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "dirtree_getattr" DirTree.DIRTREE.getattr env ->

  EXTRACT AFS.file_get_sz fsxp inum ams
  {{ 0 ~>? (bool * Log.LOG.memstate * (word 64 * unit)) *
     1 ~> fsxp *
     2 ~> inum *
     3 ~> ams }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.fs_xparams *
     2 ~>? addr *
     3 ~>? BFile.BFILE.memstate }} // env).
Proof.
  unfold AFS.file_get_sz, AFS.MSLL, pair_args_helper, BFile.BFILE.MSAlloc, Inode.INODE.ABytes.

  compile_step.
  compile_step.
  compile_step.
  solve [repeat compile_step].
  compile_step.

  compile_ret_transform_part.
  solve [repeat compile_split].
  do_duplicate (FSXPLog fsxp). (* need this after the call *)
  compile_call.

  compile_step.
  compile_step.
  solve [repeat compile_step].
  compile_step.
  do_duplicate (FSXPLog fsxp). (* need this after the call *)
  compile_ret_transformable.
  solve [repeat compile_step].
  compile_call.

  simpl Rec.Rec.data in *.
  compile_step.

  change Log.LOG.commit_ro with Log.LOG.begin.
  solve [repeat compile_step].

  cbv [Inode.INODE.iattr Inode.INODE.iattrtype Rec.Rec.data].
  solve [repeat compile_step].
Unshelve.
  all : compile.
Defined.

Eval lazy in (projT1 compile_file_get_sz).

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  add_compiled_program "asyncfs_file_get_sz" compile_file_get_sz env.
  (* TODO add more programs here *)
  exact env.
Defined.
