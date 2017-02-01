Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers.
Import ListNotations.

Import Go.

Require Import AsyncFS.

Local Open Scope string_scope.

Example compile_file_get_sz : sigT (fun p => source_stmt p /\
  forall env fsxp inum ams,
(*
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
*)
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
  unfold AFS.file_get_sz, AFS.MSLL.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* This also gets stuck in an infinite loop decomposing [FSLayout.FSXPLog fsxp]
   * into its constituent components, even though we don't actually need to break
   * it up..
   *)
  (*
  repeat compile_step.
  *)

Admitted.
