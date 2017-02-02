Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers.
Import ListNotations.

Import Go.

Require Import AsyncFS.

Local Open Scope string_scope.

Instance q : GoWrapper
   (FSLayout.log_xparams * FSLayout.inode_xparams * FSLayout.balloc_xparams).
  typeclasses eauto.
Defined.

Instance qq : GoWrapper
   (FSLayout.log_xparams * FSLayout.inode_xparams * FSLayout.balloc_xparams *
    FSLayout.balloc_xparams * FSLayout.balloc_xparams * W).
  typeclasses eauto.
Defined.

Instance q3 : GoWrapper
   (BFile.BFILE.memstate *
    (Rec.Rec.data
       (Rec.Rec.field_type
          (Rec.Rec.FS "len" (Rec.Rec.WordF addrlen)
             (Rec.Rec.FE
                [("indptr", Rec.Rec.WordF addrlen);
                ("blocks",
                Rec.Rec.ArrayF (Rec.Rec.WordF addrlen) Inode.INODE.NDirect)]
                "attrs" Inode.INODE.iattrtype))) * unit)).
  typeclasses eauto.
Defined.

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
  unfold AFS.file_get_sz, AFS.MSLL, pair_args_helper.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* why is [compile_step] breaking up [FSLayout.FSXPLog] in the return statement,
      instead of breaking up [1 ~> fsxp]? *)

  transform_pre.
  compile_step.

  (* another automation failure? *)
  (* why is it necessary to manually declare the typeclass instances above,
   * [q] and [qq], when [typeclasses eauto] solves them just fine?
   *)
  compile_decompose.
  compile_bind.
  compile_decompose.
  compile_bind.
  compile_decompose.
  compile_bind.
  compile_decompose.
  compile_bind.
  compile_decompose.
  compile_bind.
  compile_split.
  compile_split.
  compile_split.
  compile_split.
  compile_split.
  compile_split.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* super slow, something seems fishy.. *)

Admitted.
