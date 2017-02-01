Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers.
Import ListNotations.

Import Go.

Require Import DirTree.

Local Open Scope string_scope.

Example compile_mkfile : sigT (fun p => source_stmt p /\
  forall env fsxp dnum name fms,
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
  unfold DIRTREE.mkfile.
  compile_step.
  compile_step.

  (* The next step fails to find (WrapByTransforming BFILE.memstate).
     Why does it even search for that? *)

  (*
  compile_step.
  *)
Admitted.
