Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import Inode.

Local Open Scope string_scope.

Instance z : GoWrapper (Rec.Rec.data INODE.IRecSig.itemtype).
  simpl.
  typeclasses eauto.
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
    "irec_get" Inode.INODE.IRec.get env ->
  EXTRACT INODE.getattrs lxp ixp inum ms
  {{ 0 ~>? (Log.LOG.memstate * ((Rec.Rec.data INODE.iattrtype) * unit)) *
     1 ~> lxp *
     2 ~> ixp *
     3 ~> inum *
     4 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? FSLayout.inode_xparams *
     3 ~>? nat *
     4 ~>? Log.LOG.memstate }} // env).
Proof.
  unfold INODE.getattrs, INODE.IRec.get_array, pair_args_helper.
  compile_step.
  compile_step.
  (* rewrite ProgMonad.bind_right_id. ? *)
Admitted.

Example compile_irec_get : sigT (fun p => source_stmt p /\
  forall env lxp ixp inum ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "log_read" Log.LOG.read env ->
  EXTRACT INODE.IRec.get lxp ixp inum ms
  {{ 0 ~>? (Log.LOG.memstate * ((Rec.Rec.data INODE.iattrtype) * unit)) *
     1 ~> lxp *
     2 ~> ixp *
     3 ~> inum *
     4 ~> ms }}
    p
  {{ fun ret => 0 ~> ret *
     1 ~>? FSLayout.log_xparams *
     2 ~>? FSLayout.inode_xparams *
     3 ~>? nat *
     4 ~>? Log.LOG.memstate }} // env).
Proof.
  unfold Inode.INODE.IRec.get, Log.LOG.read_array, pair_args_helper.
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
  (* TODO add more programs here *)
  exact env.
Defined.
