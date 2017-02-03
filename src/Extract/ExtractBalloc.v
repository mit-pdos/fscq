Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers EnvBuild.
Import ListNotations.

Import Go.

Require Import Balloc.

Local Open Scope string_scope.

Instance GoWrapper_ialloc_item : GoWrapper IAlloc.Alloc.Bmp.Defs.item.
  typeclasses eauto.
Defined.

Example compile_IAlloc_ifind_avail : sigT (fun p => source_stmt p /\
  forall env lxp xp ms,
  EXTRACT IAlloc.Alloc.ifind_avail_nonzero lxp xp ms
  {{ 0 ~>? (Log.LOG.memstate * (option (addr * IAlloc.Alloc.Bmp.Defs.item) * unit))
   * 1 ~> lxp
   * 2 ~> xp
   * 3 ~> ms
  }}
    p
  {{ fun ret => 0 ~> ret
   * 1 ~>? FSLayout.log_xparams
   * 2 ~>? IAlloc.Alloc.BmpSig.xparams
   * 3 ~>? Log.LOG.memstate
  }} // env).
Proof.
  unfold IAlloc.Alloc.ifind_avail_nonzero.
  unfold IAlloc.Alloc.avail_nonzero.
  unfold IAlloc.Alloc.Bmp.ifind.
  unfold IAlloc.Alloc.BmpSig.RALen, IAlloc.Alloc.BmpSig.RAStart.
  unfold IAlloc.Sig.BMPLen, IAlloc.Sig.BMPStart.
  unfold pair_args_helper.

  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* why isn't this happening via [compile_step]? *)
  transform_pre.
  compile_step.

  (* compile_split should work here.. *)
Admitted.

Example compile_IAlloc_alloc : sigT (fun p => source_stmt p /\
  forall env lxp xp ms,
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "ialloc_ifind_avail" IAlloc.Alloc.ifind_avail_nonzero env ->
  prog_func_call_lemma
    {|
      FArgs := [
        with_wrapper _;
        with_wrapper _;
        with_wrapper _;
        with_wrapper _;
        with_wrapper _
      ];
      FRet := with_wrapper _
    |}
    "ialloc_bmp_put" IAlloc.Alloc.Bmp.put env ->
  EXTRACT IAlloc.alloc lxp xp ms
  {{ 0 ~>? (Log.LOG.memstate * (option addr * unit)) * 1 ~> lxp * 2 ~> xp * 3 ~> ms }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? FSLayout.log_xparams * 2 ~>? FSLayout.balloc_xparams * 3 ~>? (Log.LOG.mstate * Cache.cachestate) }} // env).
Proof.
  unfold IAlloc.alloc, IAlloc.Alloc.alloc, pair_args_helper.
  compile_step.
  compile_step.
  compile_step. (* why does this step explode [xp] into pieces? *)
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

  
  (* cannot reconstruct [xp]?? *)
Admitted.

Definition extract_env : Env.
  pose (env := StringMap.empty FunctionSpec).
  (* TODO add more programs here *)
  exact env.
Defined.
