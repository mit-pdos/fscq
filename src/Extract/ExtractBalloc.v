Require Import List String.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Require Import Wrappers.
Import ListNotations.

Import Go.

Require Import Balloc.

Local Open Scope string_scope.

(* Interesting problem: [IAlloc.Alloc.Bmp.ifind] takes a callback
 * function as an argument, and we have trouble wrapping it.  What
 * should we do -- do we want to extend Go semantics to include
 * function pointers?
 *)

(*
Example compile_IAlloc_alloc : sigT (fun p => source_stmt p /\
  forall env lxp xp ms,
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
    "ialloc_bmp_ifind" IAlloc.Alloc.Bmp.ifind env ->
  EXTRACT IAlloc.alloc lxp xp ms
  {{ 0 ~>? (Log.LOG.memstate * (option addr * unit)) * 1 ~> lxp * 2 ~> xp * 3 ~> ms }}
    p
  {{ fun ret => 0 ~> ret * 1 ~>? FSLayout.log_xparams * 2 ~>? FSLayout.balloc_xparams * 3 ~>? (Log.LOG.mstate * Cache.cachestate) }} // env).
Proof.
  unfold IAlloc.alloc, IAlloc.Alloc.alloc.
  compile_step.
  compile_step.
Admitted.
*)
