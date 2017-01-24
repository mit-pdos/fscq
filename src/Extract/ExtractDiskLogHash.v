Require Import Nat List String.
Require Import Omega.
Require Import StringMap.
Require Import Word Prog Pred AsyncDisk.
Require Import GoSemantics GoFacts GoHoare GoCompilationLemmas GoExtraction GoSepAuto GoTactics2.
Import ListNotations.

Require Import Cache FSLayout.

Require Import Wrappers.

Require Import DiskLogHash.

Import Go.
Local Open Scope string_scope.

(*
Example compile_evict : forall env, sigT (fun p => forall a cs,
  prog_func_call_lemma {| FArgs := [with_wrapper addr; with_wrapper cachestate]; FRet := with_wrapper cachestate |} "writeback" BUFCACHE.writeback env ->
  EXTRACT BUFCACHE.evict a cs
  {{ 0 ~> a * 1 ~> cs }}
    p
  {{ fun ret => 0 |->? * 1 ~> ret }} // env
  /\ source_stmt p).
Proof.
  unfold BUFCACHE.evict.
  intros.
  compile.
Defined.
Eval lazy in (projT1 (compile_evict (StringMap.empty _))).
*)

Hint Extern 2 (GoWrapper (Rec.Rec.data _)) => simpl : typeclass_instances.

Instance GoWrapper_log_hdr : GoWrapper PaddedLog.Hdr.header.
  typeclasses eauto.
Defined.

Require Import Eqdep.

Theorem extract_hdr_read :
  sigT (fun p =>
          source_stmt p /\ forall env xp cs,
            prog_func_call_lemma {| FArgs := [with_wrapper addr; with_wrapper cachestate];
                                    FRet := with_wrapper (cachestate * (valu * unit)) |}
                                 "BUFCACHE.read" BUFCACHE.read env ->
            EXTRACT PaddedLog.Hdr.read xp cs
            {{ 0 ~>? cachestate * 1 ~> xp * 2 ~> cs }}
              p
            {{ fun ret => 0 ~> ret * 1 ~>? log_xparams * 2 ~>? cachestate }} // env).
  unfold PaddedLog.Hdr.read, PaddedLog.Hdr.LAHdr.
  Ltac pattern_prog pat :=
    match goal with
    | [ |- ProgMonad.prog_equiv _ ?pr ] =>
      let Pr := fresh "Pr" in
      set pr as Pr;
      pattern pat in Pr;
      subst Pr
    end.
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
  unfold pair_args_helper.
  eapply extract_equiv_prog. 
  pattern_prog (PaddedLog.Hdr.val2hdr (fst (snd a))).
  eapply ProgMonad.bind_left_id.
  compile_step.
  unfold PaddedLog.Hdr.val2hdr.
  cbv beta iota delta [Rec.Rec.of_word eq_rec_r eq_rect eq_rec eq_sym Rec.Rec.len PaddedLog.Hdr.header_type  plus minus
                             addrlen hashlen wtl whd].
  compile_step.
  compile_step.
  (* This next [compile_step] is not useful *)
  compile_step.
Abort.