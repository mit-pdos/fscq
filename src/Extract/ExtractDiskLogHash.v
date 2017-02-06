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
  pattern_prog (PaddedLog.Hdr.val2hdr (fst (snd a))).
  compile_step.
  unfold PaddedLog.Hdr.val2hdr.
  cbv beta iota delta [Rec.Rec.of_word Rec.Rec.len PaddedLog.Hdr.header_type plus minus
                             addrlen hashlen wtl whd].
  compile_step.
  compile_step.
  do_declare (immut_word 768) ltac:(fun var => idtac var).
  eapply hoare_weaken.
  eapply CompileBindRet with (vara := nth_var 7 vars) (HA := GoWrapper_immut_word _).
  3: cancel_go.
  3: cancel_go.
  compile_step.
  Require Import ProgMonad.
  Lemma bind_f : forall A B C (a : A) (f : A -> B) (g : B -> prog C),
      prog_equiv (x <- Ret (f a); g x) (x' <- Ret a; g (f x')).
  Proof.
    intros.
    rewrite ?bind_left_id.
    reflexivity.
  Qed.
  (* We'll want the automation to keep punting [eq_rec*] down the line as much as possible *)
  eapply extract_equiv_prog.
  symmetry.
  apply bind_f with (f := fun x => eq_rec_r word x PaddedLog.Hdr.plus_minus_header).
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* First, freeze the buffer *)
  pattern_prog (fst (snd a)).
  do_declare (immut_word valulen) ltac:(fun var => idtac var).
  eapply hoare_weaken.
  eapply CompileBindRet with (vara := nth_var 12 vars) (a := fst (snd a)) (HA := GoWrapper_immut_word _).
  3: cancel_go.
  3: cancel_go.
  eapply hoare_weaken.
  apply CompileFreeze with (svar := nth_var 8 vars) (dvar := nth_var 12 vars).
  rewrite valulen_is. exists (valulen_real / 8). reflexivity.
  cancel_go.
  cancel_go.

  (* Now, we have to actually call [split1] *)
  eapply hoare_weaken.
  match goal with
  | [ |- context[split1 ?sz1_ ?sz2_ ?buf_] ] =>
    pose proof (@CompileSplit1 sz1_ sz2_ buf_ env (nth_var 7 vars) (nth_var 12 vars))
  end.
  apply H0.
  exists (768 / 8). reflexivity.
  apply Nat.divide_sub_r.
  rewrite valulen_is. exists (valulen_real / 8). reflexivity.
  exists (768 / 8). reflexivity.
  match goal with
  | [ |- context[wrap (@eq_rec_r ?A ?x ?P ?p ?y ?e)] ] =>
    replace (wrap (@eq_rec_r A x P p y e)) with (wrap (fst (snd a) : immut_word _)) by admit (* TODO *)
  end.
  cancel_go.
  cancel_go.

  (* We did a split call! *)
Abort.