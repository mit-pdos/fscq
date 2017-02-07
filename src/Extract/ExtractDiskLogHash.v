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
  compile_step.
  compile_step.
  compile_step.
  compile_step.

  (* First, freeze the buffer *)
  pattern_prog (fst (snd a)).
  Import Rec.
  cbv [Rec.data Rec.field_type string_dec string_rec string_rect Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect
      sumbool_rec sumbool_rect Bool.bool_dec bool_rec bool_rect eq_rec_r eq_rec eq_rect eq_sym eq_ind_r eq_ind] in *.
  compile_step.
  compile_step.
  pattern_prog (fst (snd a)).
  do_declare (immut_word valulen) ltac:(fun var => idtac var).
  eapply hoare_weaken.
  eapply CompileBindRet with (A := immut_word valulen) (vara := nth_var 11 vars) (a := fst (snd a)).
  3: cancel_go.
  3: cancel_go.
  
  eapply hoare_weaken.
  apply CompileFreeze with (svar := nth_var 9 vars) (dvar := nth_var 11 vars).
  rewrite valulen_is. exists (valulen_real / 8). reflexivity.
  cancel_go.
  cancel_go.

  (* Simplify the deserialization *)
  unfold PaddedLog.Hdr.val2hdr.
  set (X := fst (snd a)).
  cbv beta iota delta [Rec.Rec.of_word Rec.Rec.len PaddedLog.Hdr.header_type plus minus
                             addrlen hashlen wtl whd fst snd].
  subst X.
  compile_step.
  compile_step.
  compile_step.
  compile_step.
  do_declare (immut_word 64) ltac:(fun var => idtac var).
  eapply hoare_weaken.
  eapply CompileBindRet with (A := immut_word 64) (vara := nth_var 15 vars).
  3: solve [cancel_go].
  3: solve [cancel_go].
  
  erewrite split1_iter.

  (* Now, we have to actually call [split1] *)
  compile_step. (* TODO: this is unnecessary; we already have [fst (snd a)] in the pre *)
  Focus 1.
  match goal with
  | |- context[@Bind (word ?n)] =>
    do_declare (immut_word n)
               ltac:(fun var =>
                       eapply hoare_weaken; [ eapply CompileBindRet with (A := immut_word n) (vara := var) | solve [ cancel_go ] .. ])
  end.
  eapply CompileEqRect.
  eapply CompileEqRect with (P := immut_word).
  compile_step.
  norm.
  do 19 delay_one.
  eapply cancel_one.
  eapply PickFirst.

  match goal with
  | |- context [ ImmutableBuffer ?x ] => replace x with valulen
  end.
  reflexivity.
  change (S ?x) with (1 + x).
  repeat change (?x + S ?y) with (S x + y).
  apply le_plus_minus. rewrite valulen_is; omega.
  cancel'.
  cancel.
  Focus 1.
  Lemma wrap_wrapper_eq_rect : forall A x P p y e {Wr : GoWrapper (P y)},
      @wrap _ (GoWrapper_eq_rect A x P y e) p = @wrap _ Wr (@eq_rect A x P p y e).
  Proof.
    intros.
    reflexivity.
  Qed.
  Lemma wrap_eq_rect : forall A x P p y e {Wr : forall xy, GoWrapper (P xy)},
      wrap (@eq_rect A x P p y e) = wrap p.
  Proof.
    intros.
    rewrite <- e.
    reflexivity.
  Qed.
  repeat rewrite wrap_wrapper_eq_rect.
  repeat rewrite wrap_eq_rect.
  reflexivity.

  match goal with
  | [ |- context[split1 ?sz1_ ?sz2_ ?buf_] ] =>
    pose proof (@CompileSplit1 sz1_ sz2_ buf_ env (nth_var 15 vars) (nth_var 16 vars))
  end.
  eapply hoare_weaken.
  apply H0.
  exists (64 / 8). reflexivity.
  apply Nat.divide_add_r.
  exists (704 / 8). reflexivity.
  apply Nat.divide_sub_r.
  Lemma valulen_div_8 : Nat.divide 8 valulen.
    rewrite valulen_is. exists (valulen_real / 8). reflexivity.
  Qed.
  apply valulen_div_8.
  exists (768 / 8). reflexivity.
  cancel_go.
  cancel_go.

  (* Now, do the [wordToNat] *)
Abort.