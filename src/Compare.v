Require Import Prog.
Require Import BasicProg.
Require Import SepAuto.
Require Import Word.
Require Import Hoare.
Require Import Pred.
Require Import EqdepFacts.

Set Implicit Arguments.

Definition compare T sz (buf1 buf2 : word sz) rx : prog T :=
  If (weq buf1 buf2) {
    rx true
  } else {
    rx false
  }.


Theorem compare_ok :
  forall sz (buf1 buf2 : word sz),
  {< (_ : unit),
  PRE         emp
  POST RET:r  emp * [[ r = true -> buf1 = buf2 ]] * [[ r = false -> buf1 <> buf2 ]]
  CRASH       emp
  >} compare buf1 buf2.
Proof.
  unfold compare. step. step. step.
Qed.

Definition compare_hash T sz (buf1 buf2 : word sz) rx : prog T :=
  h1 <- Hash buf1;
  h2 <- Hash buf2;
  If (weq h1 h2) {
    rx true
  } else {
    rx false
  }.

Theorem compare_hash_ok :
  forall sz (buf1 buf2 : word sz),
  {< (_ : unit),
  PRE         emp
  POST RET:r  emp * [[ r = true -> buf1 = buf2 ]] * [[ r = false -> buf1 <> buf2 ]]
  CRASH       emp
  >} compare_hash buf1 buf2.
Proof.
  unfold compare_hash. step. step. step.
  step. rewrite H5 in H7. rewrite H7 in H8.
  pose proof (eq_sigT_snd H8).
  autorewrite with core in *. auto.
  step.

  Grab Existential Variables.
  all: eauto.
Qed.