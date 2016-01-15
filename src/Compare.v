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


Lemma hash_safe_eq : forall hm h1 h2 sz (k1 k2 : word sz),
  hash_safe hm h1 k1 ->
  hash_safe (upd_hashmap' hm h1 k1) h2 k2 ->
  h1 = h2 ->
  k1 = k2.
Proof.
  unfold hash_safe, upd_hashmap'; intros. subst.
  destruct (weq h2 default_hash) eqn:Hdef.

  destruct hm;
    (unfold hashmap_get in *; rewrite Hdef in *;
    destruct H as [ H' | H' ]; inversion H';
    destruct H0 as [ H0' | H0' ]; inversion H0';
    rewrite H2 in H3; pose proof (eq_sigT_snd H3); autorewrite with core in *; auto).

  subst.
  rewrite upd_hashmap_eq in H0; auto.
  destruct H0 as [ H0' | H0' ]; inversion H0'.
  pose proof (eq_sigT_snd H1). autorewrite with core in *. auto.
Qed.

Theorem compare_hash_ok :
  forall sz (buf1 buf2 : word sz),
  {< (_ : unit),
  PRE         emp
  POST RET:r  emp * [[ r = true -> buf1 = buf2 ]] * [[ r = false -> buf1 <> buf2 ]]
  CRASH       emp
  >} compare_hash buf1 buf2.
Proof.
  unfold compare_hash.
  hoare.

  rewrite <- H5 in H9.
  eapply hash_safe_eq; eauto.

  Grab Existential Variables.
  all: eauto.
Qed.