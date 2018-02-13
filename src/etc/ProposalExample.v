Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import Word.
Require Import SepAuto.
Require Import BasicProg.
Require Import Log.
Require Import Bool.
Require Import Idempotent.

Set Implicit Arguments.

Definition inc_two T s0 s1 rx : prog T :=
  v0 <- Read s0 ;
  Write s0 (v0 ^+ $1) ;;
  v1 <- Read s1 ;
  Write s1 (v1 ^+ $1) ;;
  rx tt.

Theorem inc_two_ok: forall s0 s1,
  {< v0 v1,
  PRE    s0 |-> v0 * s1 |-> v1
  POST:r s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1)
  CRASH  s0 |-> v0 * s1 |-> v1 \/
         s0 |-> (v0 ^+ $1) * s1 |-> v1 \/
         s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1)
  >} inc_two s0 s1.
Proof.
  unfold inc_two.
  hoare.
Qed.


Definition log_inc_two T xp s0 s1 rx : prog T :=
  LOG.begin xp ;;
  v0 <- LOG.read xp s0 ;
  ok0 <- LOG.write xp s0 (v0 ^+ $1) ;
  v1 <- LOG.read xp s1 ;
  ok1 <- LOG.write xp s1 (v1 ^+ $1) ;
  If (bool_dec (andb ok0 ok1) true) {
    LOG.commit xp ;;
    rx true
  } else {
    LOG.abort xp ;;
    rx false
  }.


Theorem log_inc_two_ok: forall xp s0 s1,
  {< d v0 v1 F,
  PRE    LOG.rep xp (NoTransaction d) *
         [[ (s0 |-> v0 * s1 |-> v1 * F)%pred d ]]
  POST:r [[ r = false ]] * LOG.rep xp (NoTransaction d) \/
         [[ r = true ]] * exists d', LOG.rep xp (NoTransaction d') *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred d' ]]
  CRASH  LOG.log_intact xp d \/
         exists d', LOG.log_intact xp d' *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred d' ]]
  >} log_inc_two xp s0 s1.
Proof.
  unfold log_inc_two, LOG.log_intact.
  hoare.
Qed.

Hint Extern 1 ({{_}} log_inc_two _ _ _ _) => apply log_inc_two_ok : prog.

Theorem log_inc_two_recover_ok: forall xp s0 s1,
  {< d v0 v1 F,
  PRE     LOG.rep xp (NoTransaction d) *
          [[ (s0 |-> v0 * s1 |-> v1 * F)%pred d ]]
  POST:r  [[ r = false ]] * LOG.rep xp (NoTransaction d) \/
          [[ r = true ]] * exists d', LOG.rep xp (NoTransaction d') *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred d' ]]
  CRASH:r LOG.rep xp (NoTransaction d) \/
          exists d', LOG.rep xp (NoTransaction d') *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred d' ]]
  >} log_inc_two xp s0 s1 >> LOG.recover xp.
Proof.
  intros.
  unfold forall_helper; intros d v0 v1 F.
  exists (LOG.log_intact xp d \/
          exists d', LOG.log_intact xp d' *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred d' ]])%pred.
  intros.

  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eauto with prog.
  eapply LOG.recover_ok.

  cancel.
  hoare_unfold LOG.unfold_intact.
  cancel.
  hoare_unfold LOG.unfold_intact.
  LOG.unfold_intact; cancel; cancel.
  hoare_unfold LOG.unfold_intact.
  LOG.unfold_intact; cancel; cancel.
Qed.
