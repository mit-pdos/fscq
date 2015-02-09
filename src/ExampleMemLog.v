Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import Word.
Require Import SepAuto.
Require Import BasicProg.
Require Import MemLog.
Require Import Bool.
Require Import GenSep.
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
  ms <- MEMLOG.begin xp ;
  v0 <- MEMLOG.read xp s0 ms;
  ms <- MEMLOG.write xp s0 (v0 ^+ $1) ms;
  v1 <- MEMLOG.read xp s1 ms;
  ms <- MEMLOG.write xp s1 (v1 ^+ $1) ms;
  ok <- MEMLOG.commit xp ms;
  If (bool_dec ok true) {
    rx ok
  } else {
    rx false
  }.

(* Several preconditions for MEMLOG.init.  *)
Theorem log_inc_two_ok: forall xp s0 s1,
  {< mbase v0 v1 F,
  PRE    MEMLOG.rep xp (NoTransaction mbase) ms_empty * 
         [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST:r [[ r = false ]] * MEMLOG.rep xp (NoTransaction mbase) ms_empty \/
         [[ r = true ]] * exists m', MEMLOG.rep xp (NoTransaction m') ms_empty *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH  MEMLOG.log_intact xp mbase \/
         exists m', MEMLOG.log_intact xp m' *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  >} log_inc_two xp s0 s1.
Proof.
  unfold log_inc_two; unfold MEMLOG.log_intact.
  intros.
  hoare.
Qed.

Hint Extern 1 ({{_}} log_inc_two _ _ _ _) => apply log_inc_two_ok : prog.

(* Several preconditions for MEMLOG.init.  *)
Theorem log_inc_two_recover_ok: forall xp s0 s1,
  {< mbase v0 v1 F,
  PRE     MEMLOG.rep xp (NoTransaction mbase) ms_empty * 
          [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST:r  [[ r = false ]] * MEMLOG.rep xp (NoTransaction mbase) ms_empty \/
          [[ r = true ]] * exists m', MEMLOG.rep xp (NoTransaction m') ms_empty *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH:r MEMLOG.rep xp (NoTransaction mbase) ms_empty \/
          exists m', MEMLOG.rep xp (NoTransaction m') ms_empty *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  >} log_inc_two xp s0 s1 >> MEMLOG.recover xp.
Proof.
  intros.
  unfold forall_helper; intros mbase v0 v1 F.
  exists (MEMLOG.log_intact xp mbase \/
          exists d', MEMLOG.log_intact xp d' *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem d') ]])%pred; intros.

  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply log_inc_two_ok.
  eapply MEMLOG.recover_ok.
  cancel.
  step.
  cancel.
  cancel.
  cancel.
  cancel.
  cancel.
  cancel.
  cancel.
  step.
  cancel.
  cancel.
  cancel.
  step.
  cancel.
  cancel.
Qed.
