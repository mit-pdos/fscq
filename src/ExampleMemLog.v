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

Theorem log_inc_two_ok: forall xp s0 s1,
  {< mbase v0 v1 F,
  PRE    MEMLOG.rep xp (NoTransaction mbase) ms_empty * 
         [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST:r [[ r = false ]] * MEMLOG.rep xp (NoTransaction mbase) ms_empty \/
         [[ r = true ]] * exists m', MEMLOG.rep xp (NoTransaction m') ms_empty *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH  MEMLOG.log_intact xp mbase \/
         exists m', (MEMLOG.log_intact xp m' \/ MEMLOG.log_intact_either xp mbase m') *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  >} log_inc_two xp s0 s1.
Proof.
  unfold log_inc_two.
  hoare_unfold log_intact_unfold.
Qed.

Hint Extern 1 ({{_}} log_inc_two _ _ _ _) => apply log_inc_two_ok : prog.

Hint Rewrite crash_xform_sep_star_dist crash_xform_or_dist crash_xform_exists_comm : crash_xform.

Definition nop {T} rx : prog T := rx tt.

Theorem nop_ok:
  {< (_: unit),
  PRE    emp
  POST:r emp
  CRASH  emp
  >} nop.
Proof.
  unfold nop.
  hoare.
Qed.

Theorem test_corr3:
  {< (_: unit),
  PRE     emp
  POST:r  emp
  CRASH:r emp
  >} nop >> nop.
Proof.
  intros.
  unfold forall_helper; intros.
  exists emp; intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  apply nop_ok.
  apply nop_ok.
  cancel.
  step.

  (* Be careful about [pimpl_crash] thinking our [crash_xform p =p=> p] is
   * actually [.. =p=> crash] and matching up with it..
   *)
  rewrite sep_star_comm. apply star_emp_pimpl.

  cancel.
  step.

  cancel.
Qed.

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
          exists m', (MEMLOG.log_intact xp m' \/ MEMLOG.log_intact_either xp mbase m') *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]])%pred; intros.

  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply log_inc_two_ok.
  eapply MEMLOG.recover_ok.
  cancel.
  step.
  fold (@sep_star valuset); auto. (* fixed in 8b9ec1fe *)
  unfold MEMLOG.would_recover_either.
  autorewrite with crash_xform.
  cancel.
  autorewrite with crash_xform.
  instantiate (a1 := crash_xform p).
  cancel.
  apply pimpl_or_r; left; cancel.
  step.
  rewrite sep_star_or_distr.
  apply pimpl_or_r; left; cancel.
  cancel.
  rewrite H3; cancel.
  apply pimpl_or_r; left; cancel.
  fold (@sep_star valuset); auto.
  rewrite H3; cancel.
  apply pimpl_or_r; left; cancel.
  apply pimpl_or_r; left; cancel.
  apply pimpl_or_r; left; cancel.
  (* XXX this seems like a theorem that MemLog should provide *)
  admit.

  rewrite H3.
  autorewrite with crash_xform.
  (* missing morphisms somewhere.. *)
  admit.

  step.
  instantiate (p:=p); cancel.
  apply pimpl_or_r; left; cancel.

  cancel; apply pimpl_or_r; left; cancel.

  fold (@sep_star valuset).
  cancel.
  cancel.
  cancel.
  (* XXX this seems like a theorem that MemLog should provide *)
  apply pimpl_or_r; left.
  admit.
Qed.
