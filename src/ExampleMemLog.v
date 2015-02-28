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
  PRE    s0 |~> v0 * s1 |~> v1
  POST:r s0 |~> (v0 ^+ $1) * s1 |~> (v1 ^+ $1)
  CRASH  s0 |~> v0 * s1 |~> v1 \/
         s0 |~> (v0 ^+ $1) * s1 |~> v1 \/
         s0 |~> (v0 ^+ $1) * s1 |~> (v1 ^+ $1)
  >} inc_two s0 s1.
Proof.
  unfold inc_two.
  hoare.
Qed.


Definition log_inc_two T xp s0 s1 cs rx : prog T :=
  mscs <- MEMLOG.begin xp cs;
  let2 (mscs, v0) <- MEMLOG.read xp s0 mscs;
  mscs <- MEMLOG.write xp s0 (v0 ^+ $1) mscs;
  let2 (mscs, v1) <- MEMLOG.read xp s1 mscs;
  mscs <- MEMLOG.write xp s1 (v1 ^+ $1) mscs;
  let2 (mscs, ok) <- MEMLOG.commit xp mscs;
  If (bool_dec ok true) {
    rx (mscs, ok)
  } else {
    rx (mscs, false)
  }.

Theorem log_inc_two_ok: forall xp s0 s1 cs,
  {< mbase v0 v1 F,
  PRE             MEMLOG.rep xp (NoTransaction mbase) (ms_empty, cs) * 
                  [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST:(mscs', r) [[ r = false ]] * MEMLOG.rep xp (NoTransaction mbase) mscs' \/
                  [[ r = true ]] * exists m', MEMLOG.rep xp (NoTransaction m') mscs' *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH           MEMLOG.would_recover_old xp mbase \/
                  exists m', MEMLOG.might_recover_cur xp mbase m' *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  >} log_inc_two xp s0 s1 cs.
Proof.
  unfold log_inc_two.
  hoare_unfold MEMLOG.log_intact_unfold.
Qed.

Hint Extern 1 ({{_}} log_inc_two _ _ _ _ _) => apply log_inc_two_ok : prog.

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

Theorem log_inc_two_recover_ok: forall xp s0 s1 cs,
  {< mbase v0 v1 F,
  PRE             MEMLOG.rep xp (NoTransaction mbase) (ms_empty, cs) * 
                  [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST:(mscs', r) [[ r = false ]] * MEMLOG.rep xp (NoTransaction mbase) mscs' \/
                  [[ r = true ]] * exists m', MEMLOG.rep xp (NoTransaction m') mscs' *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH:r         exists mscs', MEMLOG.rep xp (NoTransaction mbase) mscs' \/
                  exists m', MEMLOG.rep xp (NoTransaction m') mscs' *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  >} log_inc_two xp s0 s1 cs >> MEMLOG.recover xp.
Proof.
  intros.
  unfold forall_helper; intros mbase v0 v1 F.
  exists (MEMLOG.would_recover_old xp mbase \/
          exists m', (MEMLOG.might_recover_cur xp mbase m') *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]])%pred; intros.

  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eapply log_inc_two_ok.
  eapply MEMLOG.recover_ok.
  cancel.
  step.
  (* XXX it shouldn't be necessary to repeatedly call cancel *)
  cancel.
  cancel.
  auto.
  unfold MEMLOG.would_recover_either.
  autorewrite with crash_xform.
  rewrite sep_star_or_distr.
  apply pimpl_or_l.
  cancel.
  autorewrite with crash_xform.
  rewrite sep_star_or_distr.
  cancel.

  step.
  rewrite sep_star_or_distr.
  apply pimpl_or_r; left; cancel.
  rewrite H3; cancel.
  rewrite H3; cancel.
  apply pimpl_or_r; right; cancel.
  instantiate (a := Array.upd (Array.upd mbase s0 (v0 ^+ $1)) s1 (v1 ^+ $1)).
  admit.
  rewrite H3; cancel.
  apply pimpl_or_r; left; cancel.
  apply pimpl_or_r; right; cancel.
  admit.

  norm'l.
  unfold stars; simpl.
  autorewrite with crash_xform.
  cancel.
  autorewrite with crash_xform.
  rewrite sep_star_or_distr.
  cancel.

  step.
  rewrite H3; cancel.
  apply pimpl_or_r; left; cancel.

  rewrite H3; cancel.
  apply pimpl_or_r; right; cancel.

  rewrite H3.
  rewrite sep_star_or_distr.
  cancel. cancel.
  cancel.
Qed.
