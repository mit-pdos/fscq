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
Require Import FSLayout.

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
  POST RET:r
         s0 |~> (v0 ^+ $1) * s1 |~> (v1 ^+ $1)
  CRASH  s0 |~> v0 * s1 |~> v1 \/
         s0 |~> (v0 ^+ $1) * s1 |~> v1 \/
         s0 |~> (v0 ^+ $1) * s1 |~> (v1 ^+ $1)
  >} inc_two s0 s1.
Proof.
  unfold inc_two.
  hoare.
Qed.

Definition log_inc_two_body T xp s0 s1 mscs rx : prog T :=
  let^ (mscs, v0) <- MEMLOG.read xp s0 mscs;
  mscs <- MEMLOG.write xp s0 (v0 ^+ $1) mscs;
  let^ (mscs, v1) <- MEMLOG.read xp s1 mscs;
  mscs <- MEMLOG.write xp s1 (v1 ^+ $1) mscs;
  rx mscs.

Theorem log_inc_two_body_ok: forall xp s0 s1 mscs,
  {< mbase m v0 v1 F Fm,
  PRE             MEMLOG.rep xp Fm (ActiveTxn mbase m) mscs * 
                  [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem m)]]
  POST RET:mscs   exists m', MEMLOG.rep xp Fm (ActiveTxn mbase m') mscs *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH           MEMLOG.would_recover_old xp Fm mbase
  >} log_inc_two_body xp s0 s1 mscs.
Proof.
  unfold log_inc_two_body.
  hoare_unfold MEMLOG.log_intact_unfold.
Qed.

Hint Extern 1 ({{_}} progseq (log_inc_two_body _ _ _ _) _) => apply log_inc_two_body_ok : prog.

Definition log_inc_two T xp s0 s1 cs rx : prog T :=
  mscs <- MEMLOG.begin xp cs;
  mscs <- log_inc_two_body xp s0 s1 mscs;
  let^ (mscs, ok) <- MEMLOG.commit xp mscs;
  If (bool_dec ok true) {
    rx ^(mscs, ok)
  } else {
    rx ^(mscs, false)
  }.

Theorem log_inc_two_ok: forall xp s0 s1 mscs,
  {< mbase v0 v1 F Fm,
  PRE             MEMLOG.rep xp Fm (NoTransaction mbase) mscs * 
                  [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST RET:^(mscs, r)
                  [[ r = false ]] * MEMLOG.rep xp Fm (NoTransaction mbase) mscs \/
                  [[ r = true ]] * exists m', MEMLOG.rep xp Fm (NoTransaction m') mscs *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  CRASH           MEMLOG.would_recover_old xp Fm mbase \/
                  exists m', MEMLOG.would_recover_either xp Fm mbase m' *
                  [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]]
  >} log_inc_two xp s0 s1 mscs.
Proof.
  unfold log_inc_two.
  hoare_unfold MEMLOG.log_intact_unfold.
Qed.

Hint Extern 1 ({{_}} progseq (log_inc_two _ _ _ _) _) => apply log_inc_two_ok : prog.

Hint Rewrite crash_xform_sep_star_dist crash_xform_or_dist crash_xform_exists_comm : crash_xform.

Definition i2 xp s0 s1 T := @log_inc_two T xp s0 s1.

Theorem log_inc_two_recover_ok: forall xp s0 s1 mscs,
  {<<< v0 v1 F Fm mbase,
  PRE
    MEMLOG.rep xp Fm (NoTransaction mbase) mscs *
    [[ (s0 |-> v0 * s1 |-> v1 * F)%pred (list2mem mbase)]]
  POST RET:rr
    exists mscs,
   ([[ rr = OK ^(mscs, false) \/ rr = Recover mscs ]] * MEMLOG.rep xp Fm (NoTransaction mbase) mscs \/
    exists m',
    [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F)%pred (list2mem m') ]] *
    [[ rr = OK ^(mscs, true) \/ rr = Recover mscs ]] * MEMLOG.rep xp Fm (NoTransaction m') mscs)
  >>>} log_inc_two xp s0 s1 mscs >> MEMLOG.recover xp (fst (snd mscs)).
Proof.
  intros.
  unfold forall_helper at 1 2; intros v0 v1 F.
  eapply (MEMLOG.recover_corr2_to_corr3 (i2 xp s0 s1)).
  unfold i2.
  intros.
  eapply pimpl_ok2.
  eapply log_inc_two_ok.
  cancel.
Qed.
