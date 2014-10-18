Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import Word.
Require Import SepAuto.
Require Import BasicProg.
Require Import Log.
Require Import Bool.
Require Import Idempotent.


Definition inc_two s0 s1 rx :=
  v0 <- Read s0 ;
  Write s0 (v0 ^+ $1) ;;
  v1 <- Read s1 ;
  Write s1 (v1 ^+ $1) ;;
  rx tt.

Theorem inc_two_ok: forall s0 s1,
  {< v0 v1 F,
  PRE    s0 |-> v0 * s1 |-> v1 * F
  POST:r s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F
  CRASH  s0 |-> v0 * s1 |-> v1 * F \/
         s0 |-> (v0 ^+ $1) * s1 |-> v1 * F \/
         s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F
  >} inc_two s0 s1.
Proof.
  unfold inc_two.
  hoare.
Qed.


Definition log_inc_two xp s0 s1 rx :=
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


Notation "{< e1 .. e2 , 'PRE' pre 'POST' : rp post 'CRASH' : rc crash 'IDEM' idemcrash >} p1 >> p2" :=
  (forall rxOK rxREC, corr3
   (fun done_ crashdone_ =>
    (exis (fun e1 => .. (exis (fun e2 =>
     pre *
     [[ forall r_,
        {{ fun done'_ crash'_ => (fun rp => post) r_ *
                                 [[ done'_ = done_ ]] * [[ crash'_ ==> idemcrash ]]
        }} rxOK r_ ]] *
     [[ forall r_,
        {{ fun done'_ crash'_ => (fun rc => crash) r_ *
                                 [[ done'_ = crashdone_ ]] * [[ crash'_ ==> idemcrash ]]
        }} rxREC r_ ]]
     )) .. ))
   )%pred
   (p1 rxOK)%pred
   (p2 rxREC)%pred)
  (at level 0, p1 at level 60, p2 at level 60, e1 binder, e2 binder, rp at level 0, rc at level 0).


Theorem log_inc_two_ok: forall xp s0 s1,
  {< d F v0 v1 F',
  PRE    LOG.rep xp (NoTransaction d) * F *
         [[ (s0 |-> v0 * s1 |-> v1 * F')%pred d ]]
  POST:r exists d', LOG.rep xp (NoTransaction d') * F *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F')%pred d' ]]
  CRASH  LOG.log_intact xp d F \/
         exists d', LOG.log_intact xp d' F *
         [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F')%pred d' ]]
  >} log_inc_two xp s0 s1.
Proof.
  unfold log_inc_two, LOG.log_intact.
  hoare.
  eexists; pred_apply; cancel.
  pred_apply; cancel.
  eexists; pred_apply; cancel.
  pred_apply; cancel.
  pred_apply; cancel.
  eapply pimpl_trans; [| eapply pimpl_star_emp ].
  eapply pimpl_or_r; right.
  cancel.
  pred_apply; cancel.
  eapply pimpl_trans; [| eapply pimpl_star_emp ].
  eapply pimpl_or_r; right.
  cancel.
  pred_apply; cancel.
  admit.  (* something went wrong with guessing OR branches *)
  eexists; pred_apply; cancel.
  pred_apply; cancel.
  admit.  (* something went wrong with guessing OR branches *)
  admit.  (* something went wrong with guessing OR branches *)
Qed.

Hint Extern 1 ({{_}} log_inc_two _ _ _ _) => apply log_inc_two_ok : prog.

Theorem log_inc_two_recover_ok: forall xp s0 s1,
  {< d F v0 v1 F',
  PRE     LOG.rep xp (NoTransaction d) * F *
          [[ (s0 |-> v0 * s1 |-> v1 * F')%pred d ]]
  POST:r  exists d', LOG.rep xp (NoTransaction d') * F *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F')%pred d' ]]
  CRASH:r LOG.rep xp (NoTransaction d) * F \/
          exists d', LOG.rep xp (NoTransaction d') * F *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F')%pred d' ]]
  IDEM    LOG.log_intact xp d F \/
          exists d', LOG.log_intact xp d' F *
          [[ (s0 |-> (v0 ^+ $1) * s1 |-> (v1 ^+ $1) * F')%pred d' ]]
  >} log_inc_two xp s0 s1 >> LOG.recover xp.
Proof.
  intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2.
  eauto with prog.
  eapply LOG.recover_ok.

  cancel.
  pred_apply; cancel.
  step.
  pred_apply; cancel.
  unfold LOG.log_intact; cancel.
  eapply pimpl_trans; [| eapply pimpl_star_emp ].
  eapply pimpl_or_r; right.
  unfold LOG.log_intact; cancel.
  pred_apply; cancel.
  pred_apply; cancel.
  pred_apply; cancel.
  cancel.
  step.
  unfold LOG.log_intact; cancel.
  eapply pimpl_trans; [| eapply pimpl_star_emp ].
  eapply pimpl_or_r; right.
  unfold LOG.log_intact; cancel.
  pred_apply; cancel.
  pred_apply; cancel.
  pred_apply; cancel.
  cancel.
  step.
  eapply pimpl_trans; [| eapply pimpl_star_emp ].
  eapply pimpl_or_r; right.
  cancel.
  pred_apply; cancel.
  unfold LOG.log_intact; cancel.
  eapply pimpl_trans; [| eapply pimpl_star_emp ].
  eapply pimpl_or_r; right.
  cancel.
  unfold LOG.log_intact; cancel.
  pred_apply; cancel.
  eapply pimpl_or_r; right.
  cancel.
Qed.
