Require Import Arith.
Require Import Bool.
Require Import Pred PredCrash.
Require Import Prog.
Require Import Hoare.
Require Import BasicProg.
Require Import Omega.
Require Import SepAuto.
Require Import Idempotent.


Definition noop {T} a rx : prog T :=
  If (le_dec a 10) {
    rx true
  } else {
    rx false
  }.

Theorem noop_ok: forall a,
  {< (_ : unit),
  PRE         [[ True ]]
  POST RET:r  [[ r = false ]] \/ [[ r = true  ]]
  CRASH       [[ False ]]
  >} noop a.
Proof.
  unfold noop.
  hoare.
Qed.


Definition rec {T} rx : prog T :=
  rx true.

Theorem rec_ok :
  {< (_ : unit),
  PRE        [[ True ]]
  POST RET:r [[ True ]]
  CRASH      [[ True ]]
  >} rec.
Proof.
  unfold rec.
  hoare.
Qed.


Definition absurd {T} a rx : prog T :=
  r <- noop a;
  rx false.


Theorem absurd_ok: forall a,
  {<< (_ : unit),
  PRE         [[ True ]]
  POST RET:r  [[ True ]]
  REC RET:r   [[ r = true ]]
  >>} absurd a >> rec.
Proof.
  unfold absurd.
  unfold forall_helper; intros; eexists; intros.
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx.
  apply noop_ok.
  apply rec_ok.
  intros; cancel.
  step.
  step.
  rewrite crash_xform_sep_star_dist.
  instantiate (1 := [[ False ]]%pred).
  rewrite crash_xform_lift_empty.
  cancel.
  Unshelve. exact tt.
Qed.

















