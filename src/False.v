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

Theorem noop_rx : forall T a (rx: _ -> prog T),
  noop a rx = rx true \/
  noop a rx = rx false.
Proof.
  intros.
  unfold noop, If_.
  destruct (le_dec a 10); intuition.
Qed.

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

Definition continue {T} rx : prog T :=
  rx tt.

Theorem continue_ok :
  {< (_:unit),
  PRE [[ True ]]
  POST RET:r [[ r = tt ]]
  CRASH [[ False ]]
  >} continue.
Proof.
  unfold continue; intros.
  unfold corr2 at 1; intros.
  unfold exis in H; repeat deex.
  repeat (apply sep_star_lift2and in H; destruct H).
  unfold lift in *.
  eapply H2; eauto.
  pred_apply; cancel.
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

















