Require Import AsyncDisk.
Require Import Prog.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Word.
Require Import Idempotent.
Require Import SepAuto.

Set Implicit Arguments.

Parameter work : forall {T} (rx : unit -> prog T), prog T.
Parameter recover : forall {T} (rx : unit -> prog T), prog T.
Parameter rep : bool -> nat -> rawpred.
Axiom rep_xform : forall b n, crash_xform (rep b n) =p=> rep b n.

Theorem work_ok :
  {< v,
  PRE         rep true v
  POST RET:r  rep true (v+1)
  CRASH       rep true v \/ rep false (v+1) \/ rep true (v+1)
  >} work.
Admitted.

Theorem recover_ok :
  {< v x,
  PRE         rep x v
  POST RET:r  rep true v
  CRASH       rep x v
  >} recover.
Admitted.

Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.
Hint Extern 1 ({{_}} progseq work _) => apply work_ok : prog.
Hint Extern 1 ({{_}} progseq recover _) => apply recover_ok : prog.

Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
  (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.
Proof.
  reflexivity.
Qed.

Theorem work_recover_ok :
  {<< v,
  PRE         rep true v
  POST RET:r  rep true (v+1)
  REC RET:r   rep true v \/ rep true (v+1)
  >>} work >> recover.
Proof.
  unfold forall_helper; intros.
  eexists; intros.

  (* Idempotence theorem *)
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.

  (* Mechanical transformations *)
  intros.
  cancel.

  (* Post condition *)
  step.

  (* [crash] should be basically the same as [idemcrash], modulo the frame *)
  apply instantiate_crash.

  (* Try to cancel out the idemcrash implication; breaks up the 3 ORs from [work]'s crash condition *)
  cancel.

  (* Now we have a bunch of subgoals about idemcrash; re-combine the ORs back together.. *)
  apply pimpl_or_r. left. reflexivity.
  simpl. or_r. apply pimpl_or_r. left. reflexivity.
  simpl. or_r. or_r. reflexivity.

  (* Now we need to prove idempotence..  [xform_norm] breaks up the 3 ORs from idemcrash *)
  simpl.
  xform_norm.

  (* Prove each of the 3 idempotence subgoals *)
  all: rewrite H3.
  all: rewrite rep_xform.
  all: repeat ( cancel || step ).
Qed.
