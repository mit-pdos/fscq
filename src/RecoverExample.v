Require Import AsyncDisk.
Require Import Prog.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Word.
Require Import Idempotent.
Require Import SepAuto.
Require Import Lock.

Set Implicit Arguments.

Parameter work : forall {T} (rx : unit -> prog T), prog T.
Parameter recover : forall {T} (rx : unit -> prog T), prog T.
Parameter rep : bool -> nat -> hashmap -> rawpred.
Axiom rep_xform : forall b n hm, crash_xform (rep b n hm) =p=> rep b n hm.

Theorem work_ok :
  {< v,
  PRE:hm          rep true v hm
  POST:hm' RET:r  rep true (v+1) hm'
  CRASH:hm'       rep true v hm' \/ rep false (v+1) hm' \/ rep true (v+1) hm'
  >} work.
Admitted.

Theorem recover_ok :
  {< v x,
  PRE:hm          rep x v hm
  POST:hm' RET:r  rep true v hm'
  CRASH:hm'       rep x v hm'
  >} recover.
Admitted.

Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.
Hint Extern 1 ({{_}} progseq work _) => apply work_ok : prog.
Hint Extern 1 ({{_}} progseq recover _) => apply recover_ok : prog.

Lemma instantiate_crash : forall idemcrash (F_ : rawpred) (hm_crash : hashmap),
  (fun hm => F_ * idemcrash hm) hm_crash =p=> F_ * idemcrash hm_crash.
Proof.
  reflexivity.
Qed.

Theorem work_recover_ok :
  {X<< v,
  PRE:hm          rep true v hm
  POST:hm' RET:r  rep true (v+1) hm'
  REC:hm' RET:r   rep true v hm' \/ rep true (v+1) hm'
  >>X} work >> recover.
Proof.
  unfold forall_helper; intros.

  (* Idempotence theorem *)
  eapply pimpl_ok3.
  eapply corr3_from_corr2_rx; eauto with prog.

  (* Mechanical transformations *)
  intros.
  cancel.

  (* Post condition *)
  step.

  (**
   * Try to cancel out the idemcrash implication.
   * This breaks up the 3 ORs from [work]'s crash condition.
   * Note that [cancel] tries to unify the first OR branch with [idemcrash], which is wrong;
   * to avoid this, hide the fact that [idemcrash] is an evar using [set_evars].
   *)
  set_evars.
  assert (exists idemcrash', idemcrash' = H) as Hidem by eauto.
  destruct Hidem as [idemcrash' Hidem]. rewrite <- Hidem. subst H.
  rewrite <- locked_eq in Hidem.
  cancel.

  (**
   * Now we have a bunch of subgoals about idemcrash; re-combine the ORs back together..
   * Need to first unlock the idemcrash evar to make progress.
   *)
  rewrite locked_eq.
  apply pimpl_or_r. left. reflexivity.

  rewrite locked_eq.
  or_r. apply pimpl_or_r. left. reflexivity.

  rewrite locked_eq.
  or_r. or_r. reflexivity.

  (* Now we need to prove idempotence..  [xform_norm] breaks up the 3 ORs from idemcrash *)
  simpl.
  xform_norm.

  (* Prove each of the 3 idempotence subgoals *)
  all: rewrite H3.
  all: rewrite rep_xform.
  all: repeat ( cancel || step ).
Qed.
