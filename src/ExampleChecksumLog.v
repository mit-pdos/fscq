Require Import Prog.
Require Import BasicProg.
Require Import Word.
Require Import Pred.
Require Import PredCrash.
Require Import Mem.
Require Import Cache.
Require Import List.
Require Import Hoare.
Require Import SepAuto.
Require Import ChecksumLog.

Set Implicit Arguments.


Definition block1 : addr := $0.
Definition block2 : addr := $1.
Definition hash_block : addr := $2.

(* Representations for an example with two log blocks. *)
(* block1 and block2 are synced, hash_block has some valid hash *)
Definition any_hash_rep (a b a' b' : valu) (d : @mem addr (@weq addrlen) valuset) :
    @pred addr (@weq addrlen) valuset :=
  (exists hv,
    [[ (block1 |-> (a, nil) *
     block2 |-> (b, nil) *
     hash_block |-> (hash_to_valu hv, nil))%pred d ]] *
    [[ hash_list_rep (b' :: a' :: nil) hv ]])%pred.

(* hash_block has the valid hash of block1 and block2 values *)
Definition rep a b (d : @mem addr (@weq addrlen) valuset) :
    @pred addr (@weq addrlen) valuset :=
  any_hash_rep a b a b d.

(* After a crash:
  - block1 and block2 can be anything
  - hash_block can be one of:
    - hash of old values
    - hash of new values but unsynced
    - hash of new values and synced *)
Definition crep (a b a' b' : valu) :
    @pred addr (@weq addrlen) valuset :=
  (exists hv hv',
    block1 |->? *
    block2 |->? *
    ( hash_block |-> (hash_to_valu hv, nil) *
        [[ hash_list_rep (b :: a :: nil) hv ]] \/
      hash_block |-> (hash_to_valu hv', hash_to_valu hv :: nil) *
        [[ hash_list_rep (b :: a :: nil) hv /\ hash_list_rep (b' :: a' :: nil) hv' ]] \/
      hash_block |-> (hash_to_valu hv', nil) *
        [[ hash_list_rep (b' :: a' :: nil) hv' ]]))%pred.


(* Example "log" implementation using checksums *)
Definition put T cs d1 d2 rx : prog T :=
  cs <- BUFCACHE.write block1 d1 cs;
  cs <- BUFCACHE.write block2 d2 cs;
  h <- hash_list (d1 :: d2 :: nil);
  cs <- BUFCACHE.write hash_block (hash_to_valu h) cs;
  cs <- BUFCACHE.sync block1 cs;
  cs <- BUFCACHE.sync block2 cs;
  cs <- BUFCACHE.sync hash_block cs;
  rx cs.

Definition get T cs rx : prog T :=
  let^ (cs, d1) <- BUFCACHE.read block1 cs;
  let^ (cs, d2) <- BUFCACHE.read block2 cs;
  rx ^(d1, d2).

Definition recover T cs rx : prog T :=
  let^ (cs, d1) <- BUFCACHE.read block1 cs;
  let^ (cs, d2) <- BUFCACHE.read block2 cs;
  let^ (cs, diskh) <- BUFCACHE.read hash_block cs;
  h <- hash_list (d1 :: d2 :: nil);
  If (weq diskh (hash_to_valu h)) {
    rx cs
  } else {
    cs <- put cs default_valu default_valu;
    rx cs
  }.


Theorem put_ok : forall cs d1 d2,
  {< d d1_old d2_old d1_old' d2_old',
  PRE
    BUFCACHE.rep cs d *
    any_hash_rep d1_old d2_old d1_old' d2_old' d
  POST RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      rep d1 d2 d'
  CRASH
    exists cs' d',
      BUFCACHE.rep cs' d' *
      [[ (crep d1_old' d2_old' d1 d2)%pred d' ]]
  >} put cs d1 d2.
Proof.
  unfold put, rep, any_hash_rep, crep.
  step.
  step.
  step.
  apply goodSize_bound with (bound := 2); auto.
  step.
  step.
  step.
  step.
  step.

  all: cancel.
  Grab Existential Variables.
  all: eauto.
Qed.

Hint Extern 1 ({{_}} progseq (put _ _ _) _) => apply put_ok : prog.


Theorem get_ok : forall cs,
  {< d d1 d2,
  PRE
    BUFCACHE.rep cs d *
    rep d1 d2 d
  POST RET:^(d1', d2')
    exists cs', BUFCACHE.rep cs' d *
    rep d1 d2 d *
    [[ d1 = d1' /\ d2 = d2' ]]
  CRASH
    exists cs', BUFCACHE.rep cs' d *
    rep d1 d2 d
  >} get cs.
Proof.
  unfold get, rep, any_hash_rep.
  step.
  step.
  step.
Qed.

(* block1 and block2 get some value, and hash_block points to a valid hash of  *)
Definition after_crash_pred (v1 v2 : valu) :
    @pred addr (@weq addrlen) valuset :=
  (exists a b hv,
      block1 |-> (a, nil) *
      block2 |-> (b, nil) *
      hash_block |-> (hash_to_valu hv, nil) *
    [[ hash_list_rep (v2 :: v1 :: nil) hv ]])%pred.

Lemma crash_xform_would_recover_either_pred : forall v1 v2 v1' v2',
  crash_xform (crep v1 v2 v1' v2') =p=>
    after_crash_pred v1 v2 \/
    after_crash_pred v1' v2'.
Proof.
  unfold crep, after_crash_pred.
  intros.
  repeat (autorewrite with crash_xform; cancel).
Qed.

Hint Rewrite crash_xform_would_recover_either_pred : crash_xform.


Theorem recover_ok : forall cs,
  {< d1_old d2_old d1 d2,
  PRE
    exists d,
      BUFCACHE.rep cs d *
      [[ crash_xform (crep d1_old d2_old d1 d2)%pred d ]]
  POST RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      (rep d1_old d2_old d' \/
       rep d1 d2 d' \/
       rep default_valu default_valu d')
  CRASH
    exists cs' d',
      (BUFCACHE.rep cs' d' *
       [[ (crep d1_old d2_old default_valu default_valu)%pred d' ]]) \/
      (BUFCACHE.rep cs' d' *
       [[ (crep d1 d2 default_valu default_valu)%pred d' ]])
  >} recover cs.
Proof.
  unfold recover, rep.
  intros.
  eapply pimpl_ok2; eauto with prog.
  intros. norm'l. unfold stars; simpl.

  (* autorewrite with crash_xform doesn't work? *)
  assert (Hafter_crash: (after_crash_pred d1_old d2_old)%pred d \/
    (after_crash_pred d1 d2)%pred d).
    apply crash_xform_would_recover_either_pred.
    auto.

  unfold after_crash_pred in Hafter_crash.
  destruct Hafter_crash;
  destruct_lift H.

  - cancel.
    step.
    step.
    step.
    apply goodSize_bound with (bound := 2); auto.
    step.
    step.
    apply hash_to_valu_inj in H8.
    subst.
    assert (Hheq: d1_old = a /\ d2_old = b).
      eapply hash_list_injective in H5; try apply H10.
      inversion H5. auto.
    unfold any_hash_rep.
    cancel_with eauto.

    step.
    unfold any_hash_rep.
    cancel_with eauto.
    step.
    all: repeat cancel; try (
      unfold crep in *;
      instantiate (1:=d);
      apply pimpl_or_r; left;
      repeat cancel).

  - cancel.
    step.
    step.
    step.
    apply goodSize_bound with (bound := 2); auto.
    step.
    step.
    apply hash_to_valu_inj in H8.
    subst.
    assert (Hheq: d1 = a /\ d2 = b).
      eapply hash_list_injective in H5; try apply H10.
      inversion H5. auto.
    unfold any_hash_rep.
    cancel_with eauto.

    step.
    unfold any_hash_rep.
    cancel_with eauto.
    step.
    all: repeat cancel; try (
      unfold crep in *;
      instantiate (1:=d);
      apply pimpl_or_r; right;
      repeat cancel).

  Grab Existential Variables.
  all: eauto.
Qed.
