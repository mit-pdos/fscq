Require Import Prog.
Require Import Word.
Require Import FSLayout.
Require Import Log.
Require Import BasicProg.
Require Import Compare.
Require Import Cache.
Require Import Pred.
Require Import PredCrash.
Require Import Hoare.
Require Import Mem.
Require Import GenSep.
Require Import SepAuto.
Require Import List.
Require Import Array.
Require Import EqdepFacts.

Set Implicit Arguments.

Definition block1 : addr := $0.
Definition block2 : addr := $1.
Definition default_valu : valu := $0.
Definition hash_block : addr := $2.


Definition hash2 (a b : word valulen) := hash_to_valu (hash_fwd (Word.combine a b)).

Definition rep a b (d : @mem addr (@weq addrlen) valuset) :
    @pred addr (@weq addrlen) valuset :=
  [[ (block1 |-> (a, nil) *
   block2 |-> (b, nil) *
   hash_block |-> (hash2 a b, nil))%pred d ]] *
  [[ hash_inv (hash_fwd (Word.combine a b)) = existT _ _ (Word.combine a b) ]].

Definition hash_crep a b l :
    @pred addr (@weq addrlen) valuset :=
  (block1 |->? *
   block2 |->? *
   hash_block |-> (hash2 a b, l)) *
  [[ hash_inv (hash_fwd (Word.combine a b)) = existT _ _ (Word.combine a b) ]]%pred.

Definition crep a b a' b' :
    @pred addr (@weq addrlen) valuset :=
  (hash_crep a b nil \/
  hash_crep a' b' (hash2 a b :: nil) \/
  hash_crep a' b' nil).

(*
   (hash_block |-> (hash2 a b, nil) \/
    hash_block |-> (hash2 a' b', hash2 a b :: nil) \/
    hash_block |-> (hash2 a' b', nil)) )%pred d ]] *
  [[ exists a b, hash_block |-> ((hash2 a b), nil) /\
hash_inv (hash_fwd (Word.combine a b)) = existT _ _ (Word.combine a b) ]]. *)


(* Example "log" implementation using checksums *)

Definition put T cs d1 d2 rx : prog T :=
  cs <- BUFCACHE.write block1 d1 cs;
  cs <- BUFCACHE.write block2 d2 cs;
  h <- Hash (Word.combine d1 d2);
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
  h <- Hash (Word.combine d1 d2);
  If (weq diskh (hash_to_valu h)) {
    rx cs
  } else {
    cs <- put cs default_valu default_valu;
    rx cs
  }.


Theorem put_ok : forall cs d1 d2,
  {< d d1_old d2_old,
  PRE
    BUFCACHE.rep cs d
  POST RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      rep d1 d2 d'
  CRASH
    exists cs' d',
      BUFCACHE.rep cs' d' *
      [[ (crep d1_old d2_old d1 d2)%pred d' ]]
  >} put cs d1 d2.
Proof.
  unfold put, rep, crep, hash_crep.
  step.

  step.
  step.
  step.
  step.
  step.
  step.
  step.
  all: try (unfold hash2; cancel).

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
  unfold get, rep.
  step.
  step.
  step.
Qed.

(* block1 and block2 get some value, and hash_block points to a valid hash of  *)
Definition after_crash_pred v1 v2 :
    @pred addr (@weq addrlen) valuset :=
  (exists a b, 
      block1 |-> (a, nil) *
      block2 |-> (b, nil) *
      hash_block |-> (hash2 v1 v2, nil) *
    [[ hash_inv (hash_fwd (Word.combine v1 v2)) = existT _ _ (Word.combine v1 v2) ]])%pred.

Lemma crash_xform_would_recover_either_pred : forall v1 v2 v1' v2',
  crash_xform (crep v1 v2 v1' v2') =p=>
    after_crash_pred v1 v2 \/
    after_crash_pred v1' v2'.
Proof.
Admitted.

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

  (* apply crash_xform_sep_star_dist in H4.*)
  assert (Hafter_crash: (after_crash_pred d1_old d2_old)%pred d \/
    (after_crash_pred d1 d2)%pred d).
    apply crash_xform_would_recover_either_pred.
    auto.

  unfold after_crash_pred in Hafter_crash.
  destruct Hafter_crash; destruct_lift H.

  - cancel.
    step.
    step.
    step.
    step.
    step.
    unfold hash2 in *.
    apply hash_to_valu_inj in H8.
    assert (Hheq: d1_old = a /\ d2_old = b).
      rewrite H8 in H5.
      rewrite H5 in H11.
      pose proof (eq_sigT_snd H11).
      autorewrite with core in *.
      apply combine_inj in H0.
      auto.
    cancel.

    step.
    step.
    unfold rep. cancel.
    cancel.
    all: cancel; try (unfold crep, hash_crep; instantiate (1:=d); cancel).


Admitted.
