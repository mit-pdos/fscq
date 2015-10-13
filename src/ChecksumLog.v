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
   hash_block |-> (hash2 a b, nil) )%pred d ]].

Definition crep a b a' b' (d : @mem addr (@weq addrlen) valuset) :
    @pred addr (@weq addrlen) valuset :=
  [[ (block1 |->? *
   block2 |->? *
   (hash_block |-> (hash2 a b, nil) \/
    hash_block |-> (hash2 a' b', hash2 a b :: nil) \/
    hash_block |-> (hash2 a' b', nil)) )%pred d ]].


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
    BUFCACHE.rep cs d *
    rep d1_old d2_old d
  POST RET:cs'
    exists d',
      BUFCACHE.rep cs' d' *
      rep d1 d2 d'
  CRASH
    exists cs' d',
      BUFCACHE.rep cs' d' *
      crep d1_old d2_old d1 d2 d'
  >} put cs d1 d2.
Proof.
  unfold put, rep, crep.
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


Theorem recover_ok : forall cs,
  {< d d1_old d2_old d1 d2,
  PRE
    BUFCACHE.rep cs d *
    [[ crash_xform (crep d1_old d2_old d1 d2 d)%pred d ]]
  POST RET:cs
    exists d',
      rep d1_old d2_old d' \/
      rep d1 d2 d' \/
      rep default_valu default_valu d'
  CRASH
    exists d', crep d1_old d2_old d1 d2 d'
  >} recover cs.
Proof.
Admitted.