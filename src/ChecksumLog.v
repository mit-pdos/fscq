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

Definition rep a b : @pred addr (@weq addrlen) valuset :=
  (block1 |-> (a, nil) *
   block2 |-> (b, nil) *
   hash_block |-> (hash2 a b, nil) )%pred.

Definition crep a b a' b' : @pred addr (@weq addrlen) valuset :=
  (block1 |->? *
   block2 |->? *
   (hash_block |-> (hash2 a b, nil) \/
    hash_block |-> (hash2 a' b', hash2 a b :: nil) \/
    hash_block |-> (hash2 a' b', nil)) )%pred.


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
    rep d1_old d2_old
  POST RET:cs
    rep d1 d2
  CRASH
    exists cs', BUFCACHE.rep cs' d *
    crep d1_old d2_old d1 d2
  >} put cs d1 d2.

Theorem get_ok : forall cs,
  {< d d1 d2,
  PRE
    BUFCACHE.rep cs d *
    rep d1 d2
  POST RET:^(d1', d2')
    [[ d1 = d1' /\ d2 = d2' ]]
  CRASH
    BUFCACHE.rep cs d
  >} get cs.

Theorem recover_ok : forall cs,
  {< d d1_old d2_old d1 d2,
  PRE
    BUFCACHE.rep cs d *
    crash_xform (crep d1_old d2_old d1 d2)
  POST RET:cs
    rep d1_old d2_old \/
    rep d1 d2 \/
    rep default_valu default_valu
  CRASH
    crep d1_old d2_old d1 d2
  >} recover cs.
