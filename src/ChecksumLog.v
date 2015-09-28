Require Import Prog.
Require Import Word.
Require Import FSLayout.
Require Import Log.
Require Import BasicProg.
Require Import Compare.
Require Import Cache.
Require Import Pred.
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
  d1 <- BUFCACHE.read block1 cs;
  d2 <- BUFCACHE.read block2 cs;
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