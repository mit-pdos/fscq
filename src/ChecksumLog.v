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

(* Example "log" using checksums *)

Definition apply T xp (cs : cachestate) rx : prog T :=
  (* apply log to disk *)
  let^ (cs, v) <- BUFCACHE.read (LogData xp) cs;
  cs <- BUFCACHE.write (DataStart xp) v cs;
  cs <- BUFCACHE.sync (DataStart xp) cs;
  rx cs.


Definition write T xp (mscs : memstate_cachestate) v rx : prog T :=
  let '^(ms, cs) := mscs in
  (* write log to disk *)
  cs <- BUFCACHE.write (LogData xp) v cs;
  cs <- BUFCACHE.sync (LogData xp) cs;
  (* write hash to commit block *)
  h <- Hash v;
  cs <- BUFCACHE.write (LogHeader xp) (hash_to_valu h) cs;
  cs <- BUFCACHE.sync (LogHeader xp) cs;

  cs <- apply xp cs;
  rx ^(^(ms, cs), true).

Definition recover T (xp: log_xparams) cs rx : prog T :=
  let^ (cs, v) <- BUFCACHE.read (LogData xp) cs;
  let^ (cs, diskh) <- BUFCACHE.read (LogHeader xp) cs;
  h <- Hash v;
  If (weq diskh (hash_to_valu h)) {
    (* If the log's checksum is okay, apply the changes. *)
    cs <- apply xp cs;
    rx true
  } else {
    rx true
  }.