Require Import Prog.
Require Import Word.
Require Import FSLayout.
Require Import Log.
Require Import BasicProg.
Require Import Compare.
Require Import Cache.

Set Implicit Arguments.

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