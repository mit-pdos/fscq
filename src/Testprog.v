Require Import Prog.
Require Import Log.
Require Import Word.
Require Import Balloc.

Definition copy_block xp (a b : addr) (rx : prog) : prog :=
  v <- LOG.read xp a;
  ok <- LOG.write xp b v;
  rx.

Fixpoint copy_many xp (count : nat) (src dst : addr) rx :=
  match count with
  | O => rx tt
  | S c => copy_block xp (src ^+ $ c) (dst ^+ $ c)
           (copy_many xp c src dst rx)
  end.

Definition testcopy xp rx :=
  LOG.init xp ;;
  LOG.begin xp ;;
  copy_many xp 200 $100 $500 ;;
  LOG.commit xp ;;
  rx.

Definition testalloc lxp bxp rx :=
  LOG.init lxp ;;
  LOG.begin lxp ;;
  b <- BALLOC.alloc lxp bxp ;
  match b with
  | None =>
    LOG.abort lxp ;;
    rx
  | Some bn =>
    ok <- LOG.write lxp $0 (LOG.addr2valu bn) ;
    LOG.commit lxp ;;
    rx
  end.
