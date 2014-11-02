Require Import Prog.
Require Import Log.
Require Import Word.
Require Import Balloc.

Set Implicit Arguments.


Definition copy_block T xp (a b : addr) rx : prog T :=
  v <- LOG.read xp a;
  ok <- LOG.write xp b v;
  rx.

Fixpoint copy_many T xp (count : nat) (src dst : addr) rx : prog T :=
  match count with
  | O => rx tt
  | S c => copy_block xp (src ^+ $ c) (dst ^+ $ c)
           (copy_many T xp c src dst rx)
  end.

Definition testcopy T xp rx : prog T :=
  LOG.init xp ;;
  LOG.begin xp ;;
  copy_many xp 200 $100 $500 ;;
  LOG.commit xp ;;
  rx.

Definition testalloc T lxp bxp rx : prog T :=
  LOG.init lxp ;;
  LOG.begin lxp ;;
  b <- BALLOC.alloc lxp bxp ;
  match b with
  | None =>
    LOG.abort lxp ;;
    rx None
  | Some bn =>
    ok <- LOG.write lxp $0 (addr2valu bn) ;
    LOG.commit lxp ;;
    rx (Some bn)
  end.
