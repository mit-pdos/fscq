Require Import Prog.
Require Import MemLog.
Require Import Word.
Require Import Balloc.

Set Implicit Arguments.


Definition copy_block T xp (a b : addr) ms rx : prog T :=
  v <- MEMLOG.read xp a ms;
  ms' <- MEMLOG.write xp b v ms;
  rx ms'.

Fixpoint copy_many T xp (count : nat) (src dst : addr) ms rx : prog T :=
  match count with
  | O =>
    rx ms
  | S c =>
    ms' <- copy_block xp (src ^+ $ c) (dst ^+ $ c) ms;
    copy_many T xp c src dst ms' rx
  end.

Definition testcopy T xp rx : prog T :=
  MEMLOG.init xp ;;
  ms <- MEMLOG.begin xp ;
  ms' <- copy_many xp 200 $100 $500 ms ;
  ok <- MEMLOG.commit xp ms' ;
  rx ok.

Definition testalloc T lxp bxp rx : prog T :=
  MEMLOG.init lxp ;;
  ms <- MEMLOG.begin lxp ;
  b_ms' <- BALLOC.alloc lxp bxp ms ;
  let (b, ms') := b_ms' in
  match b with
  | None =>
    MEMLOG.abort lxp ms' ;;
    rx None
  | Some bn =>
    ms'' <- MEMLOG.write lxp $0 (addr2valu bn) ms' ;
    ok <- MEMLOG.commit lxp ms'' ;
    rx (Some bn)
  end.
