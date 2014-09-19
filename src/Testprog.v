Require Import Prog.
Require Import Log.
Require Import Word.

Definition copy_block xp (a b : addr) (rx : prog) : prog :=
  v <- LOG.read xp a;
  ok <- LOG.write xp b v;
  rx.

Fixpoint copy_many xp (count : nat) (src dst : addr) rx :=
  match count with
  | O => rx tt
  | S c => copy_block xp (src ^+ (natToWord addrlen c)) (dst ^+ (natToWord addrlen c))
           (copy_many xp c src dst rx)
  end.

Definition testcopy xp rx :=
  LOG.init xp ;;
  LOG.begin xp ;;
  copy_many xp 200 (natToWord addrlen 100) (natToWord addrlen 500) ;;
  LOG.commit xp ;;
  rx.
