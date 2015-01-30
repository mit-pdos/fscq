Require Import Prog.
Require Import MemLog.
Require Import Word.
Require Import Balloc.
Require Import BFile.

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

Definition test_bfile T lxp bxp ixp v rx : prog T :=
  MEMLOG.init lxp ;;
  ms <- MEMLOG.begin lxp ;
  r <- BFILE.bfgrow lxp bxp ixp $3 ms ;
  let (ok, ms) := r in
  match ok with
  | false => MEMLOG.abort lxp ms ;; rx None
  | true =>
    ms <- BFILE.bfwrite lxp ixp $3 $0 v ms ;
    b <- BFILE.bfread lxp ixp $3 $0 ms ;
    ms <- BFILE.bfshrink lxp bxp ixp $3 ms ;
    ok <- MEMLOG.commit lxp ms ;
    match ok with
    | false => rx None
    | true => rx (Some b)
    end
  end.

(* Why does this seemingly simple function take forever to compile?? *)
(*
Fixpoint test_bfile_many {T} lxp bxp ixp v n (rx : option valu -> prog T) : prog T :=
  match n with
  | O => rx (Some v)
  | S n' =>
    ov <- test_bfile lxp bxp ixp v ;
    match ov with
    | None => rx None
    | Some v' => test_bfile_many lxp bxp ixp v' n' rx
    end
  end.
*)
