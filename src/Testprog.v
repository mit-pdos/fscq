Require Import Prog.
Require Import MemLog.
Require Import Word.
Require Import Balloc.
Require Import BFile.
Require Import BasicProg.
Require Import Pred.
Require Import FSLayout.
Require Import Cache.

Set Implicit Arguments.


Definition copy_block T xp (a b : addr) mscs rx : prog T :=
  let2 (mscs, v) <- MEMLOG.read xp a mscs;
  mscs <- MEMLOG.write xp b v mscs;
  rx mscs.

Fixpoint copy_many T xp (count : nat) (src dst : addr) mscs rx : prog T :=
  match count with
  | O =>
    rx mscs
  | S c =>
    mscs <- copy_block xp (src ^+ $ c) (dst ^+ $ c) mscs;
    copy_many T xp c src dst mscs rx
  end.

Definition testcopy T xp rx : prog T :=
  cs <- BUFCACHE.init $1000 ;
  mscs <- MEMLOG.init xp cs ;
  mscs <- MEMLOG.begin xp mscs ;
  mscs <- copy_many xp 200 $100 $500 mscs ;
  let2 (mscs, ok) <- MEMLOG.commit xp mscs ;
  rx ok.

Definition testalloc T lxp bxp rx : prog T :=
  cs <- BUFCACHE.init $1000 ;
  mscs <- MEMLOG.init lxp cs ;
  mscs <- MEMLOG.begin lxp mscs ;
  let2 (mscs, b) <- BALLOC.alloc lxp bxp mscs ;
  match b with
  | None =>
    mscs <- MEMLOG.abort lxp mscs ;
    rx None
  | Some bn =>
    mscs <- MEMLOG.write lxp $0 (addr2valu bn) mscs ;
    let2 (mscs, ok) <- MEMLOG.commit lxp mscs ;
    rx (Some bn)
  end.

Definition test_bfile T fsxp v mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs ;
  let2 (mscs, ok) <- BFILE.bfgrow (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) $3 mscs ;
  match ok with
  | false =>
    mscs <- MEMLOG.abort (FSXPMemLog fsxp) mscs ;
    rx (mscs, None)
  | true =>
    mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) $3 $0 v mscs ;
    let2 (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs ;

    match ok with
    | false => rx (mscs, None)
    | true =>
      mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs ;
      let2 (mscs, b) <- BFILE.bfread (FSXPMemLog fsxp) (FSXPInode fsxp) $3 $0 mscs ;
      mscs <- BFILE.bfshrink (FSXPMemLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) $3 mscs ;
      let2 (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs ;
      match ok with
      | false => rx (mscs, None)
      | true => rx (mscs, Some b)
      end
    end
  end.

Definition test_bfile_bulkwrite T fsxp v nblocks mscs rx : prog T :=
  mscs <- MEMLOG.begin (FSXPMemLog fsxp) mscs;
  mscs <- For block < nblocks
    Loopvar mscs <- mscs
    Continuation lrx
    Invariant emp
    OnCrash emp
    Begin
      mscs <- BFILE.bfwrite (FSXPMemLog fsxp) (FSXPInode fsxp) $3 block v mscs;
      lrx mscs
  Rof;
  let2 (mscs, ok) <- MEMLOG.commit (FSXPMemLog fsxp) mscs;
  rx (mscs, ok).

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
