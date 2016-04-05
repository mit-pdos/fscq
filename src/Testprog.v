Require Import Prog.
Require Import Log.
Require Import Word.
Require Import Balloc.
Require Import BFile.
Require Import BasicProg.
Require Import Pred.
Require Import FSLayout.
Require Import Cache.
Require Import AsyncDisk.

Set Implicit Arguments.


Definition copy_block T xp (a b : addr) mscs rx : prog T :=
  let^ (mscs, v) <- LOG.read xp a mscs;
  mscs <- LOG.write xp b v mscs;
  rx mscs.

Fixpoint copy_many T xp (count : nat) (src dst : addr) mscs rx : prog T :=
  match count with
  | O =>
    rx mscs
  | S c =>
    mscs <- copy_block xp (src + c) (dst + c) mscs;
    copy_many T xp c src dst mscs rx
  end.

(*
Definition testcopy T xp rx : prog T :=
  cs <- BUFCACHE.init 1000 ;
  mscs <- LOG.init xp cs ;
  mscs <- LOG.begin xp mscs ;
  mscs <- copy_many xp 200 $100 $500 mscs ;
  let^ (mscs, ok) <- LOG.commit xp mscs ;
  rx ok.

Definition testalloc T lxp bxp rx : prog T :=
  cs <- BUFCACHE.init 1000 ;
  mscs <- LOG.init lxp cs ;
  mscs <- LOG.begin lxp mscs ;
  let^ (mscs, b) <- BALLOC.alloc lxp bxp mscs ;
  match b with
  | None =>
    mscs <- LOG.abort lxp mscs ;
    rx None
  | Some bn =>
    mscs <- LOG.write lxp $0 (addr2valu bn) mscs ;
    let^ (mscs, ok) <- LOG.commit lxp mscs ;
    rx (Some bn)
  end.
*)

Definition test_bfile T fsxp v mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs ;
  let^ (mscs, ok) <- BFILE.grow (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) 3 $0 mscs ;
  match ok with
  | false =>
    mscs <- LOG.abort (FSXPLog fsxp) mscs ;
    rx ^(mscs, None)
  | true =>
    mscs <- BFILE.write (FSXPLog fsxp) (FSXPInode fsxp) 3 0 v mscs ;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs ;
    match ok with
    | false => rx ^(mscs, None)
    | true =>
      mscs <- LOG.begin (FSXPLog fsxp) mscs ;
      let^ (mscs, b) <- BFILE.read (FSXPLog fsxp) (FSXPInode fsxp) 3 0 mscs ;
      mscs <- BFILE.shrink (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) 3 1 mscs ;
      let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs ;
      match ok with
      | false => rx ^(mscs, None)
      | true => rx ^(mscs, Some b)
      end
    end
  end.

Definition test_bfile_bulkwrite T fsxp v nblocks mscs rx : prog T :=
  mscs <- LOG.begin (FSXPLog fsxp) mscs;
  let^ (mscs) <- ForN block < nblocks
    Ghost [ (_:unit) ]
    Loopvar [ mscs ]
    Continuation lrx
    Invariant emp
    OnCrash emp
    Begin
      mscs <- BFILE.write (FSXPLog fsxp) (FSXPInode fsxp) 3 block v mscs;
      lrx ^(mscs)
  Rof ^(mscs);
  let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
  rx ^(mscs, ok).

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
