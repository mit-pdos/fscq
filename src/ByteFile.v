Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred.
Require Import DirName.
Require Import Hoare.
Require Import GenSep.
Require Import GenSepN.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
Require Import DirTree.
Require Import Arith.
Require Import Array.
Require Import FSLayout.
Require Import Cache.
Require Import Rec.
Require Import RecArray.
Require Import Omega.

Set Implicit Arguments.
Import ListNotations.

Module BYTEFILE.

  (* XXX some rep relating size in bytes to bflen *)


  Record chunk := {
                   chunk_block : addr;
                   chunk_boff : nat;
                   chunk_bend : nat;
                   chunk_boff_proof : chunk_boff < valulen;
                   chunk_bend_proof : chunk_bend <= valulen
                   }.

  Lemma off_lt_valulen :
    forall off,
      off mod valulen < valulen.
  Proof.
    intros.
    (* apply mod_bound_pos. *)
    admit.
  Admitted.

  Lemma end_lt_valulen :
    forall x,
      Nat.min x valulen <= valulen.
  Proof.
    intros.
    apply Nat.le_min_r.
  Qed.
    
  (* fix point for computing list of byte chunks to write, one entry per block *)
  Fixpoint chunkList (b: nat) (sz:nat) (off:nat) : list chunk :=
    match b with
      | O => nil   (* XXX maybe the last chunk: [(off, sz)] *)
      | S b' =>
        let blk := off / valulen in   (* XXX blk should be addr, very slow! *)
        let boff := off mod valulen in
        let bend := Nat.min (boff + sz) valulen in
        let bsz := bend - boff in
        (@Build_chunk ($ blk) boff bend (off_lt_valulen off) (end_lt_valulen (boff + sz))) :: chunkList b' (sz - bsz) (off+boff)
     end.
  
  Eval compute in chunkList 0 10 10.
  (* Eval compute in chunkList 1 4096 100. *)

  Definition grow_if_needed T fsxp inum b mscs rx : prog T := 
    let^ (mscs, len) <- BFILE.bflen (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    If (wlt_dec len b) {
      let^ (mscs, ok) <- BFILE.bftrunc (FSXPLog fsxp) (FSXPBlockAlloc fsxp) (FSXPInode fsxp) inum (b ^+ $1) mscs;
      If (bool_dec ok true) {
        rx ^(mscs, false)
      } else {
        rx ^(mscs, false)
      }
    } else {
      rx ^(mscs, true)
    }.

  
  Lemma boff_valulen_boff :
    forall boff,
      boff < valulen ->
      boff + (valulen - boff) = valulen.
  Proof.
    intros. omega.
  Qed.

  Definition write_byte T fsxp inum off len (data:word (len*8)) sz mscs rx : prog T :=
    mscs <- LOG.begin (FSXPLog fsxp) mscs;
    mscs <- ForEach ck ckrest (chunkList (((sz-off)/valulen)+1) sz off)
      Ghost [ mbase m F ]
      Loopvar [ mscs lenleft dataleft ]    
      Continuation lrx  
      Invariant
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs
        (* XXX n bytes written, n + remaining = sz *)
      OnCrash
        LOG.would_recover_old fsxp.(FSXPLog) F mbase
      Begin
        let '(b, boff1, bend, boffProof, bendProof) := ck in
        let^ (mscs, ok) <- grow_if_needed fsxp inum b mscs;
        If (bool_dec ok true) {
          let^ (mscs, v) <- BFILE.bfread  (FSXPLog fsxp) (FSXPInode fsxp) inum b mscs;
          let v_boff := (eq_rect valulen word v (boff1+(valulen-boff1)) (@boff_valulen_boff boff1 boffProof)) in
          let x := (split1 (boff1) (valulen - boff1) v_boff ) in
          let y := (split2 (valulen - bend) bend v) in
          let z := (split1 (bend-boff1) (lenleft-(bend-off)) dataleft) in
          let v' := combine x (combine z y) in
          mscs <- BFILE.bfwrite (FSXPLog fsxp) (FSXPInode fsxp) inum b v' mscs;
         lrx ^(mscs)    
        } else {
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
          rx ^(mscs, false)
        }
      Rof ^(mscs);
    let^ (mscs, oldattr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    mscs <- BFILE.bfsetattr (FSXPLog fsxp) (FSXPInode fsxp) inum
                            (INODE.Build_iattr (off ^+ sz)
                                               (INODE.IMTime oldattr)
                                               (INODE.IType oldattr))
                            mscs;
    let^ (mscs, ok) <- LOG.commit (FSXPLog fsxp) mscs;
    rx ^(mscs, ok).

END BYTEFILE.