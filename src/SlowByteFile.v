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
Require Import Eqdep_dec.
Require Import Bytes.
Require Import ProofIrrelevance.

Set Implicit Arguments.
Import ListNotations.

Module SLOWBYTEFILE.

  Definition byte_type := Rec.WordF 8.
  Definition itemsz := Rec.len byte_type.
  Definition items_per_valu : addr := $ valubytes.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    unfold items_per_valu.
    rewrite valulen_is, valubytes_is.
    reflexivity.
  Qed.

  Definition bytes_rep f (allbytes : list byte) :=
    BFileRec.array_item_file byte_type items_per_valu itemsz_ok f allbytes.

  Definition rep (bytes : list byte) (f : BFILE.bfile) :=
    exists allbytes,
    bytes_rep f allbytes /\
    firstn (# (f.(BFILE.BFAttr).(INODE.ISize))) allbytes = bytes.

  Fixpoint apply_bytes (allbytes : list byte) (off : addr) (data : list byte) :=
    match data with
    | nil => allbytes
    | b :: rest => upd (apply_bytes allbytes (off^+$1) rest) off b
    end.

  Definition write_bytes T fsxp inum (off : addr) (data : list byte) mscs rx : prog T :=
    let^ (mscs, finaloff) <- ForEach b rest data
      Ghost [ mbase F Fm A allbytes ]
      Loopvar [ mscs boff ]
      Continuation lrx
      Invariant
        exists m' flist' f' allbytes',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs  *
          [[ (Fm * BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ bytes_rep f' allbytes' ]] *
          [[ apply_bytes allbytes' boff rest = apply_bytes allbytes off data ]]
      OnCrash
        exists m',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
      Begin
        let^ (mscs, curlen) <- BFileRec.bf_getlen
          items_per_valu fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
        If (wlt_dec boff curlen) {
          mscs <- BFileRec.bf_put byte_type items_per_valu itemsz_ok
            fsxp.(FSXPLog) fsxp.(FSXPInode) inum boff b mscs;
          lrx ^(mscs, boff ^+ $1)
        } else {
          let^ (mscs, ok) <- BFileRec.bf_extend
            byte_type items_per_valu itemsz_ok
            fsxp.(FSXPLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) inum b mscs;
          If (bool_dec ok true) {
            lrx ^(mscs, boff ^+ $1)
          } else {
            rx ^(mscs, false)
          }
        }
      Rof ^(mscs, off);
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    If (wlt_dec finaloff oldattr.(INODE.ISize)) {
      mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                              (INODE.Build_iattr finaloff
                                                 (INODE.IMTime oldattr)
                                                 (INODE.IType oldattr)) mscs;
      rx ^(mscs, true)
    } else {
      rx ^(mscs, true)
    }.

  Theorem write_bytes_ok: forall fsxp inum off len data mscs,
      {< m mbase F Fm A flist f bytes data0 Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ (Fx * array off data0 $1)%pred (list2mem bytes) ]] *
           [[ length data0 = len ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ (Fx * array off data $1)%pred (list2mem bytes') ]] *
           [[ BFILE.BFAttr f = BFILE.BFAttr f' ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase 
      >} write_bytes fsxp inum off data mscs.
  Proof.
    unfold write_bytes.
    step.   (* step into loop *)
    instantiate (allbytes' := bytes).
    unfold rep in H6.
    admit.

    step.  (* bf_getlen *)
    step.   (* if *)
    step.   (* bf_put *)

    
    
    unfold rep.
    cancel.

    admit.

    step.

    admit.

    rewrite <- H11.

    admit.  

    step.
    
    apply pimpl_or_r.

    right.

    cancel.   (*  unification problem *)

    admit.

    admit.

   Admitted.
         
       

End SLOWBYTEFILE.
