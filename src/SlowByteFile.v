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
    BFileRec.array_item_file byte_type items_per_valu itemsz_ok f allbytes /\
    # (natToWord addrlen (length allbytes)) = length allbytes.

  Definition rep (bytes : list byte) (f : BFILE.bfile) :=
    exists allbytes,
    bytes_rep f allbytes /\
    firstn (# (f.(BFILE.BFAttr).(INODE.ISize))) allbytes = bytes.

  Fixpoint apply_bytes (allbytes : list byte) (off : nat) (data : list byte) :=
    match data with
    | nil => allbytes
    | b :: rest => updN (apply_bytes allbytes (off+1) rest) off b
    end.


  (*
  Lemma apply_bytes_upd:
    forall allbytes off b rest,
      (wordToNat off) < # (natToWord addrlen (length allbytes)) ->
      apply_bytes allbytes off (b::rest) = upd (apply_bytes allbytes (off^+$1) rest) off b.
  Proof.
    simpl. reflexivity.
  Qed.
*)

  Lemma apply_bytes_upd_comm:
    forall rest allbytes off off' b, 
      off < off' ->
      apply_bytes (updN allbytes off b) off' rest = updN (apply_bytes allbytes off' rest) off b.
  Proof.
    induction rest.
    simpl. reflexivity.
    simpl.
    intros.
    rewrite IHrest.
    rewrite updN_comm.
    reflexivity.
    omega.
    omega.
  Qed.

  Definition write_bytes T fsxp inum (off : nat) (data : list byte) mscs rx : prog T :=
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
          [[ apply_bytes allbytes' boff rest = apply_bytes allbytes off data ]] *
          [[ boff <= off + length data ]]
      OnCrash
        exists m',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
      Begin
        let^ (mscs, curlen) <- BFileRec.bf_getlen
          items_per_valu fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
        If (wlt_dec ($ boff) curlen) {
          mscs <- BFileRec.bf_put byte_type items_per_valu itemsz_ok
            fsxp.(FSXPLog) fsxp.(FSXPInode) inum ($ boff) b mscs;
          lrx ^(mscs, boff + 1)
        } else {
          let^ (mscs, ok) <- BFileRec.bf_extend
            byte_type items_per_valu itemsz_ok
            fsxp.(FSXPLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) inum b mscs;
          If (bool_dec ok true) {
            lrx ^(mscs, boff + 1)
          } else {
            rx ^(mscs, false)
          }
        }
      Rof ^(mscs, off);
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    If (wlt_dec ($ finaloff) oldattr.(INODE.ISize)) {
      mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                              (INODE.Build_iattr ($ finaloff)
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
           [[ (Fx * arrayN off data0)%pred (list2nmem bytes) ]] *
           [[ length data0 = len ]] *
           [[ length data = len ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ (Fx * arrayN off data)%pred (list2nmem bytes') ]] *
           [[ BFILE.BFAttr f = BFILE.BFAttr f' ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase 
      >} write_bytes fsxp inum off data mscs.
  Proof.
    unfold write_bytes, rep, bytes_rep.
    step.   (* step into loop *)
    step.   (* bf_getlen *)
    step.   (* if *)
    step.   (* bf_put *) 

    
    apply wlt_lt in H15. unfold byte in *. omega.
    constructor.

    step.   (* loop around, on the true if branch *)

    rewrite length_upd. auto.   (* length of allbytes still inbounds *)

    rewrite <- H14.
    rewrite <- apply_bytes_upd_comm by omega.
    unfold upd.

    erewrite wordToNat_natToWord_bound. reflexivity.

    apply list2nmem_arrayN_bound in H6.
    intuition.
    admit.  (* fix foreach loop: add fact elem in list, then contradiction *)
    eapply le_trans.
    apply H13.
    rewrite H4.
    eapply le_trans.
    apply H5.
    rewrite firstn_length.
    apply Nat.le_min_l.
    
    admit.
    
    admit.
    
    step.  (* bf_extend *)
    
    constructor.
    step.   (* if *)
    step.   (* impossible subgoal *)
    step.   (* return, on the false-false path *)
    step.   (* loop around, on the false-true path *)

    admit.  (* extending keeps length of allbytes inbounds *)
    admit.  (* something about apply_bytes when extending *)

    step.   (* impossible subgoal *)
    (* out of the for loop! *)
    step.   (* bfgetattr *)
    step.   (* if *)
    step.   (* bfsetattr *)
    step.   (* return *)

    apply pimpl_or_r. right. cancel.
    admit.  (* some unification problem *)
    admit.  (* new allbytes *)
    admit.  (* new allbytes matches array pred *)

    step.   (* return *)
    apply pimpl_or_r. right. cancel.
    admit.  (* some unification problem *)
    admit.  (* new allbytes *)
    admit.  (* new allbytes matches array pred *)

    apply LOG.activetxn_would_recover_old.
  Admitted.

End SLOWBYTEFILE.
