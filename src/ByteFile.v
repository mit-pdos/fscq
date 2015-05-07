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

Set Implicit Arguments.
Import ListNotations.

Module BYTEFILE.

  Fixpoint list2word elen (l : list (word elen)) : word (length l * elen).
    refine
      match l with
      | nil => $0
      | x :: l' => _
      end.
    exact (Word.combine x (list2word elen l')).
  Defined.

  Fixpoint word2list elen nelem (w : word (nelem * elen)) : list (word elen).
    refine
     (match nelem as n' return (nelem = n' -> list (word elen)) with
      | 0 => fun _ => nil
      | S nelem' => _
      end eq_refl).
    intros; subst.
    refine (split1 elen (nelem' * elen) w :: _).
    exact (word2list elen nelem' (split2 elen (nelem' * elen) w)).
  Defined.

  Theorem length_word2list : forall elen nelem (w : word (nelem * elen)),
    length (word2list elen nelem w) = nelem.
  Proof.
    induction nelem; simpl; auto.
  Qed.

  Theorem length_word2list_mult : forall elen nelem (w : word (nelem * elen)),
    nelem * elen = length (word2list elen nelem w) * elen.
  Proof.
    intros; rewrite length_word2list; auto.
  Qed.

  Theorem list2word2list : forall elen l,
    word2list elen (length l) (list2word l) = l.
  Proof.
    unfold word2list, list2word, eq_rec_r, eq_rec.
    induction l.
    reflexivity.
    simpl in *.
    f_equal.
    rewrite split1_combine; auto.
    rewrite split2_combine; auto.
  Qed.

  Theorem word2list2word : forall elen nelem (w : word (nelem * elen)),
    list2word (word2list elen nelem w) =
    eq_rect (nelem*elen) word w (length (word2list elen nelem w) * elen) (length_word2list_mult _ _ _).
  Proof.
    induction nelem; simpl; intros.
    rewrite word0; reflexivity.
    rewrite IHnelem; clear IHnelem.
    rewrite combine_split_eq_rect2.
    f_equal.
    apply (UIP_dec eq_nat_dec).
  Qed.

  Lemma block_byte_match_1 :
    forall x,
      valubytes = (Nat.min x valubytes) + (valubytes - (Nat.min x valubytes)).
  Proof.
    intros.
    rewrite le_plus_minus_r; auto.
    apply Min.le_min_r.
  Qed.

  Lemma block_byte_match_2 :
    forall lenbytes x,
      lenbytes =
      (Nat.min lenbytes x) + (lenbytes - (Nat.min lenbytes x)).
  Proof.
    intros.
    rewrite le_plus_minus_r; auto.
    apply Min.le_min_l.
  Qed.

  Fixpoint block_byte_match (blocks : list valu) (bytelist : list byte) : Prop :=
    match blocks with
    | nil => bytelist = nil
    | b :: blocks' =>
      let this_block_bytes := Nat.min (length bytelist) valubytes in
      let b_split := eq_rect valubytes bytes (valu2bytes b)
        (this_block_bytes + (valubytes - this_block_bytes)) (block_byte_match_1 _) in
      let bytes_split := eq_rect (length bytelist) bytes (list2word bytelist)
        (this_block_bytes + (length bytelist - this_block_bytes)) (block_byte_match_2 _ _) in
      (bsplit1 (this_block_bytes) (valubytes - this_block_bytes) b_split =
       bsplit1 (this_block_bytes) (length bytelist - this_block_bytes) bytes_split) /\
      block_byte_match blocks'
        (word2list 8 (length bytelist - this_block_bytes)
          (bsplit2 this_block_bytes (length bytelist - this_block_bytes) bytes_split))
    end.

  Definition rep (bytes : list byte) (bfattr : BFILE.bfattr) : @pred nat eq_nat_dec valu :=
    (exists blocks,
     [[ length bytes = # (bfattr.(INODE.ISize)) ]] *
     arrayN 0 blocks *
     [[ block_byte_match blocks bytes ]])%pred.


  Record chunk := {
                   chunk_block : addr;
                   chunk_boff : nat;
                   chunk_bend : nat;
                   chunk_data : bytes (chunk_bend-chunk_boff);
                   chunk_boff_proof : chunk_boff < valubytes;
                   chunk_bend_proof : chunk_bend <= valubytes;
                   chunk_boff_bend_proof : chunk_boff <= chunk_bend
                   }.

  Lemma off_lt_valubytes :
    forall off,
      off mod valubytes < valubytes.
  Proof.
    intros.
    apply Nat.mod_bound_pos.
    omega.
    rewrite valubytes_is; omega.
  Qed.

  Lemma end_lt_valubytes :
    forall x,
      Nat.min x valubytes <= valubytes.
  Proof.
    intros.
    apply Nat.le_min_r.
  Qed.

  Lemma off_end_lt :
    forall off sz,
      off mod valubytes <= Nat.min (off mod valubytes + sz) valubytes.
  Proof.
    intros.
    apply Nat.min_glb.
    omega.
    apply Nat.lt_le_incl.
    apply Nat.mod_bound_pos.
    omega.
    rewrite valubytes_is; omega.
  Qed.

  Definition bsplit1_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz1 :=
    bsplit1 sz1 sz2 (eq_rect sz bytes v _ H).

  Definition bsplit2_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz2 :=
    bsplit2 sz1 sz2 (eq_rect sz bytes v _ H).

  Theorem bsz_ok:
    forall sz bsz,
      bsz <= sz -> sz = bsz + (sz - bsz).
  Proof.
    intros.
    omega.
  Qed.

  Theorem bsz_le_sz:
    forall off sz,
      (Nat.min ((off mod valubytes) + sz) valubytes) - (off mod valubytes) <= sz.
  Proof.
    intros.
    admit.
  Admitted.

  (* fix point for computing list of byte chunks to write, one entry per block *)
  Function chunkList (sz : nat) (data: bytes sz) (off : nat) {measure id sz} : list chunk :=
    match sz with
      | O => nil
      | S sz' =>
        let blk := off / valubytes in
        let boff := off mod valubytes in
        let bend := Nat.min (boff + sz) valubytes in
        let bsz := bend - boff in
        (@Build_chunk ($ blk) boff bend (bsplit1_dep bsz (sz-bsz) data (bsz_ok (bsz_le_sz _ _)))
          (off_lt_valubytes off) (end_lt_valubytes (boff + sz))
          (off_end_lt off sz)
        ) :: @chunkList (sz - bsz) (bsplit2_dep bsz (sz-bsz) data (bsz_ok (bsz_le_sz _ _))) (off+boff) 
     end.
  Proof.
    intros.
    rewrite <- teq.
    admit.
  Admitted.

  (* Eval compute in chunkList 1 10 10. *)

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

  Lemma boff_valubytes_boff :
    forall boff,
      boff < valubytes ->
      valubytes = boff + (valubytes - boff).
  Proof.
    intros. omega.
  Qed.

  Lemma bend_valubytes_bend :
    forall bend,
      bend <= valubytes ->
      valubytes = bend + (valubytes - bend).
  Proof.
    intros. omega.
  Qed.

  Record len_bytes := {
    len_bytes_len : nat;
    len_bytes_data : bytes len_bytes_len
  }.

  Theorem xlen_ylen_zlen_valulen :
    forall boff bend ylen,
      boff <= bend ->
      bend <= valubytes ->
      ylen = bend - boff ->
      boff + (ylen + (valubytes - bend)) = valubytes.
  Proof.
    intros.
    omega.
  Qed.

  Theorem ylen_lenleft_ylen :
    forall ylen lenleft,
      (*
      boff <= bend ->
      bend - boff < lenleft ->
      *)
      lenleft = ylen + (lenleft - ylen).
  Proof.
    intros.
    admit.
  Admitted.

  Theorem valubytes_valulen:
      valubytes * 8 = valulen.
  Proof.
    rewrite valubytes_is.
    rewrite valulen_is.
    reflexivity.
  Qed.

  Hint Resolve boff_valubytes_boff : bytechunk.
  Hint Resolve bend_valubytes_bend : bytechunk.
  Hint Resolve ylen_lenleft_ylen : bytechunk.
  Hint Resolve xlen_ylen_zlen_valulen: bytechunk.
  Hint Resolve valubytes_valulen : bytechunk.
  Local Obligation Tactic := eauto with bytechunk.



  (* Update the range (boff, bend) of bytes in v. It is replaced with chunk
   data. x is the left of the block that isn't updated (< boff), and z is the
   right end (> bend). the new block is v' = x * chunk_data * z. *)
  Program Definition update_block v (ck:chunk) : valu :=
    let boff := chunk_boff ck in
    let bend := chunk_bend ck in
    let boffProof := chunk_boff_proof ck in
    let bendProof := chunk_bend_proof ck in
    let boffbendProof := chunk_boff_bend_proof ck in
    let vb := valu2bytes v in
    let x := bsplit1_dep boff (valubytes - boff) vb _ in
    let z := bsplit2_dep bend (valubytes - bend) vb _ in
    let ylen := bend-boff in
    let y := chunk_data ck in
    let v' := bcombine x (bcombine y z) in
    let v'' := eq_rect _ bytes v' valubytes _ in
    v''.

  Program Definition write_chunk T fsxp inum (ck: chunk) mscs rx : prog T :=
    let b := chunk_block ck in
    let^ (mscs, v) <- BFILE.bfread  (FSXPLog fsxp) (FSXPInode fsxp) inum b mscs;
    let v':= update_block v ck in
    mscs <- BFILE.bfwrite (FSXPLog fsxp) (FSXPInode fsxp) inum b (bytes2valu v') mscs;
    rx mscs.

   Theorem write_chunk_ok: forall fsxp inum ck mscs,
     {< m mbase F Fm A B flist f v0,
     PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ (B * #(chunk_block ck) |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
     POST RET: mscs
             exists m' flist' f' v,
          LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #(chunk_block ck) |-> v)%pred (list2nmem (BFILE.BFData f')) ]] *
          [[ update_block v0 ck = v ]]
     CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} write_chunk fsxp inum ck mscs.
   Proof.
     (*
     unfold write_chunk.
     hoare.
     unfold update_block.
     unfold bytes2valu.
     unfold eq_rec_r.
     unfold eq_rec.
     repeat rewrite eq_rect_nat_double.

     generalize (update_block_obligation_1 v8 ck).

     
     generalize  (update_block_obligation_3 v8 ck).
     generalize  (update_block_obligation_2 v8 ck).
     
     generalize (eq_trans (update_block_obligation_4 v8 ck)  (write_chunk_obligation_1 fsxp inum ck ^( m0, c) rx ^( a0, a1) v8 tt)).
     generalize (update_block_obligation_4 v8 ck).
     generalize  (eq_sym valulen_is).
     
     unfold valu2bytes.

     generalize valubytes_is.
     generalize valulen_is.
     
     generalize (chunk_boff_proof ck).
     generalize chunk_bend_proof ck.

     
     rewrite valubytes_is.
     intros.

     Require Import ProofIrrelevance.
     replace e1 with e2 by apply proof_irrelevance.

     SearchAbout eq_rect.
     Print eq_rect_r.
     Print eq_rect.
*)
     admit.
  Admitted.


   Axiom a:
     False.

   Local Obligation Tactic := destruct a.

   Require Import Wf.

   Print upd.
   
   Fixpoint apply_chunk (bytelist : list byte) (b:addr) (boff bend : nat) (data: bytes (bend-boff)) (pf : boff <= bend) : list byte.
     refine
     (match bend as X return bend = X -> list byte with
       | O => fun pf => bytelist
       | S bend' => fun pf => 
     if lt_dec boff bend then
       let bytelist' := @apply_chunk bytelist b boff bend' (bsplit1_dep (bend'-boff) 1 data _) _ in
       @upd byte bytelist' ((b ^* ($ valubytes)) ^+ ($ bend) ^- $1) (bsplit2_dep (bend-boff-1) 1 data _)
     else
       bytelist
     end (refl_equal _)).
     omega.
     omega.
     omega.
   Defined.
  
   Fixpoint apply_chunks (bytelist : list byte) cklist :=
     match cklist with
       | nil => nil
       | ck :: cklist' => let bytelist' := apply_chunks bytelist cklist' in
                      @apply_chunk bytelist' (chunk_block ck) (chunk_boff ck) (chunk_bend ck) (chunk_data ck) (chunk_boff_bend_proof ck)
     end.

   Definition write_bytes T fsxp inum (off : addr) len (data : bytes len) mscs rx : prog T :=
    let chunkList' := chunkList data (# off) in
    let^ (mscs) <- ForEach ck ckrest chunkList'
      Ghost [ mbase F Fm A bytes ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant
        exists m' flist' f' bytes',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs  *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ rep bytes' (BFILE.BFAttr f') (list2nmem (BFILE.BFData f')) ]] *
          [[ apply_chunks bytes' ckrest = apply_chunks bytes chunkList' ]]
      OnCrash
        LOG.would_recover_old fsxp.(FSXPLog) F mbase
      Begin
        let^ (mscs, ok) <- grow_if_needed fsxp inum (chunk_block ck) mscs;
        If (bool_dec ok true) {
          mscs <- write_chunk fsxp inum ck mscs;
          lrx ^(mscs)
        } else {
          rx ^(mscs, false)
        }
      Rof ^(mscs);

    (*
    let^ (mscs, oldattr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    mscs <- BFILE.bfsetattr (FSXPLog fsxp) (FSXPInode fsxp) inum
                            (INODE.Build_iattr (off ^+ ($ len))
                                               (INODE.IMTime oldattr)
                                               (INODE.IType oldattr))
                            mscs; *)
    rx ^(mscs, true).

  
  Theorem write_bytes_ok: forall fsxp inum off len data mscs,
      {< m mbase F Fm A flist f bytes data0 Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes (BFILE.BFAttr f) (list2nmem (BFILE.BFData f)) ]] *
           [[ (Fx * array off data0 $1)%pred (list2mem bytes) ]] *
           [[ length data0 = len ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' (BFILE.BFAttr f') (list2nmem (BFILE.BFData f')) ]] *
           [[ (Fx * array off (word2list 8 len data) $1)%pred (list2mem bytes') ]] *
           [[ BFILE.BFAttr f = BFILE.BFAttr f' ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase 
      >} write_bytes fsxp inum off data mscs.
  Proof.
    unfold write_bytes.
    hoare.
    
    
     admit.
   Admitted.
         
       

End BYTEFILE.
