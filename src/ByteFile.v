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

  (* fix point for computing list of byte chunks to write, one entry per block *)
  Fixpoint chunkList (b : nat) (sz : nat) (off : nat) : list chunk :=
    match b with
      | O => nil
      | S b' =>
        let blk := off / valubytes in
        let boff := off mod valubytes in
        let bend := Nat.min (boff + sz) valubytes in
        let bsz := bend - boff in
        (@Build_chunk ($ blk) boff bend
          (off_lt_valubytes off) (end_lt_valubytes (boff + sz))
          (off_end_lt off sz)
        ) :: chunkList b' (sz - bsz) (off+boff)
     end.

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

  Theorem boff_bend_boff_valubytes_bend :
    forall boff bend,
      boff <= bend ->
      bend <= valubytes ->
      boff + (bend - boff + (valubytes - bend)) = valubytes.
  Proof.
    intros.
    omega.
  Qed.

  Theorem bend_boff_lenleft_bend_boff :
    forall bend boff lenleft,
      (*
      boff <= bend ->
      bend - boff < lenleft ->
      *)
      lenleft = bend - boff + (lenleft - (bend - boff)).
  Proof.
    intros.
    admit.
  Admitted.

  Hint Resolve boff_valubytes_boff : bytechunk.
  Hint Resolve bend_valubytes_bend : bytechunk.
  Hint Resolve bend_boff_lenleft_bend_boff : bytechunk.
  Hint Resolve boff_bend_boff_valubytes_bend : bytechunk.
  Local Obligation Tactic := eauto with bytechunk.

  Definition bsplit1_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz1 :=
    bsplit1 sz1 sz2 (eq_rect sz bytes v _ H).

  Definition bsplit2_dep sz sz1 sz2 (v : bytes sz) (H : sz = sz1 + sz2) : bytes sz2 :=
    bsplit2 sz1 sz2 (eq_rect sz bytes v _ H).

  (* Update a range of bytes in a block. z (boff, bend) is the part that we are
  replacing with data bytes, * x is the left of the block that isn't updated,
  and z is the right end. z_rest id the remainder of dataleft' *)
  Program Definition update_block v dataleft' (ck:chunk) : (valu * _) :=
    let lenleft := len_bytes_len dataleft' in
    let dataleft := len_bytes_data dataleft' in
    let boff := chunk_boff ck in
    let bend := chunk_bend ck in
    let boffProof := chunk_boff_proof ck in
    let bendProof := chunk_bend_proof ck in
    let boffbendProof := chunk_boff_bend_proof ck in
    let vb := valu2bytes v in
    let x := bsplit1_dep boff (valubytes - boff) vb _ in
    let y := bsplit2_dep bend (valubytes - bend) vb _ in
    let z := bsplit1_dep (bend-boff) (lenleft-(bend-boff)) dataleft _ in
    let z_rest := bsplit2_dep (bend-boff) (lenleft-(bend-boff)) dataleft _ in
    let v' := bcombine x (bcombine z y) in
    let v'' := eq_rect _ bytes v' valubytes _ in
    (v'', z_rest).
  Next Obligation.
    admit.
  Admitted.
  
  Program Definition write_chunk T fsxp inum (off: addr) dataleft' (ck: chunk) mscs rx : prog T :=
    let b := chunk_block ck in
    let^ (mscs, v) <- BFILE.bfread  (FSXPLog fsxp) (FSXPInode fsxp) inum b mscs;
    let (v'', z_rest) := update_block v dataleft' ck in
    mscs <- BFILE.bfwrite (FSXPLog fsxp) (FSXPInode fsxp) inum b (bytes2valu v'') mscs;
      rx ^(mscs, z_rest).
    Next Obligation.
      admit.
    Admitted.

    (* some conditions on off and dataleft'? v is the new value, something block_byte_match *)
   Theorem write_chunk_ok: forall fsxp inum off dataleft' ck mscs,
      {< m mbase F Fm A B flist f v0,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ (B * #off |-> v0)%pred (list2nmem (BFILE.BFData f)) ]]
       POST RET:^(mscs, z_rest)
             exists m' flist' f' v,
          LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ (B * #off |-> v)%pred (list2nmem (BFILE.BFData f')) ]] *
          [[ update_block v0 dataleft' ck = (v, z_rest) ]]
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} write_chunk fsxp inum off dataleft' ck mscs.
   Proof.
   Admitted.

  Program Definition write_byte T fsxp inum (off : addr) len (data : bytes len) mscs rx : prog T :=
    let^ (mscs, _) <- ForEach ck ckrest (chunkList (((len - # off)/valulen)+1) len (# off))
      Ghost [ mbase m F ]
      Loopvar [ mscs dataleft' ]
      Continuation lrx
      Invariant
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs
        (* XXX n bytes written, n + remaining = sz *)
      OnCrash
        LOG.would_recover_old fsxp.(FSXPLog) F mbase
      Begin
        let^ (mscs, ok) <- grow_if_needed fsxp inum (chunk_block ck) mscs;
        If (bool_dec ok true) {
          let^ (mscs, z_rest) <- write_chunk fsxp inum off dataleft' ck mscs;
          lrx ^(mscs, (Build_len_bytes z_rest))
        } else {
          mscs <- LOG.abort (FSXPLog fsxp) mscs;
          rx ^(mscs, false)
        }
      Rof ^(mscs, Build_len_bytes data);
    let^ (mscs, oldattr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    mscs <- BFILE.bfsetattr (FSXPLog fsxp) (FSXPInode fsxp) inum
                            (INODE.Build_iattr (off ^+ ($ len))
                                               (INODE.IMTime oldattr)
                                               (INODE.IType oldattr))
                            mscs;
    rx ^(mscs, true).

       

End BYTEFILE.
