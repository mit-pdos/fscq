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
      | O => nil   (* XXX maybe the last chunk: [(off, sz)] *)
      | S b' =>
        let blk := off / valubytes in   (* XXX blk should be addr, very slow! *)
        let boff := off mod valubytes in
        let bend := Nat.min (boff + sz) valubytes in
        let bsz := bend - boff in
        (@Build_chunk ($ blk) boff bend
          (off_lt_valubytes off) (end_lt_valubytes (boff + sz))
          (off_end_lt off sz)
        ) :: chunkList b' (sz - bsz) (off+boff)
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

(*
  Theorem boff_bend_boff_valulen_bend :
    forall boff bend,
      
(boff + (bend - boff + (valulen - bend)))
*)

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
      lenleft = bend - boff + (lenleft - (bend - boff)).
  Proof.
    admit.
  Admitted.

  Definition write_byte T fsxp inum (off : addr) len (data : bytes len) mscs rx : prog T :=
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
        let lenleft := len_bytes_len dataleft' in
        let dataleft := len_bytes_data dataleft' in
        let b := chunk_block ck in
        let boff1 := chunk_boff ck in
        let bend := chunk_bend ck in
        let boffProof := chunk_boff_proof ck in
        let bendProof := chunk_bend_proof ck in
        let boffendProof := chunk_boff_bend_proof ck in
        let^ (mscs, ok) <- grow_if_needed fsxp inum b mscs;
        If (bool_dec ok true) {
          let^ (mscs, v) <- BFILE.bfread  (FSXPLog fsxp) (FSXPInode fsxp) inum b mscs;
          let vb := valu2bytes v in
          let v_boff := eq_rect valubytes bytes vb (boff1 + (valubytes-boff1)) (@boff_valubytes_boff boff1 boffProof) in
          let v_bend := eq_rect valubytes bytes vb (bend + (valubytes - bend)) (@bend_valubytes_bend bend bendProof) in
          let x := bsplit1 (boff1) (valubytes - boff1) v_boff in
          let y := bsplit2 bend (valubytes - bend) v_bend in
          let dataleft_cast := eq_rect _ bytes dataleft
            (bend - boff1 + (lenleft - (bend - boff1))) (bend_boff_lenleft_bend_boff bend boff1 _) in
          let z := bsplit1 (bend-boff1) (lenleft-(bend-boff1)) dataleft_cast in
          let z_rest := bsplit2 (bend-boff1) (lenleft-(bend-boff1)) dataleft_cast in
          let v' := bcombine x (bcombine z y) in
          let v'' := eq_rect _ bytes v' valubytes
            (@boff_bend_boff_valubytes_bend boff1 bend boffendProof bendProof) in
          mscs <- BFILE.bfwrite (FSXPLog fsxp) (FSXPInode fsxp) inum b (bytes2valu v'') mscs;
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
