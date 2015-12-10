Require Import Mem.
Require Import Prog.
Require Import Log.
Require Import BFile.
Require Import Word.
Require Import BasicProg.
Require Import Bool.
Require Import Pred.
Require Import Hoare.
Require Import GenSep.
Require Import GenSepN.
Require Import SepAuto.
Require Import Idempotent.
Require Import Inode.
Require Import List.
Require Import Balloc.
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
Require Import BFileRec Rounding.

Set Implicit Arguments.
Import ListNotations.

(** A byte-based interface to a BFileRec. Fast because it uses the range
update operation in BFileRec to do writes, and exposes an API that uses
[byte count]s rather than [list byte]s as inputs. *)
Module BYTEFILE.

  Definition byte_type := Rec.WordF 8.
  Definition itemsz := Rec.len byte_type.
  Definition items_per_valu : addr := $ valubytes.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    unfold items_per_valu.
    rewrite valulen_is, valubytes_is.
    reflexivity.
  Qed.

  Record bytefile_attr := {
    FMTime : word 32;
    FType : word 32;
    FDev : word 64
  }.

  Definition attr0 := Build_bytefile_attr $0 $0 $0.

  (* The bytes of a file are mapped onto a list of blocks:   *)
  (*   [ block 0 ... block n]                                *)
  (*   <-- allbytes      -->                                 *)
  (*   <-- bytes     -->                                     *)

  Definition bytes_rep f (allbytes : list byte) :=
    BFileRec.array_item_file byte_type items_per_valu itemsz_ok f allbytes /\
    # (natToWord addrlen (length allbytes)) = length allbytes.

  Definition rep (bytes : list byte) (attr : bytefile_attr) (f : BFILE.bfile) :=
    exists allbytes,
    bytes_rep f allbytes /\
    firstn (# (f.(BFILE.BFAttr).(INODE.ISize))) allbytes = bytes /\
    length bytes = (# (f.(BFILE.BFAttr).(INODE.ISize))) /\
    divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes /\
    FMTime attr = INODE.IMTime (BFILE.BFAttr f) /\
    FType attr = INODE.IType (BFILE.BFAttr f) /\
    FDev attr = INODE.IDev (BFILE.BFAttr f).

  Lemma block_items_ok : block_items items_per_valu = valubytes.
  Proof.
    unfold block_items.
    unfold items_per_valu.
    rewrite valubytes_is.
    reflexivity.
  Qed.

  (* roundup_ge specialized to valubytes *)
  Lemma roundup_valu_ge : forall n, n <= roundup n valubytes.
  Proof.
    intros.
    apply roundup_ge.
    rewrite valubytes_is.
    (* produces a nicer proof term than omega *)
    apply gt_Sn_O.
  Qed.

  Definition hidden (P : Prop) : Prop := P.
  Opaque hidden.

  Definition update_bytes T fsxp inum (off : nat) len (newbytes : bytes len) mscs rx : prog T :=
  If (lt_dec 0 len) {
    let^ (mscs) <- BFileRec.bf_update_range items_per_valu itemsz_ok
      fsxp inum off newbytes mscs;
    rx ^(mscs)
  } else {
    rx ^(mscs)
  }.

  Inductive byte_buf : Set :=
  | len_bytes : forall (len:nat), bytes len -> byte_buf.

  Definition buf_len (buf:byte_buf) : nat :=
  match buf with
  | @len_bytes len _ => len
  end.

  Definition buf_data (buf:byte_buf) : bytes (buf_len buf) :=
  match buf with
  | @len_bytes _ b => b
  end.

  Definition read_bytes T fsxp inum (off:nat) len mscs rx : prog T :=
  If (lt_dec 0 len) {
    let^ (mscs, attr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    let flen := # (INODE.ISize attr) in
    If (lt_dec off flen) {
      If (lt_dec (off+len) flen) {
        let^ (mscs, data) <- BFileRec.bf_read_range items_per_valu itemsz_ok
          fsxp inum off len mscs;
        rx ^(mscs, len_bytes data)
      } else {
        let^ (mscs, data) <- BFileRec.bf_read_range items_per_valu itemsz_ok
          fsxp inum off (flen - off) mscs;
        rx ^(mscs, len_bytes data)
      }
   } else {
    (* reading starting at or past the end of the file *)
    rx ^(mscs, @len_bytes 0 (wzero _))
   }
  } else {
    (* reading zero bytes *)
    rx ^(mscs, @len_bytes 0 (wzero _))
  }.

  Implicit Arguments read_bytes [T].

  Lemma list2nmem_array_eq' : forall A (l l':list A),
    l = l' ->
    arrayN 0 l (list2nmem l').
  Proof.
    intros.
    rewrite H.
    apply list2nmem_array.
  Qed.

  Lemma sep_star_abc_to_acb : forall AT AEQ AV (a b c : @pred AT AEQ AV),
    (a * b * c)%pred =p=> (a * c * b).
  Proof. cancel. Qed.

  Lemma list2nmem_arrayN_xyz_frame : forall (A:Type) (l:list A)
    off len,
    off + len <= length l ->
    (arrayN 0 (firstn off l) *
    arrayN (off+len) (skipn (off+len) l) *
    arrayN off (firstn len (skipn off l)))%pred (list2nmem l).
  Proof.
    intros.
    apply sep_star_abc_to_acb.
    rewrite arrayN_combine by LOG.solve_lengths.
    apply arrayN_combine.
    LOG.solve_lengths.
    apply list2nmem_array_eq'.
    rewrite <- firstn_sum_split.
    apply firstn_skipn.
  Qed.

  Lemma goodSize_read_length : forall F A m bxp ixp
   (inum:addr) (fl : list BFILE.bfile)
    f len (allbytes : list byte),
    array_item_file byte_type items_per_valu itemsz_ok f allbytes ->
    (A * # (inum) |-> f)%pred (list2nmem fl) ->
    (F * BFILE.rep bxp ixp fl)%pred m ->
    len <= length allbytes ->
    goodSize addrlen len.
  Proof.
    intros.
    eapply goodSize_word_bound.
    eapply le_trans; eauto.
    eapply bfrec_bound with (itemtype := byte_type); eauto.
  Qed.

  Hint Resolve goodSize_read_length.

  Lemma min_eq_l : forall n m,
    n <= m ->
    n = Nat.min n m.
  Proof.
    intros.
    rewrite Nat.min_l; omega.
  Qed.

  Lemma min_eq_r : forall n m,
    m <= n ->
    m = Nat.min n m.
  Proof.
    intros.
    rewrite Nat.min_r; omega.
  Qed.

  Hint Resolve min_eq_l min_eq_r.
  Hint Extern 4 (_ <= _) => omega.

  Theorem read_bytes_ok: forall fsxp inum off len mscs,
  {< m mbase F Fm A flist f bytes attr,
  PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
      [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
      [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
      [[ rep bytes attr f ]]
   POST RET:^(mscs, b)
      exists Fx v,
      LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
      [[ (Fx * arrayN off v)%pred (list2nmem bytes) ]] *
      [[ @Rec.of_word (Rec.ArrayF byte_type (buf_len b))
        (buf_data b) = v ]] *
      let flen := # (INODE.ISize (BFILE.BFAttr f)) in
      [[ buf_len b = Nat.min (flen - off) len ]] *
      [[ goodSize addrlen (buf_len b) ]] *
      (* non-error guarantee *)
      [[ 0 < len -> off < flen ->
         0 < buf_len b ]]
   CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
   >} read_bytes fsxp inum off len mscs.
   Proof.
    unfold read_bytes, rep, bytes_rep.
    step. (* 15s *)
    step.
    step.
    step.
    step.

    eapply goodSize_word_bound.
    eapply le_trans.
    apply divup_lt_arg.
    apply Nat.lt_le_incl; eauto.

    erewrite array_items_num_blocks; eauto.
    apply divup_mono.
    eapply le_trans.
    apply Nat.lt_le_incl; eauto.
    apply firstn_length_l_iff; auto.

    step.
    match goal with
    | [ H: Rec.of_word ?w = _ |- context[Rec.of_word ?w] ] =>
      rewrite H
    end.
    rewrite <- firstn_double_skipn
      with (len2 := # (INODE.ISize (BFILE.BFAttr f)))
      by omega.
    apply list2nmem_arrayN_xyz_frame.
    omega.

    apply firstn_length_l_iff in H4.
    eauto.

    step.
    rewrite le_plus_minus_r by omega.
    eapply goodSize_word_bound.
    eapply le_trans.
    apply divup_lt_arg.
    eauto.

    rewrite le_plus_minus_r by omega.
    erewrite BFileRec.array_items_num_blocks; eauto.
    apply divup_mono.
    apply firstn_length_l_iff; auto.

    step.
    match goal with
    | [ H: Rec.of_word ?w = _ |- context[Rec.of_word ?w] ] =>
      rewrite H
    end.
    rewrite <- firstn_double_skipn
      with (len2 := # (INODE.ISize (BFILE.BFAttr f)))
      by omega.
    apply list2nmem_arrayN_xyz_frame.
    omega.

    apply firstn_length_l_iff in H4.
    eauto.

    step.
    (* off out of bounds *)
    apply emp_star_r.
    apply list2nmem_array.

    (* buf_len value (error) *)
    rewrite Nat.min_l; omega.

    (* len = 0 *)
    step.
    apply emp_star_r.
    apply list2nmem_array.

    (* buf_len value (error) *)
    rewrite Nat.min_r; omega.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_bytes _ _ _ _ _) _) => apply read_bytes_ok : prog.

  Theorem update_bytes_ok: forall fsxp inum off len (newbytes : bytes len) mscs,
      {< m mbase F Fm A flist f bytes attr olddata Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes attr f ]] *
           [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]] *
           [[ length olddata = len ]]
      POST RET: ^(mscs)
           exists m' flist' f' bytes',
           LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' attr f' ]] *
           [[ let newdata := @Rec.of_word (Rec.ArrayF byte_type len) newbytes in
              (Fx * arrayN off newdata)%pred (list2nmem bytes') ]]
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} update_bytes fsxp inum off newbytes mscs.
  Proof.
    unfold update_bytes.
    step. (* 40s *)
    inversion H6 as [allbytes Hrepconj].
    inversion Hrepconj as [Hbytes_rep Hrepconj']; clear Hrepconj.
    inversion Hbytes_rep as [Hrecrep Hallbytes_goodSize].
    (* TODO: replace this with filelen f *)
    set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.

    step. (* 50s *)
    - instantiate (Fx0 := (Fx * arrayN flen
        (skipn flen allbytes))%pred).
      rewrite <- firstn_skipn with (l := allbytes) (n := flen) at 2.
      replace (firstn flen allbytes).
      replace flen with (length bytes) at 1.
      apply list2nmem_arrayN_app with (l' := skipn flen allbytes) in H5.
      pred_apply; cancel.
      cancel.
    - reflexivity.
    - unfold BFileRec.hidden.
      rewrite Rec.array_of_word_length with (ft := byte_type).
      auto.
    - unfold BFileRec.hidden in *.
      fold byte in *.
      step.
      * unfold rep.
        exists ilist'.
        split; [|split]; eauto.
        split; auto.
        eapply wordToNat_natToWord_bound.
        eapply BFileRec.bfrec_bound with (itemtype := byte_type); eauto.
        split.
        subst.
        apply firstn_length_l.
        replace (length ilist').
        replace (BFILE.BFAttr f').
        apply firstn_length_l_iff; auto.
        replace (length ilist').
        replace (BFILE.BFAttr f').
        auto.
      * replace (BFILE.BFAttr f').
        apply firstn_length_l_iff in H10.
        match goal with
        | [ H : _ (list2nmem ilist') |- _ ] => rename H into Hilist'
        end.
        rewrite <- firstn_skipn with (l := ilist') (n := # (INODE.ISize (BFILE.BFAttr f))) in Hilist'.
        assert (length (firstn # (INODE.ISize (BFILE.BFAttr f)) ilist')
          = # (INODE.ISize (BFILE.BFAttr f))) as Hflen.
        apply firstn_length_l; omega.
        eapply pimpl_apply in Hilist'; [|apply sep_star_abc_to_acb].
        rewrite <- Hflen in Hilist' at 1.
        assert (Htails_eq := Hilist').
        apply list2nmem_arrayN_end_eq in Htails_eq; auto.
        rewrite Htails_eq in Hilist'.
        apply list2nmem_arrayN_app_iff in Hilist'.
        assumption.
        exact ($ 0).
        autorewrite with lengths; omega.
    - (* no-op case len = 0 *)
      step.
      assert (olddata = nil) by (apply length_nil; omega).
      subst olddata.
      simpl.
      pred_apply; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (update_bytes ?fsxp ?inum ?off ?newbytes _) _) =>
    apply update_bytes_ok with (fsxp:=fsxp) (inum:=inum) (off:=off) (newbytes:=newbytes) : prog.

  Definition grow_file T fsxp inum newlen mscs rx : prog T :=
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    let oldlen := oldattr.(INODE.ISize) in
    If (wlt_dec oldlen ($ newlen)) {
      let^ (mscs, ok) <- bf_expand items_per_valu fsxp inum newlen mscs;
      If (bool_dec ok true) {
        let zeros := @natToWord ((roundup newlen valubytes-#oldlen)*8) 0 in
        let^ (mscs) <- bf_update_range items_per_valu itemsz_ok
           fsxp inum #oldlen zeros mscs;
         mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                                (INODE.Build_iattr ($ newlen)
                                                   (INODE.IMTime oldattr)
                                                   (INODE.IType oldattr)
                                                   (INODE.IDev oldattr)) mscs;
        rx ^(mscs, true)
      } else {
        rx ^(mscs, false)
      }
    } else {
      rx ^(mscs, true)
    }.

  Definition filelen f := # (INODE.ISize (BFILE.BFAttr f)).

  Theorem grow_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes attr,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes attr f ]] *
           [[ goodSize addrlen newlen ]] *
           (* spec requires that file is growing, so that it can guarantee
              that the new size of the file is $newlen. *)
           [[ filelen f <= newlen ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' fdata' fattr',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ bytes' = (bytes ++ (repeat $0 (newlen -  (# (INODE.ISize (BFILE.BFAttr f)))))) ]] *
           [[ rep bytes' attr f' ]] *
           [[ fattr' = INODE.Build_iattr ($ newlen) f.(BFILE.BFAttr).(INODE.IMTime) f.(BFILE.BFAttr).(INODE.IType) f.(BFILE.BFAttr).(INODE.IDev) ]] *
           [[ f' = BFILE.Build_bfile fdata' fattr' ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} grow_file fsxp inum newlen mscs.
   Proof.
     unfold grow_file, rep, bytes_rep.
     step. (* 30s *)
     step.
     step. (* 10s *)

     fold (filelen f) in *.
     instantiate (Fi := arrayN 0 allbytes).
     apply list2nmem_array.
     apply firstn_length_l_iff in H6.
     unfold ge.
     fold (filelen f) in H10.
     fold byte.
     replace (length allbytes).
     fold (roundup (filelen f) valubytes).
     rewrite block_items_ok.
     apply roundup_mono.
     apply Nat.lt_le_incl.
     unfold filelen.
     apply lt_word_lt_nat; auto.

     assert (filelen f < newlen) as Hnewlen.
     apply lt_word_lt_nat; auto.
     assert (Hflenround := roundup_valu_ge (filelen f)).
     assert (Hnewlenround := roundup_valu_ge newlen).
     assert (roundup (filelen f) valubytes <= roundup newlen valubytes) as
      Hnewlen_round.
     apply roundup_mono; omega.
     assert (filelen f <= length allbytes) as Hflen_all.
     replace (length allbytes).
     apply roundup_valu_ge.
     assert (Init.Nat.min (filelen f) (length allbytes) =
      filelen f) as Hlen_all_min.
     apply Nat.min_l; auto.

     step.
     step. (* 60s *)
     step.

     step. (* 80s *)
     fold (filelen f) in *.
     apply firstn_length_l_iff in H6.
     instantiate (Fx0 := arrayN 0 (firstn (filelen f) allbytes)).
     instantiate (olddata0 := skipn (filelen f) (allbytes ++ a7)).
     replace (firstn (filelen f) allbytes) with
      (firstn (filelen f) (allbytes ++ a7)) at 1.
     apply list2nmem_arrayN_firstn_skipn.
     apply firstn_app_l; omega.
     reflexivity.
     unfold BFileRec.hidden.
     fold (filelen f).
     assert (Hlen := Rec.array_of_word_length
      byte_type (roundup newlen valubytes - filelen f) ($ 0)).
     simpl in Hlen.
     fold byte in *.
     rewrite Hlen; clear Hlen.
     fold (filelen f) in *.
     assert (length (allbytes ++ a7) = roundup newlen valubytes)
      as Hallbytes'len.
     rewrite app_length.
     replace (length a7).
     unfold alloc_items.
     rewrite block_items_ok.
     replace (length allbytes).
     fold (roundup (filelen f) valubytes).
     omega.
     rewrite skipn_length.
     omega.
     omega.
     fold (filelen f).
     omega.

     step.
     step. (* 15s *)
     apply pimpl_or_r; right.
     cancel.
     fold (filelen f) in *.
     rewrite wordToNat_natToWord_idempotent'; auto.
     exists (firstn (filelen f) allbytes ++
      repeat $0 (roundup newlen valubytes - filelen f)).
     assert (ilist' =
      firstn (filelen f) allbytes ++
      repeat $ (0) (roundup newlen valubytes - filelen f)) as Hilist'.
     eapply pimpl_apply in H25.
     eapply list2nmem_array_eq in H25.
     replace ilist'.
     reflexivity.
     rewrite Rec.of_word_zero_list.
     replace (@Rec.of_word byte_type $0) with
      (natToWord 8 0) by reflexivity.
     apply arrayN_combine.
     rewrite firstn_length_l by auto.
     reflexivity.
     fold (roundup newlen valubytes).
     autorewrite with lengths.
     rewrite Hlen_all_min.
     rewrite <- Hilist'.
     intuition.

     apply wordToNat_natToWord_idempotent'.
     replace (filelen f + (roundup newlen valubytes - filelen f))
      with (length ilist').
     eapply goodSize_bound.
     eapply BFileRec.bfrec_bound with (itemtype := byte_type); eauto.
     replace ilist'.
     autorewrite with lengths.
     omega.
     replace ilist'.
     (* split repeat into two parts - those that bring the length up to newlen,
        and then the rest that make it roundup newlen *)
     replace (roundup newlen valubytes - filelen f) with
      (newlen - filelen f + (roundup newlen valubytes - newlen)) by omega.
     rewrite <- repeat_app.
     rewrite app_assoc.
     rewrite firstn_app_l by (autorewrite with lengths; omega).
     rewrite firstn_oob by (autorewrite with lengths; omega).
     reflexivity.

     step.
     step.

     assert (filelen f = newlen) as Hflen.
     case_eq (wlt_dec (INODE.ISize (BFILE.BFAttr f)) ($ (newlen))); intros.
     contradiction.
     assert (filelen f >= newlen).
     erewrite <- wordToNat_natToWord_idempotent'; eauto.
     unfold filelen.
     apply le_word_le_nat.
     rewrite natToWord_wordToNat.
     auto.
     omega.
     apply pimpl_or_r; right.
     cancel.
     unfold filelen.
     rewrite natToWord_wordToNat.
     instantiate (fdata' := (BFILE.BFData f)).
     destruct f.
     destruct BFAttr.
     auto.
     exists allbytes.
     fold (filelen f).
     rewrite minus_diag.
     simpl.
     rewrite app_nil_r.
     rewrite wordToNat_natToWord_idempotent'
      with (n := filelen f) by auto.
     auto.

   Grab Existential Variables.
   all: try exact nil.
   all: try exact emp.
   exact BFILE.bfile0.
  Qed.

  Hint Extern 1 ({{_}} progseq (grow_file _ _ _ _) _) => apply grow_file_ok : prog.


  Lemma bounds_firstn : forall A (l : list A) n nbits,
    # (natToWord nbits (length l)) = length l ->
    # (natToWord nbits (length (firstn n l))) = length (firstn n l).
  Proof.
    intros.
    erewrite wordToNat_natToWord_bound; auto.
    rewrite firstn_length.
    eapply le_trans. apply Nat.le_min_r.
    rewrite <- H. constructor.
  Qed.

  Hint Resolve bounds_firstn.

  Definition shrink_file T fsxp inum newlen mscs rx : prog T :=
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    let^ (mscs, ok) <- bf_shrink items_per_valu fsxp inum newlen mscs;
    If (bool_dec ok true) {
      mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                              (INODE.Build_iattr ($ newlen)
                                                 (INODE.IMTime oldattr)
                                                 (INODE.IType oldattr)
                                                 (INODE.IDev oldattr)) mscs;
      rx ^(mscs, true)
    } else {
      rx ^(mscs, false)
    }.

  Theorem shrink_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes attr,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes attr f ]] *
           [[ goodSize addrlen newlen ]] *
           [[ newlen <= filelen f ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' fdata' fattr',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ bytes' = firstn newlen bytes ]] *
           [[ rep bytes' attr f' ]] *
           [[ fattr' = INODE.Build_iattr ($ newlen) f.(BFILE.BFAttr).(INODE.IMTime) f.(BFILE.BFAttr).(INODE.IType) f.(BFILE.BFAttr).(INODE.IDev) ]] *
           [[ f' = BFILE.Build_bfile fdata' fattr' ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} shrink_file fsxp inum newlen mscs.
  Proof.
    unfold shrink_file, rep, bytes_rep.
    step.
    step.

    apply list2nmem_arrayN_firstn_skipn.

    assert (kept_items items_per_valu newlen <= length allbytes).
    unfold kept_items. eapply le_trans. apply roundup_mono. eauto.
    unfold filelen. rewrite block_items_ok.
    eapply le_trans. apply roundup_mono. apply le_n.
    unfold roundup. apply Nat.eq_le_incl. auto.

    rewrite skipn_length by assumption.
    rewrite Nat.sub_add by assumption; auto.
    step.
    step.
    step.
    step.
    step.
    apply pimpl_or_r. right. cancel.
    eexists; intuition.
    eassumption.

    eauto.

    unfold filelen in *.
    erewrite wordToNat_natToWord_bound by eauto.
    repeat rewrite firstn_firstn.
    repeat rewrite Nat.min_l; auto.
    apply roundup_ge. rewrite block_items_ok. rewrite valubytes_is; omega.

    erewrite wordToNat_natToWord_bound by eauto.
    rewrite firstn_firstn.
    rewrite Nat.min_l; auto.
    rewrite firstn_length.
    rewrite Nat.min_l; auto.
    unfold filelen in *.
    eapply le_trans. eauto.
    rewrite <- H10. apply divup_ok.

    erewrite wordToNat_natToWord_bound by eauto.
    rewrite block_items_ok.
    rewrite firstn_length. rewrite Nat.min_l. auto.
    fold byte. rewrite <- H10. apply roundup_mono. auto.

    step.

    Grab Existential Variables.
    all: eauto.
    (* XXX where did this leak from? *)
    exact (FSXPBlockAlloc fsxp).
  Qed.

  Hint Extern 1 ({{_}} progseq (shrink_file _ _ _ _) _) => apply shrink_file_ok : prog.


  Lemma rep_length : forall bytes attr f,
    rep bytes attr f ->
    length bytes = (# (f.(BFILE.BFAttr).(INODE.ISize))).
  Proof.
    unfold rep. intuition deex.
  Qed.

  Lemma ge_minus_zero : forall b a,
    a >= b -> b - a = 0.
  Proof.
    induction b; simpl; intros; auto.
    destruct a; omega.
  Qed.

  Definition resize_file T fsxp inum newlen mscs rx : prog T :=
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    let oldlen := oldattr.(INODE.ISize) in
    If (wlt_dec oldlen ($ newlen)) {
      let^ (mscs, ok) <- grow_file fsxp inum newlen mscs;
      rx ^(mscs, ok)
    } else {
      let^ (mscs, ok) <- shrink_file fsxp inum newlen mscs;
      rx ^(mscs, ok)
    }.

  Theorem resize_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes attr,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes attr f ]] *
           [[ goodSize addrlen newlen ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' fdata' fattr',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ bytes' = firstn newlen bytes ++ (repeat $0 (newlen - length bytes)) ]] *
           [[ rep bytes' attr f' ]] *
           [[ fattr' = INODE.Build_iattr ($ newlen) f.(BFILE.BFAttr).(INODE.IMTime) f.(BFILE.BFAttr).(INODE.IType) f.(BFILE.BFAttr).(INODE.IDev) ]] *
           [[ f' = BFILE.Build_bfile fdata' fattr' ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} resize_file fsxp inum newlen mscs.
  Proof.
    unfold resize_file.
    step.
    step.
    step.
    apply Nat.lt_le_incl.
    apply wlt_lt in H9.
    rewrite wordToNat_natToWord_idempotent' in H9 by auto.
    apply H9.
    step.
    apply pimpl_or_r; right. cancel.

    erewrite rep_length by eauto.
    rewrite firstn_oob; auto.
    erewrite rep_length by eauto.
    apply wlt_lt in H9. rewrite wordToNat_natToWord_idempotent' in H9 by auto. omega.

    step.
    apply wge_ge in H9.
    rewrite wordToNat_natToWord_idempotent' in H9 by auto.
    eauto.
    step.
    apply pimpl_or_r; right. cancel.

    apply wge_ge in H9. rewrite wordToNat_natToWord_idempotent' in H9 by auto.

    erewrite rep_length by eauto.
    rewrite ge_minus_zero by auto. simpl. rewrite app_nil_r; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (resize_file _ _ _ _) _) => apply resize_file_ok : prog.


  (** Write bytes follows POSIX, which is overloaded to do two things:
  (1) if the write falls within the bounds of the file, update those bytes
  (2) otherwise, grow the file and update the new file (any grown bytes not
  updated are zeroed).

  We provide APIs for the two cases with separate specs: [update_bytes]
  and [overwrite_append]. *)
  Definition write_bytes T fsxp inum (off : nat) len (data : bytes len) mscs rx : prog T :=
    let newlen := off + len in
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode)
      inum mscs;
    let curlen := oldattr.(INODE.ISize) in
    (* should we grow the file? *)
    mscs <- IfRx irx (wlt_dec curlen ($ newlen)) {
      let^ (mscs, ok) <- grow_file fsxp inum newlen mscs;
      If (bool_dec ok true) {
        irx mscs
      } else {
        rx ^(mscs, false)
      }
    } else {
      irx mscs
    };
    let^ (mscs) <- update_bytes fsxp inum off data mscs;
    rx ^(mscs, true).

  (** Case (2) of [write_bytes] above, where the file must be grown.

  This is an alias for [write_bytes] since [write_bytes] already handles
  all the cases, but has its own idiosyncratic spec. *)
  Definition append T fsxp inum (off:nat) len (data : bytes len) mscs rx : prog T :=
    write_bytes fsxp inum off data mscs rx.

  Theorem append_ok: forall fsxp inum (off:nat) len (newbytes: bytes len) mscs,
    {< m mbase F Fm Fi A flist f bytes attr,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes attr f ]] *
           [[ Fi (list2nmem bytes) ]] *
           [[ goodSize addrlen (off + len) ]] *
           (* makes this an append *)
           [[ filelen f <= off ]]
       POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' zeros,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' attr f' ]] *
           [[ let newdata := @Rec.of_word (Rec.ArrayF byte_type len) newbytes in
              (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
           [[ zeros = arrayN (filelen f) (repeat $0 (off - (filelen f))) ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} append fsxp inum off newbytes mscs.
  Proof.
    unfold append, write_bytes.
    step. (* 50s *)
    inversion H7 as [allbytes Hrepconj].
    inversion Hrepconj as [Hbytes_rep Hrepconj']; clear Hrepconj.
    inversion Hrepconj' as [Hbytes Hrepconj'']; clear Hrepconj'.
    inversion Hrepconj'' as [Hbyteslen Hallbyteslen]; clear Hrepconj''.
    inversion Hbytes_rep as [Hrecrep Hallbytes_goodSize].
    fold (filelen f) in *.
    assert (filelen f <= length allbytes).
    rewrite <- Hallbyteslen.
    apply roundup_valu_ge.

    step.
    step. (* 10s *)

    unfold filelen.
    auto.

    step.
    step. (* 165s -> 7.5s !!! *)
    step.
    step. (* 165s -> 13s *)

    instantiate (Fx0 := (Fi * arrayN (filelen f) (repeat $0 (off - filelen f)))%pred).
    instantiate (olddata0 := repeat $0 len).
    fold (filelen f) in *.
    eapply pimpl_apply with (p := (Fi *
      arrayN (filelen f) (repeat $0 (off + len - filelen f)))%pred).
    cancel.
    replace (off + len - filelen f) with (off - filelen f + len) by omega.
    rewrite <- repeat_app.
    apply arrayN_combine.
    rewrite repeat_length.
    omega.
    replace (filelen f) at 1.
    apply list2nmem_arrayN_app.
    auto.

    autorewrite with lengths.
    reflexivity.

    step. (* 15s *)
    step.
    (* just the first part of step *)
    eapply pimpl_ok2; eauto with prog.
    intros; norm; [cancel|].
    subst.
    (* we derive len = 0 before step creates several subgoals. *)
    assert (filelen f >= off + len).
    apply not_wlt_ge in H15.
    apply le_word_le_nat'; auto.
    assert (len = 0) by omega.
    subst len.
    intuition; eauto.
    instantiate (Fx0 := Fi).
    instantiate (olddata0 := nil).
    pred_apply; cancel.
    auto.

    step.
    eapply pimpl_or_r; right; cancel; eauto.
    (* there are no zeroes, since we're appending nothing *)
    replace (off - filelen f) with 0 by omega.
    pred_apply; cancel.

    Grab Existential Variables.
    all: auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (append _ _ _ _ _) _) => apply append_ok : prog.

  Definition getlen T fsxp inum mscs rx : prog T :=
    let^ (mscs, attr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, INODE.ISize attr).

  Theorem getlen_ok: forall fsxp inum mscs,
    {< m mbase F Fm A flist f bytes attr,
    PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ rep bytes attr f ]]
    POST RET: ^(mscs, len)
         LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
         [[ len = $ (length bytes) ]]
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} getlen fsxp inum mscs.
  Proof.
    unfold getlen.
    step.
    step.
    erewrite rep_length by eauto.
    rewrite natToWord_wordToNat.
    congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (getlen _ _ _) _) => apply getlen_ok : prog.


  Definition getattr T fsxp inum mscs rx : prog T :=
    let^ (mscs, attr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    rx ^(mscs, Build_bytefile_attr attr.(INODE.IMTime) attr.(INODE.IType) attr.(INODE.IDev)).

  Lemma rep_attr : forall bytes attr f,
    rep bytes attr f ->
    attr = Build_bytefile_attr f.(BFILE.BFAttr).(INODE.IMTime)
                               f.(BFILE.BFAttr).(INODE.IType)
                               f.(BFILE.BFAttr).(INODE.IDev).
  Proof.
    unfold rep. intuition deex.
    destruct attr; simpl in *.
    congruence.
  Qed.

  Theorem getattr_ok: forall fsxp inum mscs,
    {< m mbase F Fm A flist f bytes attr,
    PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ rep bytes attr f ]]
    POST RET: ^(mscs, a)
         LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
         [[ a = attr ]]
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} getattr fsxp inum mscs.
  Proof.
    unfold getattr.
    step.
    step.
    erewrite rep_attr by eauto; congruence.
  Qed.

  Hint Extern 1 ({{_}} progseq (getattr _ _ _) _) => apply getattr_ok : prog.


  Definition setattr T fsxp inum newattr mscs rx : prog T :=
    let^ (mscs, iattr) <- BFILE.bfgetattr (FSXPLog fsxp) (FSXPInode fsxp) inum mscs;
    mscs <- BFILE.bfsetattr (FSXPLog fsxp) (FSXPInode fsxp) inum
            (INODE.Build_iattr iattr.(INODE.ISize)
                               newattr.(FMTime) newattr.(FType) newattr.(FDev))
            mscs;
    rx mscs.

  Theorem setattr_ok: forall fsxp inum newattr mscs,
    {< m mbase F Fm A flist f bytes attr,
    PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
        [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
        [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
        [[ rep bytes attr f ]]
    POST RET: mscs
         exists m' flist' f',
         LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
         [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
         [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
         [[ rep bytes newattr f' ]]
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
    >} setattr fsxp inum newattr mscs.
  Proof.
    unfold setattr.
    step.
    step.
    step.
    unfold rep in *; repeat deex; simpl.
    eexists.
    intuition eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (setattr _ _ _ _) _) => apply setattr_ok : prog.


  Theorem rep_unique : forall bytes1 bytes2 attr1 attr2 bf,
    rep bytes1 attr1 bf -> rep bytes2 attr2 bf -> bytes1 = bytes2 /\ attr1 = attr2.
  Proof.
    unfold rep, bytes_rep; intros.
    repeat deex.
    pose proof (array_item_file_eq H0 H); congruence.
    destruct attr1; destruct attr2; simpl in *; congruence.
  Qed.

End BYTEFILE.
