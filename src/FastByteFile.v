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
[byte count]s rather than [list byte]s as inputs.

tchajed: This is a copy of SlowByteFile that I'm in the process of making fast.
*)
Module FASTBYTEFILE.

  Definition byte_type := Rec.WordF 8.
  Definition itemsz := Rec.len byte_type.
  Definition items_per_valu : addr := $ valubytes.
  Theorem itemsz_ok : valulen = wordToNat items_per_valu * itemsz.
  Proof.
    unfold items_per_valu.
    rewrite valulen_is, valubytes_is.
    reflexivity.
  Qed.

  (* The bytes of a file are mapped onto a list of blocks:   *)
  (*   [ block 0 ... block n]                                *)
  (*   <-- allbytes      -->                                 *)
  (*   <-- bytes     -->                                     *)

  Definition bytes_rep f (allbytes : list byte) :=
    BFileRec.array_item_file byte_type items_per_valu itemsz_ok f allbytes /\
    # (natToWord addrlen (length allbytes)) = length allbytes.

  Definition rep (bytes : list byte) (f : BFILE.bfile) :=
    exists allbytes,
    bytes_rep f allbytes /\
    firstn (# (f.(BFILE.BFAttr).(INODE.ISize))) allbytes = bytes /\
    length bytes = (# (f.(BFILE.BFAttr).(INODE.ISize))) /\
    divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes.

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
    let^ (mscs) <- BFileRec.bf_update_range items_per_valu itemsz_ok
      fsxp inum off newbytes mscs;
    rx ^(mscs).

  Definition read_byte T fsxp inum (off:nat) mscs rx : prog T :=
  let^ (mscs, b) <- BFileRec.bf_get byte_type items_per_valu itemsz_ok
     fsxp.(FSXPLog) fsxp.(FSXPInode) inum ($ off) mscs;
     rx ^(mscs, b).

  Definition read_bytes T fsxp inum (off:nat) len mscs rx : prog T :=
    let^ (mscs, databytes) <- For i < len
      Ghost [ m mbase F Fm A f flist bytes ]
      Loopvar [ mscs l ]
      Continuation lrx
      Invariant
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m) mscs *
          [[ (Fm * BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ rep bytes f ]] *
          [[ l = firstn #i (skipn off bytes) ]]
     OnCrash
      exists m',
        LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
     Begin
      let^ (mscs, b) <- BFileRec.bf_get byte_type items_per_valu itemsz_ok
        fsxp.(FSXPLog) fsxp.(FSXPInode) inum ($ (off + #i)) mscs;
      lrx ^(mscs, l ++ [b])
    Rof ^(mscs, nil);
    rx ^(mscs, databytes).

  Theorem read_byte_ok: forall fsxp inum off mscs,
    {< m mbase F Fx Fm A flist f bytes v,
    PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
          [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
          [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
          [[ rep bytes f ]] *
          [[ (Fx * off |-> v)%pred (list2nmem bytes) ]]
    POST RET:^(mscs, b)
          LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
          [[ b = v ]]
    CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} read_byte fsxp inum off mscs.
  Proof.
    unfold read_byte.
    unfold rep, bytes_rep.
    step.
    apply list2nmem_ptsto_bound in H4.
    rewrite firstn_length in H4.
    apply Nat.min_glb_lt_iff in H4. destruct H4.
    erewrite wordToNat_natToWord_bound.
    assumption.
    apply Nat.lt_le_incl. eassumption.
    step.
    Search ptsto list2nmem selN.
    eapply list2nmem_sel in H4 as H4'.

    apply list2nmem_ptsto_bound in H4.
    rewrite firstn_length in H4.
    Search lt Init.Nat.min.
    apply Nat.min_glb_lt_iff in H4. destruct H4.

    rewrite selN_firstn in H4' by eauto.
    unfold sel in H13.
    erewrite wordToNat_natToWord_bound in H13.
    rewrite H13.
    rewrite H4'.
    reflexivity.
    apply Nat.lt_le_incl. eassumption.
  Qed.

  Theorem read_bytes_ok: forall fsxp inum off len mscs,
  {< m mbase F Fx Fm A flist f bytes v,
  PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
      [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
      [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
      [[ rep bytes f ]] *
      [[ length v = #len ]] *
      [[ (Fx * arrayN off v)%pred (list2nmem bytes) ]] *
      [[ off + #len <= length bytes ]]
   POST RET:^(mscs, databytes)
      LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
      [[ databytes = v ]]
   CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
   >} read_bytes fsxp inum off len mscs.
   Proof.
    unfold read_bytes, rep, bytes_rep.

    step. (* enter loop *)
    exists allbytes.
    split;  auto.

    step. (* bf_get *)
    (* we assert and prove this lemma first because it is used twice *)
    assert (Hoffm1: off + #(m1) < length allbytes0).
      (* without the bounds checking, this proof goes:
      m1 < off -> m1 < len
      -> off + m1 < off + len
      off + len < min( f.isize, length allbytes ) (firstn_length)
      length allbytes0 >= f.isize (from divup_ok)
      -> off + len < f.isize <= length allbytes0
      -> off + m1 < length allbytes0 *)
    apply le_trans with (off + #(len)).
    apply plus_lt_compat_l. apply wlt_lt. assumption.
    rewrite firstn_length in H4.
    apply Nat.min_glb_l in H4.
    apply le_trans with (# (INODE.ISize (BFILE.BFAttr f))). assumption.
    rewrite <- H22.
    apply divup_ok.
    erewrite wordToNat_natToWord_bound.
    apply Hoffm1.
    instantiate (bound := $ (length allbytes0)).
    rewrite H20.
    omega.

    step.
    exists allbytes; split; auto.
    subst.
      (* same charade as above *)
      assert (Hoffm1: off + #(m1) < #(INODE.ISize (BFILE.BFAttr f))).
      rewrite firstn_length in H4.
      apply Nat.min_glb_l in H4.
      apply le_trans with (off + #(len)).
      apply plus_lt_compat_l. apply wlt_lt. assumption.
      assumption.
    replace (# (m1 ^+ $ (1))) with (# (m1) + 1).
    erewrite firstn_plusone_selN.
    f_equal.
    f_equal.
    rewrite <- H16.
    unfold sel.

    erewrite wordToNat_natToWord_bound.
    apply selN_skip_first.
    apply Hoffm1.
    apply Nat.lt_le_incl.
    eassumption.
    rewrite skipn_length.
    apply Nat.lt_add_lt_sub_r.
    rewrite plus_comm.
    rewrite H18.
    apply Hoffm1.
    rewrite H18.
    omega.
    (* need to convert ^+ $(1) to +1 using bounds *)
      rewrite wplus_alt.
      unfold wplusN, wordBinN.
      simpl.
      erewrite wordToNat_natToWord_bound.
      reflexivity.
      (* same as H3, after some massaging *)
      apply wlt_lt in H3.
      unfold lt in H3.
      instantiate (bound := len).
      replace (# (m1) + 1) with (S # (m1)) by omega.
      eassumption.
    step.

    apply arrayN_list2nmem in H5.
    symmetry.
    rewrite <- H6.
    apply H5.
    (* Using arrayN_list2nmem requires a default value, which is never used,
        so we have to provide some value of type byte.
        This is seems like a bug in arrayN_list2nmem. *)
    apply ($ 0).

    apply LOG.activetxn_would_recover_old.

    Grab Existential Variables.
    exact tt.
  Qed.

  Theorem update_bytes_ok: forall fsxp inum off len (newbytes : bytes len) mscs,
      {< m mbase F Fm A flist f bytes olddata Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]] *
           [[ length olddata = len ]] *
           [[ 0 < len ]]
      POST RET: ^(mscs)
           exists m' flist' f' bytes',
           LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ let newdata := @Rec.of_word (Rec.ArrayF byte_type len) newbytes in
              (Fx * arrayN off newdata)%pred (list2nmem bytes') ]] *
           [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]]
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} update_bytes fsxp inum off newbytes mscs.
  Proof.
    unfold update_bytes.

    intros.
    eapply pimpl_ok2.
    apply bf_update_range_ok with (fsxp:=fsxp) (inum:=inum) (off:=off) (w:=newbytes).
    intros; subst.
    time norm'l. (* 40s *)

    (* we've manually done what [step] does so that we can invert the
       rep function before evars are created, so that the allbytes created
       can be used to instantiate the evars. *)
    inversion H7 as [allbytes].
    inversion H0; clear H0.
    inversion H3.
    set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.
    time norm. (* 15s *)
    cancel.
    intuition; eauto.
    - Transparent hidden.
      unfold hidden in *.

      instantiate (Fx0 := (Fx * arrayN flen
        (skipn flen allbytes))%pred).
      rewrite <- firstn_skipn with (l := allbytes) (n := flen) at 2.
      replace (firstn flen allbytes).
      replace flen with (length bytes) at 1.
      apply list2nmem_arrayN_app with (l' := skipn flen allbytes) in H6.
      pred_apply; cancel.
      cancel.
    - reflexivity.
    - rewrite Rec.array_of_word_length with (ft := byte_type).
      auto.
    - Transparent BFileRec.hidden.
      unfold BFileRec.hidden in *.
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
        apply firstn_length_l_iff in H9.
        set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.
        fold flen.
        match goal with
        | [ H : _ (list2nmem ilist') |- _ ] => rename H into Hilist'
        end.
        rewrite <- firstn_skipn with (l := ilist') (n := flen) in Hilist'.
        assert (length (firstn flen ilist') = flen) as Hflen.
        apply firstn_length_l; omega.
        Lemma sep_star_abc_to_acb : forall AT AEQ AV (a b c : @pred AT AEQ AV),
          (a * b * c)%pred =p=> (a * c * b).
        Proof. cancel. Qed.
        eapply pimpl_apply in Hilist'; [|apply sep_star_abc_to_acb].
        rewrite <- Hflen in Hilist' at 1.
        assert (Htails_eq := Hilist').
        apply list2nmem_arrayN_end_eq in Htails_eq; auto.
        rewrite Htails_eq in Hilist'.
        apply list2nmem_arrayN_app_iff in Hilist'.
        assumption.
        exact ($ 0).
        autorewrite with lengths; omega.
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
                                                   (INODE.IType oldattr)) mscs;
        rx ^(mscs, true)
      } else {
        rx ^(mscs, false)
      }
    } else {
      rx ^(mscs, true)
    }.

  Definition filelen f := # (INODE.ISize (BFILE.BFAttr f)).

  Theorem grow_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ goodSize addrlen newlen ]] *
           (* spec requires that file is growing, so that it can guarantee
              that the new size of the file is $newlen. *)
           [[ filelen f <= newlen ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' fdata' attr,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ bytes' = (bytes ++ (repeat $0 (newlen -  (# (INODE.ISize (BFILE.BFAttr f)))))) ]] *
           [[ rep bytes' f']] *
           [[ attr = INODE.Build_iattr ($ newlen) (f.(BFILE.BFAttr).(INODE.IMTime)) (f.(BFILE.BFAttr).(INODE.IType))]] *
           [[ f' = BFILE.Build_bfile fdata' attr]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
     >} grow_file fsxp inum newlen mscs.
   Proof.
     unfold grow_file, rep, bytes_rep.
     time step. (* 30s *)
     step.
     time step. (* 10s *)

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
     time step. (* 60s *)
     step.

     time step. (* 80s *)
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
     time step. (* 15s *)
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

  Theorem write_bytes_ok: forall fsxp inum (off:nat) len (newbytes: bytes len) mscs,
    {< m mbase F Fm F1 F2 A flist f bytes newdata wend,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           (* write goes from off to wend in new file *)
           [[ wend = off + len ]] *
           [[ F1%pred (list2nmem (firstn off bytes)) ]] *
           [[ F2%pred (list2nmem (skipn wend bytes)) ]] *
           [[ goodSize addrlen wend ]]
       POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' zeros,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ newdata = bsplit_list newbytes ]] *
           [[ (F1 * zeros * arrayN off newdata * F2)%pred (list2nmem bytes')]] *
           [[ zeros = arrayN len (repeat $0 (off - len)) ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} write_bytes fsxp inum off newbytes mscs.
  Proof.
    unfold write_bytes.
  Admitted.

  Hint Extern 1 ({{_}} progseq (write_bytes _ _ _ _ _) _) => apply write_bytes_ok : prog.

  Theorem append_ok: forall fsxp inum (off:nat) len (newbytes: bytes len) mscs,
    {< m mbase F Fm Fi A flist f bytes,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ Fi%pred (list2nmem bytes) ]] *
           [[ goodSize addrlen (off + len) ]] *
           (* makes this an append *)
           [[ filelen f <= off ]] *
           [[ len > 0 ]]
       POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' zeros,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ let newdata := @Rec.of_word (Rec.ArrayF byte_type len) newbytes in
              (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
           [[ zeros = arrayN (filelen f) (repeat $0 (off - (filelen f))) ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} append fsxp inum off newbytes mscs.
  Proof.
    unfold append, write_bytes.
    time step. (* 50s *)
    inversion H8 as [allbytes].
    inversion H; clear H.
    inversion H10; clear H10.
    inversion H11; clear H11.
    inversion H0.
    fold (filelen f) in *.
    assert (filelen f <= length allbytes).
    rewrite <- H12.
    apply roundup_valu_ge.

    step.
    time step. (* 10s *)

    unfold filelen.
    auto.

    step.
    time step. (* 165s -> 7.5s !!! *)
    step.
    time step. (* 165s -> 13s *)

    unfold hidden.
    fold (filelen f) in *.
    instantiate (Fx0 := (Fi * arrayN (filelen f) (repeat $0 (off - filelen f)))%pred).
    instantiate (olddata0 := repeat $0 len).
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

    time step. (* 15s *)
    step.
    (* just the first part of step *)
    eapply pimpl_ok2; eauto with prog.
    intros; norm; [cancel|].
    subst.
    (* We will derive a contradiction with len > 0, since
       filelen f <= off + len forces a zero-length write.
       Doing so before intuition prevents several subgoals with
       contradictory hypotheses. *)
    assert (filelen f >= off + len).
    apply not_wlt_ge in H21.
    apply le_word_le_nat'; auto.
    replace len with 0 in H4 by omega.
    inversion H4.

    Grab Existential Variables.
    all: try exact emp.
    all: try exact BFILE.bfile0.
    all: exact nil.
  Qed.

  Hint Extern 1 ({{_}} progseq (append _ _ _ _ _) _) => apply append_ok : prog.

End FASTBYTEFILE.
