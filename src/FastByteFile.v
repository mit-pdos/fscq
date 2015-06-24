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

  Fixpoint apply_bytes (allbytes : list byte) (off : nat) (newdata : list byte) :=
    match newdata with
    | nil => allbytes
    | b :: rest => updN (apply_bytes allbytes (off+1) rest) off b
    end.

  Lemma apply_bytes_length : forall newdata allbytes off,
    length (apply_bytes allbytes off newdata) = length allbytes.
  Proof.
    induction newdata; simpl; intros; auto.
    rewrite length_updN. eauto.
  Qed.

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

  Lemma bound_helper : forall a b,
    # (natToWord addrlen b) = b -> a <= b -> a <= # (natToWord addrlen b).
  Proof.
    intuition.
  Qed.

  Lemma boff_le_length : forall T boff (l l' : list T) off x y z q,
    off + x = boff + S z ->
    off + y <= length (firstn q l') ->
    hidden (length l' = length l) ->
    x = y ->
    boff + 1 <= length l.
  Proof.
    intros.
    subst.
    rewrite firstn_length in *.
    eapply le_trans. eapply le_trans; [ | apply H0 ].
    omega.
    rewrite H1.
    apply Min.le_min_r.
  Qed.

  Lemma le_lt_S : forall a b,
    a + 1 <= b ->
    a < b.
  Proof.
    intros; omega.
  Qed.

  Hint Resolve bound_helper.
  Hint Resolve boff_le_length.
  Hint Resolve le_lt_S.

  Lemma apply_bytes_arrayN : forall olddata newdata oldbytes newbytes off F x,
    newbytes = apply_bytes oldbytes off newdata ->
    length newdata = length olddata ->
    (F * arrayN off olddata)%pred (list2nmem (firstn x oldbytes)) ->
    (F * arrayN off newdata)%pred (list2nmem (firstn x newbytes)).
  Proof.
    induction olddata; simpl; intros.
    - destruct newdata; simpl in *; try omega.
      congruence.
    - destruct newdata; simpl in *; try omega.
      subst.
      rewrite updN_firstn_comm.
      rewrite listupd_progupd.
      apply sep_star_comm. apply sep_star_assoc.
      eapply ptsto_upd.
      apply sep_star_assoc. apply sep_star_comm. apply sep_star_assoc.
      replace (off + 1) with (S off) by omega.
      eapply IHolddata; eauto.
      apply sep_star_assoc. apply H1.

      rewrite firstn_length.
      rewrite apply_bytes_length.
      apply sep_star_assoc in H1. apply sep_star_comm in H1. apply sep_star_assoc in H1.
      apply list2nmem_ptsto_bound in H1. rewrite firstn_length in H1. auto.
  Qed.


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
      {< m mbase F Fm A flist f bytes olddata newdata Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ hidden ((Fx * arrayN off olddata)%pred (list2nmem bytes)) ]] *
           [[ hidden (newdata = @Rec.of_word (Rec.ArrayF byte_type len) newbytes) ]] *
           [[ hidden (length olddata = length newdata) ]] *
           [[ 0 < len ]]
      POST RET: ^(mscs)
           exists m' flist' f' bytes',
           LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ (Fx * arrayN off newdata)%pred (list2nmem bytes') ]] *
           [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]]
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} update_bytes fsxp inum off newbytes mscs.
  Proof.
    unfold update_bytes.

    intros.
    eapply pimpl_ok2.
    apply bf_update_range_ok.
    intros; subst.
    time norm'l.

    (* we've manually done what [step] does so that we can invert the
       rep function before evars are created, so that the allbytes created
       can be used to instantiate the evars. *)
    inversion H8 as [allbytes].
    inversion H.
    inversion H0.
    set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.
    norm.
    cancel.
    intuition; eauto.
    - Transparent hidden.
      unfold hidden in *.

      rewrite <- H in H7.
      instantiate (Fx0 := (Fx * arrayN flen
        (skipn flen allbytes))%pred).
      rewrite <- firstn_skipn with (l := allbytes) (n := flen) at 2.
      replace (firstn flen allbytes).
      replace flen with (length bytes) at 1.
      replace (firstn flen allbytes) in H7.
      apply list2nmem_arrayN_app with (l' := skipn flen allbytes) in H7.
      pred_apply; cancel.
      cancel.
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
        set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.
        fold flen.
        rewrite <- firstn_skipn with (l := ilist') (n := flen) in H25.
        assert (length (firstn flen ilist') = flen).
        apply firstn_length_l.
        apply firstn_length_l_iff in H14.
        omega.
        assert ((Fx * arrayN off newdata * arrayN flen (skipn flen allbytes))%pred
          (list2nmem (firstn flen ilist' ++ skipn flen ilist'))).
        pred_apply; cancel.
        rewrite <- H16 in H21 at 1.
        assert (H21' := H21).
        apply list2nmem_arrayN_end_eq in H21'; auto.
        rewrite H21' in H21.
        apply list2nmem_arrayN_app_iff in H21.
        assumption.
        exact ($ 0).
        apply firstn_length_l_iff in H14.
        repeat rewrite skipn_length; omega.
  Qed.

  Hint Extern 1 ({{_}} progseq (update_bytes _ _ _ _ _) _) => apply update_bytes_ok : prog.

  Definition grow_blocks T fsxp inum nblock mscs rx : prog T :=
    let^ (mscs) <- For i < nblock
      Ghost [ mbase F Fm A f bytes ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant
      exists m' flist f',
         LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs  *
          [[ (Fm * BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) flist)%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist) ]] *
          [[ bytes_rep f' (bytes ++ (repeat $0 (#i * valubytes)))  ]] *
          [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]]
      OnCrash
        exists m',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
      Begin
       let^ (mscs, n) <- BFileRec.bf_getlen items_per_valu fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
       If (wlt_dec n (natToWord addrlen INODE.blocks_per_inode ^* items_per_valu)) {
         let^ (mscs, ok) <- BFileRec.bf_extend byte_type items_per_valu itemsz_ok fsxp.(FSXPLog) fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) inum $0 mscs;
         If (bool_dec ok true) {
           lrx ^(mscs)
         } else {
           rx ^(mscs, false)
         }
       } else {
         rx ^(mscs, false)
       }
    Rof ^(mscs);
    rx ^(mscs, true).

  Lemma item0_upd:
    (upd (item0_list byte_type items_per_valu itemsz_ok) $0 $0) = repeat $0 valubytes.
  Proof.
    rewrite BFileRec.item0_list_repeat.
    unfold items_per_valu. replace (# ($ valubytes)) with (valubytes).
    destruct valubytes; reflexivity.
    rewrite valubytes_is; reflexivity.
  Qed.

  Lemma natplus1_wordplus1_eq:
    forall (a:addr) (bound:addr),
      (a < bound)%word ->
      # (a) + 1 = # (a ^+ $ (1)).
  Proof.
    intros.
    rewrite wplus_alt. unfold wplusN, wordBinN. simpl.
    erewrite wordToNat_natToWord_bound. reflexivity.
    apply wlt_lt in H.
    instantiate (bound:=bound). omega.
  Qed.

  Lemma bytes_grow_oneblock_ok:
    forall bytes nblock f (bound:addr),
    (nblock < bound) % word ->
    array_item_file byte_type items_per_valu itemsz_ok f
       ((bytes ++ repeat $ (0) (@wordToNat addrlen (nblock) * valubytes)) ++
        (upd (item0_list byte_type items_per_valu itemsz_ok) $0 $0)) ->
    array_item_file byte_type items_per_valu itemsz_ok f
       (bytes ++ repeat $ (0) (@wordToNat addrlen (nblock ^+ $ (1)) * valubytes)).
  Proof.
    intros.
    pose proof item0_upd.
    rewrite  H1 in H0.
    rewrite <- app_assoc in H0.
    rewrite repeat_app in H0.
    replace (# (nblock ^+ $ (1)) * valubytes) with (# (nblock) * valubytes + valubytes).
    auto.

    replace (# (nblock ^+ $1)) with (#nblock + 1).
    rewrite Nat.mul_add_distr_r.
    omega.
    eapply natplus1_wordplus1_eq.
    instantiate (bound:=bound); eauto.
  Qed.


Hint Resolve bytes_grow_oneblock_ok.

  Lemma length_grow_oneblock_ok:
    forall (bytes: list byte) (nblock:addr) (bound:addr),
      (nblock < bound) % word ->
      ($ (length bytes + # (nblock) * valubytes) <
         $ (INODE.blocks_per_inode) ^* items_per_valu)%word ->
      @wordToNat addrlen ($ (length (bytes ++ repeat $ (0) (# (nblock) * valubytes)))) =
         length (bytes ++ repeat $ (0) (# (nblock) * valubytes))  ->
      @wordToNat addrlen ($ (length (bytes ++ repeat $ (0) (# (nblock ^+ $ (1)) * valubytes)))) =
      length (bytes ++ repeat $ (0) (# (nblock ^+ $ (1)) * valubytes)).
  Proof.
    intros.
    replace (# (nblock ^+ $1)) with (#nblock + 1).
    rewrite Nat.mul_add_distr_r.
    simpl.
    rewrite <- repeat_app.
    repeat rewrite app_length.
    repeat rewrite repeat_length.
    erewrite wordToNat_natToWord_bound. reflexivity.
    apply wlt_lt in H0.
    rewrite app_length in H1. rewrite repeat_length in H1. rewrite H1 in H0.
    instantiate (bound := $ (INODE.blocks_per_inode) ^* items_per_valu ^+ items_per_valu ^+ $1).
    unfold INODE.blocks_per_inode in *. unfold INODE.nr_direct, INODE.nr_indirect in *.
    unfold items_per_valu in *. rewrite valubytes_is. rewrite valubytes_is in H0.
    apply le_trans with (4097 + # ($ (12 + 512) ^* natToWord addrlen 4096)). omega.
    apply Nat.eq_le_incl.
    reflexivity.
    eapply natplus1_wordplus1_eq.
    instantiate (bound:=bound); eauto.
  Qed.

Hint Resolve length_grow_oneblock_ok.

  Theorem grow_blocks_ok: forall fsxp inum nblock mscs,
      {< m mbase F Fm flist f A bytes,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ bytes_rep f bytes ]]
      POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
            ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]] *
           [[ bytes_rep f' (bytes ++ (repeat $0 (# nblock * valubytes))) ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
       >} grow_blocks fsxp inum nblock mscs.
  Proof.
    unfold grow_blocks, rep, bytes_rep.
    step. (* step into loop *)
    rewrite app_nil_r.
    eauto.
    rewrite app_nil_r.
    eauto.
    constructor.
    step. (* getlen *)
    step. (* if *)
    step. (* bf_extend *)
    constructor.
    step. (* if statement *)
    step.
    step.
    (* true branch *)
    step.
    step.
    step.
    step.

    eapply pimpl_or_r; right; cancel.
    eauto.
    rewrite app_length in H18.
    eapply H18.
    apply LOG.activetxn_would_recover_old.

    Grab Existential Variables.
    all: eauto.
    exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (grow_blocks _ _ _ _) _) => apply grow_blocks_ok : prog.

   Definition grow_file T fsxp inum newlen mscs rx : prog T :=
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    let oldlen := oldattr.(INODE.ISize) in
    If (wlt_dec oldlen ($ newlen)) {
      let^ (mscs, ok) <- bf_expand items_per_valu fsxp inum newlen mscs;
      If (bool_dec ok true) {
        let^ (mscs) <- bf_update_range items_per_valu itemsz_ok
           fsxp inum #oldlen (@natToWord ((roundup newlen valubytes-#oldlen)*8) 0) mscs;
         mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                                (INODE.Build_iattr ($ newlen)
                                                   (INODE.IMTime oldattr)
                                                   (INODE.IType oldattr)) mscs;
        rx ^(mscs, true)
      } else {
        rx ^(mscs, false)
      }
    } else {
      (* TODO: this case is actually problematic,
         since the size of the new file is not newlen *)
      rx ^(mscs, true)
    }.


  Lemma nblock_ok:
    forall oldlen newlen boundary nblock,
      oldlen <= newlen ->
      boundary = (divup oldlen valubytes) * valubytes ->
      nblock = (divup newlen valubytes) - (divup oldlen valubytes)->
      newlen - oldlen <= boundary - oldlen + nblock * valubytes.
  Proof.
    intros; subst.
    rewrite Nat.mul_sub_distr_r.
    rewrite <- Nat.add_sub_swap by apply divup_ok.
    apply Nat.sub_le_mono_r.
    rewrite Nat.add_sub_assoc by ( apply le_roundup; omega ).
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by reflexivity.
    rewrite <- minus_diag_reverse.
    rewrite <- plus_n_O.
    apply divup_ok.
  Qed.

  (* layout is [0 .. oldlen ...0... boundary ... nblock 0s ... ) *)
  (*           <-- bytes-->                                        *)
  (*           <-------- allbytes-->                               *)
  (* newlen is larger than oldlen, and perhaps larger than boundary *)
  (* lemma says that extending bytes with 0s to newlen is the same as  *)
  (* extending allbytes with with nblock 0s and taking firstn newlen. *)
  Lemma eq_bytes_allbytes_ext0_to_newlen:
    forall (allbytes: list byte) (oldlen:nat) (newlen:nat) bytes nbytes nblock,
      oldlen <= newlen ->
      (divup oldlen valubytes) * valubytes = length allbytes ->
      bytes = firstn oldlen allbytes ->
      nbytes = (length allbytes) - oldlen ->
      nblock = (divup newlen valubytes) - (divup oldlen valubytes) ->
      firstn newlen ((bytes ++ (repeat $0 nbytes)) ++ repeat $0 (nblock * valubytes)) =
        (firstn oldlen allbytes) ++ (repeat $0 (newlen - oldlen)).
  Proof.
    intros.
    assert (length bytes = oldlen).
    subst. rewrite firstn_length. apply Nat.min_l.
    rewrite <- H0.
    apply divup_ok.
    rewrite <- app_assoc.
    rewrite firstn_app_le by omega.
    f_equal; auto.
    rewrite repeat_app.
    rewrite firstn_repeat_le.
    rewrite H4.
    eauto.
    rewrite H4.
    rewrite H2.
    apply nblock_ok; auto.
  Qed.

  Lemma grow_to_end_of_block_ok:
    forall f f' allbytes,
      array_item_file byte_type items_per_valu itemsz_ok f allbytes ->
      @wordToNat addrlen ($ (length allbytes)) = length allbytes ->
      divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes ->
      f' =
      {|
      BFILE.BFData := BFILE.BFData f;
      BFILE.BFAttr := {|
                      INODE.ISize := $
                                     (divup # (INODE.ISize (BFILE.BFAttr f))
                                        valubytes * valubytes);
                      INODE.IMTime := INODE.IMTime (BFILE.BFAttr f);
                      INODE.IType := INODE.IType (BFILE.BFAttr f) |} |} ->
      rep allbytes f'.
   Proof.
    intros.
    unfold rep, bytes_rep in *.
    eexists.
    instantiate (allbytes := allbytes).
    intuition eauto.
    unfold array_item_file in *.
    subst; simpl in *.
    eauto.
    rewrite H2.
    simpl.
    rewrite H1.
    rewrite firstn_oob; eauto.
    subst; simpl.
    rewrite H1.
    eauto.
    subst; simpl.
    erewrite wordToNat_natToWord_bound.
    rewrite divup_divup_eq with (x := # (INODE.ISize (BFILE.BFAttr f))).
    rewrite H1.
    instantiate (bound := $ ( (divup # (INODE.ISize (BFILE.BFAttr f)) valubytes) * valubytes)).
    eauto.
    rewrite H1.
    eauto.
  Qed.

  Hint Resolve grow_to_end_of_block_ok.


  Lemma olddata_exists_in_block:
        forall f (allbytes: list byte),
        divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes ->
        @wordToNat addrlen ($ (length allbytes)) = length allbytes ->
        (arrayN 0 (firstn # (INODE.ISize (BFILE.BFAttr f)) allbytes) *
          arrayN # (INODE.ISize (BFILE.BFAttr f))
           (skipn # (INODE.ISize (BFILE.BFAttr f)) allbytes))%pred (list2nmem allbytes).
  Proof.
       intros.
       replace (# (INODE.ISize (BFILE.BFAttr f))) with (0 + # (INODE.ISize (BFILE.BFAttr f))) at 2 by omega.
       apply arrayN_split.
       rewrite <- H.
       apply divup_ok.
       apply list2nmem_array.
  Qed.

  Hint Resolve olddata_exists_in_block.

  Lemma length_updatebytes_ok:
      forall f (allbytes: list byte),
        @wordToNat addrlen ($ (length allbytes)) = length allbytes ->
        divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes ->
          length (skipn (@wordToNat addrlen (INODE.ISize (BFILE.BFAttr f))) allbytes) =
          length (repeat (@natToWord addrlen 0) ((divup (@wordToNat addrlen (INODE.ISize (BFILE.BFAttr f))) valubytes) * valubytes
                                 - (@wordToNat addrlen (INODE.ISize (BFILE.BFAttr f))))).
  Proof.
      intros.
      rewrite skipn_length.
      rewrite repeat_length.
      eauto.
      rewrite <- H0.
      apply divup_ok.
  Qed.

  Hint Resolve length_updatebytes_ok.

  Lemma after_grow_to_block_bytes_rep_ok:
        forall f f' (bytes' : list byte) (allbytes: list byte),
          (arrayN 0 (firstn # (INODE.ISize (BFILE.BFAttr f)) allbytes) *
            arrayN # (INODE.ISize (BFILE.BFAttr f))
             (repeat $ (0)
                (divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes -
                    # (INODE.ISize (BFILE.BFAttr f)))))%pred (list2nmem bytes') ->
          divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes ->
          rep bytes' f' ->
          # (INODE.ISize (BFILE.BFAttr f')) = divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes ->
          bytes_rep f' ((firstn # (INODE.ISize (BFILE.BFAttr f)) allbytes) ++ (repeat $ (0)
            (divup # (INODE.ISize (BFILE.BFAttr f)) valubytes *
             valubytes - # (INODE.ISize (BFILE.BFAttr f))))).
  Proof.
       intros.
       unfold rep in *.
       destruct H1.
       intuition.
       apply arrayN_combine with (off := # (INODE.ISize (BFILE.BFAttr f))) in H.
       eapply list2nmem_array_eq in H.
       rewrite <- H4 in H1.
       rewrite firstn_oob in H1.
       rewrite H1 in H3.
       rewrite H in H3.
       assumption.
       rewrite <- H6.
       rewrite  H4.
       rewrite H2.
       rewrite divup_divup_eq.
       omega.
       rewrite firstn_length.
       rewrite Nat.min_l.
       eauto.
       rewrite <- H0.
       apply divup_ok.
  Qed.

  Lemma divup_newlen_minus_oldlen_goodSize:
    forall oldlen newlen a,
      newlen = @wordToNat addrlen a ->
      goodSize addrlen (divup newlen valubytes - divup oldlen valubytes).
  Proof.
    intros.
    unfold goodSize.
    apply lt_minus'.
    subst.
    apply divup_goodSize.
  Qed.


  Lemma len_oldlenext_newlen_eq:
    forall oldlen newlen,
      divup newlen valubytes * valubytes =
       oldlen + divup oldlen valubytes * valubytes - oldlen +
        divup newlen valubytes * valubytes -
        divup oldlen valubytes * valubytes.
  Proof.
    intros.
    rewrite minus_plus.
    rewrite minus_plus.
    eauto.
 Qed.

   Lemma after_grow_rep_ok:
      forall f f'' (bytes: list byte) (allbytes: list byte) newlen oldlen,
         divup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes ->
         newlen = # (INODE.ISize (BFILE.BFAttr f'')) ->
         oldlen = # (INODE.ISize (BFILE.BFAttr f)) ->
         oldlen <= newlen ->
         bytes_rep f'' ((firstn oldlen allbytes ++
          repeat $ (0) (divup oldlen valubytes * valubytes - oldlen)) ++
          repeat $ (0) (@wordToNat addrlen ($ (divup newlen valubytes -
                     divup oldlen valubytes)) * valubytes)) ->
          rep (firstn oldlen allbytes ++ repeat $ (0) (newlen - oldlen)) f''.
   Proof.
     intros.
     unfold rep.
     eexists.
     instantiate (allbytes := ((firstn # (INODE.ISize (BFILE.BFAttr f)) allbytes ++
          repeat $ (0)
            (divup # (INODE.ISize (BFILE.BFAttr f)) valubytes *
             valubytes - # (INODE.ISize (BFILE.BFAttr f)))) ++
         repeat $ (0)
           (# ($
               (divup newlen valubytes -
                divup # (INODE.ISize (BFILE.BFAttr f)) valubytes)) *
            valubytes))).
    intuition.
    eauto.
    unfold bytes_rep in H1.
    rewrite <- H1.
    eauto.
    rewrite <- H1.
    rewrite <- H0.
    erewrite eq_bytes_allbytes_ext0_to_newlen with (oldlen := oldlen) (allbytes := allbytes).
    eauto.
    eauto.
    subst; eauto.
    eauto.
    subst; eauto.
    erewrite wordToNat_natToWord_idempotent'.
    eauto.
    eapply divup_newlen_minus_oldlen_goodSize with (a := (INODE.ISize (BFILE.BFAttr f''))); eauto.
    rewrite app_length.
    rewrite firstn_length.
    rewrite repeat_length.
    rewrite Nat.min_l.
    omega.
    rewrite <- H.
    subst.
    apply divup_ok.
    repeat rewrite app_length.
    rewrite firstn_length.
    repeat rewrite repeat_length.
    rewrite Nat.min_l.
    repeat rewrite <- H0.
    repeat rewrite <- H1.
    erewrite wordToNat_natToWord_idempotent'.
    rewrite Nat.mul_sub_distr_r.
    repeat rewrite Nat.add_sub_assoc.
    apply len_oldlenext_newlen_eq.
    unfold ge.
    apply divup_ok.
    apply le_roundup; eauto.
    eapply divup_newlen_minus_oldlen_goodSize with (a := (INODE.ISize (BFILE.BFAttr f''))); eauto.
    eapply le_trans.
    apply divup_ok.
    omega.
   Qed.

  Definition filelen f := # (INODE.ISize (BFILE.BFAttr f)).

  Theorem grow_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ goodSize addrlen newlen ]]
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
     apply firstn_length_l_iff in H5.
     unfold ge.
     fold (filelen f) in H9.
     fold byte.
     replace (length allbytes).
     fold (roundup (filelen f) valubytes).
     replace (block_items items_per_valu) with valubytes.
     apply roundup_mono.
     apply Nat.lt_le_incl.
     unfold filelen.
     apply lt_word_lt_nat; auto.
     unfold block_items.
     unfold items_per_valu.
     rewrite valubytes_is.
     reflexivity.

     step.
     time step. (* 60s *)
     step.

     time step. (* 80s *)
     fold (filelen f) in *.
     apply firstn_length_l_iff in H5.
     instantiate (Fx0 := arrayN 0 (firstn (filelen f) allbytes)).
     instantiate (olddata0 := skipn (filelen f) (allbytes ++ a7)).
     replace (firstn (filelen f) allbytes) with
      (firstn (filelen f) (allbytes ++ a7)) at 1.
     apply list2nmem_arrayN_firstn_skipn.
     apply firstn_app_l; omega.
     reflexivity.
     unfold BFileRec.hidden.
     fold byte in *.
     fold (filelen f).
     assert (Hlen := Rec.array_of_word_length
      byte_type (roundup newlen valubytes - filelen f) ($ 0)).
     simpl in Hlen.
     fold byte in Hlen.
     rewrite Hlen.
     rewrite skipn_length.
     rewrite app_length.
     fold byte in *.
     replace (length a7).
     unfold alloc_items.
     rewrite block_items_ok.
     replace (length allbytes).
     fold (filelen f).
     fold (roundup (filelen f) valubytes).
     assert (Hnewlen := roundup_valu_ge newlen).
     assert (filelen f < newlen) by (apply lt_word_lt_nat; auto).
     assert (roundup (filelen f) valubytes <= roundup newlen valubytes).
     apply roundup_mono; omega.
     omega.
     rewrite app_length.
     (* XXX: lots of repetition *)
     fold byte in *.
     replace (length a7).
     unfold alloc_items.
     rewrite block_items_ok.
     replace (length allbytes).
     fold (filelen f).
     fold (roundup (filelen f) valubytes).
     assert (newlen <= roundup newlen valubytes).
     apply roundup_valu_ge.
     assert (filelen f < newlen).
     apply lt_word_lt_nat; auto.
     assert (roundup (filelen f) valubytes <= roundup newlen valubytes).
     apply roundup_mono; omega.
     omega.
     fold (filelen f).
     assert (filelen f < newlen).
     apply lt_word_lt_nat; auto.
     assert (newlen <= roundup newlen valubytes).
     apply roundup_valu_ge.
     omega.

     step.
     time step. (* 15s *)
     apply pimpl_or_r; right.
     cancel.
     fold (filelen f) in *.
     rewrite wordToNat_natToWord_idempotent'; auto.
     exists (firstn (filelen f) allbytes ++
      repeat $0 (roundup newlen valubytes - filelen f)).
     split; [split|split].
  Admitted.

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
    let^ (mscs, ok) <- grow_file fsxp inum newlen mscs;
    If (bool_dec ok true) {
      let curlen := oldattr.(INODE.ISize) in
      mscs <- IfRx irx (wlt_dec curlen ($ off)) {
        let^ (mscs) <- update_bytes fsxp inum
          #curlen (@natToWord ((off-#curlen)*8) 0) mscs;
        irx mscs
      } else {
        irx mscs
      };
      let^ (mscs) <- update_bytes fsxp inum off data mscs;
      rx ^(mscs, true)
    } else {
      rx ^(mscs, false)
    }.

  (** Case (2) of [write_bytes] above, where the file must be grown.

  This is an alias for [write_bytes] since [write_bytes] already handles
  all the cases, but has its own idiosyncratic spec. *)
  Definition overwrite_append T fsxp inum (off:nat) len (data : bytes len) mscs rx : prog T :=
    write_bytes fsxp inum off data mscs rx.

  Lemma off_in_bounds_ext:
    forall off f bytes (newdata: list byte),
      rep bytes f ->
        off <= length (bytes ++ repeat $ (0) (off + length newdata - # (INODE.ISize (BFILE.BFAttr f)))).
  Proof.
    intros.
    rewrite app_length.
    rewrite repeat_length.
    unfold rep in H.
    destruct H.
    intuition.
  Qed.

  Lemma length_rep:
    forall f bytes,
      rep bytes f -> length bytes = # (INODE.ISize (BFILE.BFAttr f)).
  Proof.
    intros.
    unfold rep in H.
    destruct H.
    intuition.
  Qed.

  Lemma helper_sep_star_comm_middle : forall AT AEQ V (m : @mem AT AEQ V) a b c,
    ((a * b) * c)%pred m -> (a * c * b)%pred m.
  Proof.
    intros; pred_apply; cancel.
  Qed.

  Lemma len_olddata_newdata_grown_eq:
      forall f (newdata: list byte) (bytes: list byte) off,
        goodSize addrlen (off + length newdata) ->
        rep bytes f ->
        (INODE.ISize (BFILE.BFAttr f) < $ (off + length newdata))%word ->
        length (skipn off (bytes ++
            repeat $ (0) (off + length newdata - # (INODE.ISize (BFILE.BFAttr f))))) =
          length newdata.
  Proof.
      intros.
      rewrite skipn_length.
      rewrite app_length.
      rewrite repeat_length.
      unfold rep in H0.
      destruct H0.
      intuition.
      rewrite H3.
      rewrite Nat.add_sub_assoc.
      rewrite minus_plus.
      rewrite minus_plus.
      eauto.
      apply wlt_lt in H1.
      erewrite wordToNat_natToWord_idempotent' in H1 by eauto.
      apply Nat.lt_le_incl.
      eauto.
      apply off_in_bounds_ext.
      eauto.
  Qed.

  Lemma olddata_exists_in_grown_file:
       forall f (newdata: list byte) (bytes: list byte) off,
        rep bytes f ->
 (arrayN 0
   (firstn off
      (bytes ++ repeat $ (0) (off + length newdata - # (INODE.ISize (BFILE.BFAttr f))))) *
 arrayN off
   (skipn off
      (bytes ++ repeat $ (0) (off + length newdata - # (INODE.ISize (BFILE.BFAttr f))))))%pred
  (list2nmem
     (bytes ++ repeat $ (0) (off + length newdata - # (INODE.ISize (BFILE.BFAttr f))))).
  Proof.
    intros.
    apply arrayN_split.
     apply off_in_bounds_ext; eauto.
    eapply list2nmem_array.
  Qed.

   Lemma olddata_exists_in_file:
      forall f (newdata: list byte) (bytes: list byte) off,
        rep bytes f ->
        off + length newdata <= length bytes ->
         (arrayN 0 (firstn off bytes) *
          arrayN (off + length newdata) (skipn (length newdata) (skipn off bytes)) *
          arrayN off (firstn (length newdata) (skipn off bytes)))%pred (list2nmem bytes).
   Proof.
    intros.
    apply helper_sep_star_comm_middle.
    rewrite arrayN_combine.
    apply arrayN_combine.
    rewrite app_length.
    rewrite firstn_length_l by omega.
    rewrite firstn_length_l.
    omega.
    rewrite skipn_length by omega.
    omega.
    rewrite <- app_assoc.
    rewrite firstn_skipn.
    rewrite firstn_skipn.
    apply list2nmem_array.
    rewrite firstn_length_l by omega.
    omega.
   Qed.

   Lemma len_olddata_newdata_eq:
      forall f (newdata: list byte) off (bytes: list byte),
      off + length newdata <= length bytes ->
      rep bytes f ->
      length (firstn (length newdata) (skipn off bytes)) = length newdata.
    Proof.
      intros.
      LOG.solve_lengths.
    Qed.

  Lemma off_length_in_bounds:
    forall f off (bytes: list byte) (newdata: list byte),
      goodSize addrlen (off+length newdata) ->
      rep bytes f ->
      ((INODE.ISize (BFILE.BFAttr f) < $ (off + length newdata))%word -> False) ->
      off + length newdata <= length bytes.
  Proof.
    intros.
    apply wle_le in H1.
    erewrite wordToNat_natToWord_idempotent' in H1 by auto.
    rewrite length_rep with (f := f) (bytes := bytes); eauto.
  Qed.

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
    step.  (* bfgetattr *)
    step.  (* If *)
  Admitted.

  Hint Extern 1 ({{_}} progseq (write_bytes _ _ _ _ _) _) => apply write_bytes_ok : prog.

  Theorem overwrite_append_ok: forall fsxp inum (off:nat) len (newbytes: bytes len) mscs,
    {< m mbase F Fm Fi A flist f bytes newdata wend,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           (* write goes from off to wend in new file *)
           [[ wend = off + len ]] *
           [[ Fi%pred (list2nmem (firstn off bytes)) ]] *
           [[ goodSize addrlen wend ]]
       POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes' zeros,
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ newdata = bsplit_list newbytes ]] *
           [[ (Fi * zeros * arrayN off newdata)%pred (list2nmem bytes')]] *
           [[ zeros = arrayN len (repeat $0 (off - len)) ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase
      >} overwrite_append fsxp inum off newbytes mscs.
  Proof.
    unfold overwrite_append, write_bytes.
    time step. (* 50s *)
    inversion H7 as [allbytes].
    inversion H0; clear H0.
    inversion H9; clear H9.
    inversion H10; clear H10.
    inversion H3.

    step.
    time step. (* 10s *)

    instantiate (Fi0 :=
      (let extraoff := Nat.min off (# (INODE.ISize (BFILE.BFAttr f))) in
      (Fi * arrayN extraoff (skipn extraoff allbytes))%pred)).
    simpl.
    inversion H7.
    inversion H0; clear H0.
    inversion H16; clear H16.
    inversion H17; clear H17.
    set (flen := # (INODE.ISize (BFILE.BFAttr f))) in *.
    rewrite firstn_firstn in H5.
    rewrite <- firstn_skipn with (l := allbytes) (n := Nat.min off flen) at 2.
    replace (Nat.min off flen) with (length (firstn (Nat.min off flen) allbytes)) at 1.
    apply list2nmem_arrayN_app; auto.
    (* solve this by case analysis on min *)
    apply firstn_length_l_iff in H9.
    destruct (Nat.min_spec off flen) as [Hminspec|Hminspec];
      inversion Hminspec as [? Hmineq];
      rewrite Hmineq;
      rewrite firstn_length_l;
      omega.
    admit. (* have hypothesis in word *)

    step.
    time step. (* 170s *)
    step.
    step.

    step.
  Admitted.

  Hint Extern 1 ({{_}} progseq (overwrite_append _ _ _ _ _) _) => apply overwrite_append_ok : prog.

End FASTBYTEFILE.
