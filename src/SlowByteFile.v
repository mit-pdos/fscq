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
Require Import BFileRec.

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

  Definition nunit_roundup (n: nat) (unitsz:nat) : nat := (n + unitsz - 1) / unitsz.

  Definition bytes_rep f (allbytes : list byte) :=
    BFileRec.array_item_file byte_type items_per_valu itemsz_ok f allbytes /\
    # (natToWord addrlen (length allbytes)) = length allbytes.

  Definition rep (bytes : list byte) (f : BFILE.bfile) :=
    exists allbytes,
    bytes_rep f allbytes /\
    firstn (# (f.(BFILE.BFAttr).(INODE.ISize))) allbytes = bytes /\
    length bytes = (# (f.(BFILE.BFAttr).(INODE.ISize))) /\
    nunit_roundup # (INODE.ISize (BFILE.BFAttr f)) valubytes * valubytes = length allbytes.

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

  Definition hidden (P : Prop) : Prop := P.
  Opaque hidden.

  Definition update_bytes T fsxp inum (off : nat) (newdata : list byte) mscs rx : prog T :=
    let^ (mscs, finaloff) <- ForEach b rest newdata
      Ghost [ mbase F Fm A f allbytes ]
      Loopvar [ mscs boff ]
      Continuation lrx
      Invariant
        exists m' flist' f' allbytes',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs  *
          [[ (Fm * BFILE.rep fsxp.(FSXPBlockAlloc) fsxp.(FSXPInode) flist')%pred (list2mem m') ]] *
          [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
          [[ bytes_rep f' allbytes' ]] *
          [[ apply_bytes allbytes' boff rest = apply_bytes allbytes off newdata ]] *
          [[ boff <= length allbytes' ]] *
          [[ off + length newdata = boff + length rest ]] *
          [[ hidden (length allbytes = length allbytes') ]] *
          [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]]
      OnCrash
        exists m',
          LOG.rep fsxp.(FSXPLog) F (ActiveTxn mbase m') mscs
      Begin
         mscs <- BFileRec.bf_put byte_type items_per_valu itemsz_ok
            fsxp.(FSXPLog) fsxp.(FSXPInode) inum ($ boff) b mscs;
          lrx ^(mscs, boff + 1)
      Rof ^(mscs, off);
      rx mscs.

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


  Theorem update_bytes_ok: forall fsxp inum off newdata mscs,
      {< m mbase F Fm A flist f bytes olddata Fx,
       PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]] *
           [[ hidden (length olddata = length newdata) ]] *
           [[ off + length newdata <= length bytes ]]
      POST RET:mscs
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           exists flist' f' bytes',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ (Fx * arrayN off newdata)%pred (list2nmem bytes') ]] *
           [[ hidden (BFILE.BFAttr f = BFILE.BFAttr f') ]]
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase 
      >} update_bytes fsxp inum off newdata mscs.
  Proof.
    unfold update_bytes, rep, bytes_rep.

    step.   (* step into loop *)

    rewrite firstn_length in *.

    eapply le_trans. eapply le_plus_l. eapply le_trans. apply H4.

    apply Min.le_min_r.

    constructor.

    step.   (* bf_put *)

    erewrite wordToNat_natToWord_bound by eauto.
    eauto.

    constructor.


    step.
    rewrite length_upd. auto.
    rewrite <- H21.
    rewrite <- apply_bytes_upd_comm by omega.
    unfold upd.

    erewrite wordToNat_natToWord_bound by eauto.
    auto.

    rewrite length_upd.
    eauto.

    rewrite H18. rewrite length_upd. constructor.
    subst; simpl; auto.

    step.

    eexists.
    intuition.
    eauto.
    eauto.
    rewrite <- H15.
    rewrite firstn_length in *.
    rewrite <- H16.
    eauto.

    rewrite <- H15.
    rewrite <- H16.
    eauto.

    rewrite <- H15.
    eapply apply_bytes_arrayN. eauto.
    instantiate (olddata := olddata).
    eauto.
    eauto.

    apply LOG.activetxn_would_recover_old.
    Grab Existential Variables.
    exact tt. 
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
    rewrite H11; eauto.
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
    
    pose proof item0_upd.
    simpl in H6.
    rewrite H6 in H16.
    
    rewrite <- app_assoc in H16.
    rewrite repeat_app in H16.
    replace (# (m1 ^+ $ (1)) * valubytes) with (# (m1) * valubytes + valubytes).
    auto.

    replace (# (m1 ^+ $1)) with (#m1 + 1).
    rewrite Nat.mul_add_distr_r.
    omega.

    rewrite wplus_alt. unfold wplusN, wordBinN. simpl.
    erewrite wordToNat_natToWord_bound. reflexivity.
    apply wlt_lt in H.
    instantiate (bound:=nblock). omega.

    replace (# (m1 ^+ $1)) with (#m1 + 1).

    rewrite Nat.mul_add_distr_r.

    simpl.

    rewrite <- repeat_app.
    repeat rewrite app_length.
    repeat rewrite repeat_length.

    erewrite wordToNat_natToWord_bound. reflexivity.
    apply wlt_lt in H13.
    rewrite app_length in H20. rewrite repeat_length in H20. rewrite H20 in H13.
    instantiate (bound := $ (INODE.blocks_per_inode) ^* items_per_valu ^+ items_per_valu ^+ $1).
    unfold INODE.blocks_per_inode in *. unfold INODE.nr_direct, INODE.nr_indirect in *.
    unfold items_per_valu in *. rewrite valubytes_is. rewrite valubytes_is in H13.
    apply le_trans with (4097 + # ($ (12 + 512) ^* natToWord addrlen 4096)). omega.

    apply Nat.eq_le_incl.
    reflexivity.

    rewrite wplus_alt. unfold wplusN, wordBinN. simpl.
    erewrite wordToNat_natToWord_bound. reflexivity.
    apply wlt_lt in H.
    instantiate (bound:=nblock). omega.

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
     let curlen := oldattr.(INODE.ISize) in
     let curblocks := nunit_roundup #curlen valubytes  in
     let newblocks := nunit_roundup newlen valubytes in
     let nblock := newblocks - curblocks in
     mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                              (INODE.Build_iattr ($ (curblocks*valubytes))
                                                 (INODE.IMTime oldattr)
                                                 (INODE.IType oldattr)) mscs;
     mscs <- update_bytes fsxp inum #curlen (repeat $0 (curblocks*valubytes-#curlen)) mscs;
     let^ (mscs, ok) <- grow_blocks fsxp inum ($ nblock) mscs;
     If (bool_dec ok true) {
       mscs <- BFILE.bfsetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum
                              (INODE.Build_iattr ($ newlen)
                                                 (INODE.IMTime oldattr)
                                                 (INODE.IType oldattr)) mscs;
       rx ^(mscs, true)
     } else {
       rx ^(mscs, false)
     }.

   Lemma le_rewrite_eq: 
    forall m n,
      m <= n  -> exists i, m + i = n.
   Proof.
     intros.
     eexists (n-m).
     omega.
   Qed.

   Lemma lt_rewrite_eq: 
    forall m n,
      m < n  -> exists i, m + i = n.
   Proof.
     intros.
     eexists (n-m).
     omega.
   Qed.

  Lemma roundup_ok:
    forall x,
      (nunit_roundup x valubytes) * valubytes >= x.
  Proof.
    unfold nunit_roundup; intros.
    rewrite (Nat.div_mod x valubytes) at 1 by ( rewrite valubytes_is; auto ).
    rewrite <- Nat.add_sub_assoc by ( rewrite valubytes_is; omega ).
    rewrite <- plus_assoc.
    rewrite (mult_comm valubytes).
    rewrite Nat.div_add_l by ( rewrite valubytes_is; auto ).

    case_eq (x mod valubytes); intros.
    - rewrite (Nat.div_mod x valubytes) at 2 by ( rewrite valubytes_is; auto ).
      rewrite valubytes_is at 2 3. simpl.
      replace (x / valubytes + 0) with (x / valubytes) by omega.
      rewrite (mult_comm valubytes).
      omega.

    - rewrite Nat.mul_add_distr_r.
      replace (S n + (valubytes - 1)) with (valubytes + n) by ( rewrite valubytes_is; omega ).
      replace (valubytes) with (1 * valubytes) at 3 by omega.
      rewrite Nat.div_add_l by ( rewrite valubytes_is; auto ).
      rewrite (Nat.div_mod x valubytes) at 2 by ( rewrite valubytes_is; auto ).
      assert (x mod valubytes < valubytes).
      apply Nat.mod_bound_pos; try rewrite valubytes_is; omega.
      rewrite Nat.mul_add_distr_r; simpl.
      unfold ge.
      eapply le_trans with (valubytes * (x / valubytes) + valubytes).
      omega.
      replace (valubytes + 0) with (valubytes) by omega.
      rewrite plus_assoc.
      rewrite mult_comm.
      apply le_plus_l.
  Qed.

  Lemma roundup_roundup_eq:
    forall x,
      (nunit_roundup ((nunit_roundup x valubytes)*valubytes) valubytes) * valubytes =
      (nunit_roundup x valubytes) * valubytes.
  Proof.
    unfold nunit_roundup; intros.
    rewrite <- Nat.add_sub_assoc by ( rewrite valubytes_is; omega ).
    rewrite Nat.div_add_l by ( rewrite valubytes_is; auto ).
    rewrite Nat.mul_add_distr_r.
    replace ((valubytes - 1) / valubytes * valubytes) with 0. omega.
    rewrite valubytes_is.
    compute.
    auto.
  Qed.

  Lemma le_roundup:
    forall m n,
      m <= n ->
      (nunit_roundup m valubytes) * valubytes <= (nunit_roundup n valubytes) * valubytes.
  Proof.
    unfold nunit_roundup; intros.
    apply Nat.mul_le_mono_r.
    apply Nat.div_le_mono.
    rewrite valubytes_is; auto.
    omega.
  Qed.

  Lemma nblock_ok:
    forall oldlen newlen boundary nblock,
      oldlen <= newlen ->
      boundary = (nunit_roundup oldlen valubytes) * valubytes ->
      nblock = (nunit_roundup newlen valubytes) - (nunit_roundup oldlen valubytes)->
      newlen - oldlen <= boundary - oldlen + nblock * valubytes.
  Proof.
    intros; subst.
    rewrite Nat.mul_sub_distr_r.
    rewrite <- Nat.add_sub_swap by apply roundup_ok.
    apply Nat.sub_le_mono_r.
    rewrite Nat.add_sub_assoc by ( apply le_roundup; omega ).
    rewrite plus_comm.
    rewrite <- Nat.add_sub_assoc by reflexivity.
    rewrite <- minus_diag_reverse.
    rewrite <- plus_n_O.
    apply roundup_ok.
  Qed.

  Lemma firstn_app : forall A (a b : list A) n,
    length a <= n ->
    firstn n (a ++ b) = a ++ firstn (n - length a) b.
  Proof.
    induction a; simpl; intros.
    rewrite <- minus_n_O; auto.
    destruct n; try omega; simpl.
    f_equal.
    apply IHa.
    omega.
  Qed.

  Lemma firstn_repeat_le : forall n m A (x : A),
    n <= m ->
    firstn n (repeat x m) = repeat x n.
  Proof.
    induction n; simpl; intros; auto.
    destruct m; try omega; simpl.
    f_equal.
    apply IHn.
    omega.
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
      (nunit_roundup oldlen valubytes) * valubytes = length allbytes ->
      bytes = firstn oldlen allbytes ->
      nbytes = (length allbytes) - oldlen ->
      nblock = (nunit_roundup newlen valubytes) - (nunit_roundup oldlen valubytes) ->
      firstn newlen (bytes ++ (repeat $0 (nbytes + (nblock * valubytes)))) = 
        (firstn oldlen allbytes) ++ (repeat $0 (newlen - oldlen)).
  Proof.
    intros.

    assert (length bytes = oldlen).
    subst. rewrite firstn_length. apply Nat.min_l.
    rewrite <- H0.
    apply roundup_ok.

    rewrite firstn_app by omega.
    f_equal; auto.
    rewrite H4.
    rewrite firstn_repeat_le; auto.

    rewrite H2.
    rewrite <- H0.
    apply nblock_ok; auto.
  Qed.

   Theorem grow_file_ok: forall fsxp inum newlen mscs,
    {< m mbase F Fm A flist f bytes,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ (# (INODE.ISize (BFILE.BFAttr f))) <= newlen ]]
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
     step.  (* getattr *)
     step.  (* set attributes *)
     step.  (* uppdate bytes *)
     unfold rep, bytes_rep.
     eexists.
     instantiate (allbytes := allbytes).
     intuition eauto.

     (* establish rep for f', the file updated by update_bytes *)
     unfold array_item_file in *.
     subst; simpl in *.
     eauto.
     subst; simpl.
     rewrite firstn_length.
     rewrite Nat.min_l.
     eauto.
     rewrite H9.
     rewrite H7.
     eauto.
     subst; simpl in *.
     erewrite wordToNat_natToWord_bound.
     rewrite roundup_roundup_eq with (x := # (INODE.ISize (BFILE.BFAttr f))).
     rewrite H9.
     eauto.
     instantiate (bound := $ ( (nunit_roundup # (INODE.ISize (BFILE.BFAttr f))
  valubytes) * valubytes)).
     rewrite H9.
     eauto.

     (* establish arrayN precondition for updates_bytes *)
     instantiate (olddata := skipn # (INODE.ISize (BFILE.BFAttr f)) allbytes).
     instantiate (Fx := arrayN 0 (firstn # (INODE.ISize (BFILE.BFAttr f)) allbytes)).
     replace (# (INODE.ISize (BFILE.BFAttr f))) with (0 + # (INODE.ISize (BFILE.BFAttr f))) at 2 by omega.
     apply arrayN_split.
     admit. (* by H9 and roundup_ok *)
     rewrite firstn_oob.
     apply list2nmem_array.
     subst; simpl.
     rewrite H9.
     eauto.
    
     (* establish hidden length old = length new of update_bytes *)
     admit.  (* hidden length *)

     (* establish off + length newdata <= length bytes  *)
     admit. (* some length roundup *)

     unfold rep.

     step.  (* grow blocks *)
     step.
     step.
     step.
     step.
     step.
     eapply pimpl_or_r; right; cancel.
     
     eexists.
     unfold bytes_rep in H23.
     destruct H25.
     intuition.
     eapply a9.
     eapply e.
     replace (# ($ (newlen))) with newlen.
     eapply arrayN_combine in H17.
     apply list2nmem_array_eq in H17.
     rewrite <- H16 in H20.
     simpl in *.
     erewrite wordToNat_natToWord_bound in H20.
     rewrite roundup_roundup_eq in H20.
     rewrite firstn_oob in H17.
     rewrite H17.
     rewrite <- app_assoc.
     rewrite repeat_app.
     erewrite eq_bytes_allbytes_ext0_to_newlen with (oldlen := # (INODE.ISize (BFILE.BFAttr f))) (bytes := (firstn (# (INODE.ISize (BFILE.BFAttr f))) allbytes)).
     instantiate (allbytes := allbytes).
     eauto.
     eauto.
     eauto.
     eauto.
     rewrite H9.
     eauto.
     erewrite wordToNat_natToWord_bound.
     eauto.
     admit.  (* need bound on newlen *)


     rewrite <- H20.
     rewrite <- H16.
     simpl.
     erewrite wordToNat_natToWord_bound.
     eauto.
     admit.  (* roundup bound *)
     admit.  (* roundup bound *)
     simpl.
     eauto.

     admit. (* bound on newlen *)

     rewrite app_length.
     rewrite repeat_length.
     rewrite firstn_length.
     rewrite Nat.min_l.
     rewrite plus_comm.
     rewrite Nat.sub_add.
     admit. (* bound on newlen *)
     eauto.
     rewrite <- H9.
     apply roundup_ok.

     rewrite app_length.
     rewrite <- H20.
     rewrite repeat_length.
     rewrite <- H16.
     simpl.
     erewrite wordToNat_natToWord_bound.
     erewrite wordToNat_natToWord_bound.
     rewrite roundup_roundup_eq.
     erewrite wordToNat_natToWord_bound.
     rewrite Nat.mul_sub_distr_r.
     rewrite le_plus_minus_r.
     eauto.


     eapply le_roundup.
     eauto.
     instantiate (bound4 := $ (nunit_roundup newlen valubytes)).
     admit.
     instantiate (bound3 := $ ((nunit_roundup # (INODE.ISize (BFILE.BFAttr f)) valubytes) * valubytes)).
     rewrite H9.
     eauto.
     admit. (* bound on newlen *)
     step.
   Admitted.

  Hint Extern 1 ({{_}} progseq (grow_file _ _ _ _) _) => apply grow_file_ok : prog.

  
  Definition write_bytes T fsxp inum (off : nat) (data : list byte) mscs rx : prog T :=
    let newlen := off + length data in
    let^ (mscs, oldattr) <- BFILE.bfgetattr fsxp.(FSXPLog) fsxp.(FSXPInode) inum mscs;
    let curlen := oldattr.(INODE.ISize) in      
    If (wlt_dec curlen ($ newlen)) {
         let^ (mscs, ok) <- grow_file fsxp inum newlen mscs;
         If (bool_dec ok true) {
           mscs <-  update_bytes fsxp inum off data mscs;
           rx ^(mscs, ok)
        } else {
           rx ^(mscs, false)
        }
    } else {
        mscs <-  update_bytes fsxp inum off data mscs;
        rx ^(mscs, true)
    }.


  Theorem write_bytes_ok: forall fsxp inum (off:nat) (newdata: list byte) mscs,
    {< m mbase F Fm Fx A flist f bytes olddata,
      PRE LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m) mscs *
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ rep bytes f ]] *
           [[ length olddata = Nat.min (length newdata) ((length bytes - off)) ]] *
           [[ (Fx * arrayN off olddata)%pred (list2nmem bytes) ]]
       POST RET:^(mscs, ok)
           exists m', LOG.rep (FSXPLog fsxp) F (ActiveTxn mbase m') mscs *
           ([[ ok = false ]] \/
           [[ ok = true ]] * exists flist' f' bytes',
           [[ (Fm * BFILE.rep (FSXPBlockAlloc fsxp) (FSXPInode fsxp) flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ rep bytes' f' ]] *
           [[ (Fx * arrayN off newdata)%pred (list2nmem bytes') ]])
       CRASH LOG.would_recover_old (FSXPLog fsxp) F mbase 
      >} write_bytes fsxp inum off newdata mscs.
  Proof.
    unfold write_bytes. (* rep, bytes_rep. *)
    step.  (* bfgetattr *)
    step.  (* If *)
    step.  (* grow_file *)
    instantiate (curlen := (# (INODE.ISize (BFILE.BFAttr f)))).
    admit.
    step.
    step.
    step.

    (* work around unification problem *)
    eapply pimpl_ok2; eauto with prog.
    unfold rep, bytes_rep in *.
    cancel.
    eexists.
    intuition.
    instantiate (allbytes := allbytes).
    apply H.
    simpl.
    auto.
    rewrite firstn_length.
    rewrite Nat.min_l.
    admit.
    admit.
    admit.
    admit. (* H? *)
    rewrite firstn_length.
    rewrite Nat.min_l.
    admit.
    admit.
    admit.
    step.
    eapply pimpl_or_r; right; cancel.
    eexists.
    intuition.
    instantiate (allbytes := allbytes1).
    apply H8.
    apply H26.
    apply H23.
    admit. (* round up *)
    apply H25.
    step.


    (* false branch *)
    eapply pimpl_ok2; eauto with prog.
    unfold rep, bytes_rep in *.
    cancel.
    eexists.
    instantiate (allbytes := allbytes).
    intuition.
    instantiate (olddata1 := olddata).
    apply H4.
    rewrite H5.
    Transparent hidden.
    unfold hidden.
    admit. (* H10 *)
    admit. (* H10 *)

    step.  (* return *)

    eapply pimpl_or_r; right; cancel.
    eexists.
    intuition.
    instantiate (allbytes := allbytes0).
    apply H0.
    apply H18.
    apply H15.
    admit. (* roundup *)
    eapply H17.
    
  Admitted.

End SLOWBYTEFILE.
