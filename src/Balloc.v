Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Log.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Nomega.
Require Import Idempotent.
Require Import Psatz.
Require Import AddrMap.
Require Import Rec.
Require Import RecArray.
Require Import NArith.


Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
  BmapStart : addr;
  BmapNBlocks : addr
}.

Module BALLOC.

  Definition itemtype := Rec.WordF 1.
  Definition items_per_valu : addr := natToWord addrlen valulen.
  Theorem items_per_valu_not_0 : items_per_valu <> $0.
    Require Import WordAuto.
    unfold items_per_valu. rewrite valulen_is. apply word_neq. compute. intro H. simpl in H. discriminate.
  Qed.

  Theorem blocksz : valulen = Rec.len (RecArray.blocktype itemtype items_per_valu).
    unfold blocktype, items_per_valu.
    rewrite wordToNat_natToWord_idempotent.
    simpl. ring.
    rewrite valulen_is. compute. auto.
  Qed.

  Definition rep_block := RecArray.rep_block blocksz.
  Definition valu_to_block := RecArray.valu_to_block itemtype items_per_valu blocksz.
  Definition rep_valu_id := RecArray.rep_valu_id blocksz.


  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_dec : forall (a b : alloc_state), {a = b} + {a <> b}.
    destruct a; destruct b; try (left; constructor); right; discriminate.
  Qed.

  Definition alloc_state_to_bit a : word 1 :=
    match a with
    | Avail => $0
    | InUse => $1
    end.

  Definition bit_to_alloc_state (b : word 1) : alloc_state :=
    match b with
    | WS false W0 => Avail
    | _ => InUse
    end.

  Lemma bit_alloc_state_id : forall a, bit_to_alloc_state (alloc_state_to_bit a) = a.
    destruct a; auto.
  Qed.
  Hint Rewrite bit_alloc_state_id.

  Definition bmap_bits xp (bmap : addr -> alloc_state) :=
     map (fun i => alloc_state_to_bit (bmap $ (i)))
          (seq 0 (wordToNat (BmapNBlocks xp) * valulen)).

  Definition xp_to_raxp xp :=
    RecArray.Build_xparams (BmapStart xp) (BmapNBlocks xp).

  Definition rep' xp (bmap : addr -> alloc_state) :=
    RecArray.array_item itemtype items_per_valu blocksz (xp_to_raxp xp)
      (bmap_bits xp bmap).

  Definition free' T lxp xp bn rx : prog T :=
    RecArray.put itemtype items_per_valu blocksz
      lxp (xp_to_raxp xp) bn (alloc_state_to_bit Avail) rx.

  (* The second hypothesis isn't actually necessary but makes things simpler *)
  Lemma upd_bmap_bits : forall xp a bn b state,
    b = alloc_state_to_bit state ->
    wordToNat bn < wordToNat (BmapNBlocks xp) * valulen ->
    upd (bmap_bits xp a) bn b = bmap_bits xp (fupd a bn state).
  Proof.
    intros. rewrite H. unfold bmap_bits, upd.
    rewrite updN_map_seq.
    apply list_selN_ext with (default := $ (0)).
    repeat rewrite map_length; trivial.
    intros pos Hl.
    rewrite map_length in Hl. rewrite seq_length in Hl.
    repeat rewrite selN_map with (default' := 0) by (rewrite seq_length; assumption).
    Lemma selN_seq : forall a b c d, c < b -> selN (seq a b) c d = a + c.
    Proof.
      intros. rewrite nth_selN_eq. apply seq_nth; assumption.
    Qed.
    rewrite selN_seq by assumption. simpl.
    destruct (Nat.eq_dec pos (wordToNat bn)).
    rewrite e. rewrite natToWord_wordToNat. rewrite fupd_same; trivial.
    rewrite fupd_other. trivial.
    admit. (* XXX might need to worry about overflow here *)
    assumption.
  Qed.

  Theorem free'_ok : forall lxp xp bn,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (Fm * rep' xp bmap)%pred m ]] *
           [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:r ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep' xp (fupd bmap bn Avail))%pred m' ]]) \/
           ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m))
    CRASH  LOG.log_intact lxp mbase
    >} free' lxp xp bn.
  Proof.
    unfold free', rep', LOG.log_intact.
    intros. eapply pimpl_ok2. apply put_ok. (* XXX why doesn't eauto with prog work? *)
    apply items_per_valu_not_0.

    cancel.
    step.
    apply pimpl_or_r. left.
    norm.
    cancel.
    repeat (split; [constructor |]).
    pred_apply. cancel.
    erewrite upd_bmap_bits; try trivial.
    apply wlt_mult_inj in H4. rewrite wordToNat_natToWord_idempotent in H4. assumption.
    simpl. rewrite valulen_is. compute. trivial.
  Qed.

  Hint Extern 1 ({{_}} progseq (free' _ _ _) _) => apply free'_ok : prog.

  Definition alloc' T lxp xp rx : prog T :=
    For i < (BmapNBlocks xp ^* $ (valulen))
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        LOG.rep lxp (ActiveTxn mbase m)
      OnCrash
        LOG.log_intact lxp mbase
      Begin
        bit <- RecArray.get itemtype items_per_valu blocksz
          lxp (xp_to_raxp xp) i;
        let state := bit_to_alloc_state bit in
        If (alloc_state_dec state Avail) {
          ok <- RecArray.put itemtype items_per_valu blocksz
            lxp (xp_to_raxp xp) i (alloc_state_to_bit InUse);
          If (bool_dec ok true) {
            rx (Some i)
          } else {
            rx None
          }
        } else {
          lrx tt
        }
      Rof;;
    rx None.

(*
  Theorem sel_avail' : forall len a bn start, (bn < $ len)%word ->
    sel (map (fun i => alloc_state_to_valu (a $ i)) (seq start len)) bn = $0 ->
    a (bn ^+ $ start) = Avail.
  Proof.
    unfold sel.
    induction len; intros; simpl.
    - exfalso. apply wlt_lt in H. simpl in H. omega.
    - simpl in H0.
      destruct (weq bn $0); subst; simpl in *.
      + rewrite wplus_unit.
        unfold alloc_state_to_valu in *.
        destruct (a $ start); auto.
        apply natToWord_inj in H0.
        discriminate.
        admit.
        admit.
      + case_eq (wordToNat bn); intros.
        * admit.
        * rewrite H1 in *.
          replace (bn ^+ $ start) with ((bn ^- $1) ^+ $ (S start)).
          apply IHlen.
          admit.
          replace (wordToNat (bn ^- $1)) with (n0).
          auto.
          admit.
          admit.
  Qed.

  Theorem sel_avail : forall len a bn, (bn < $ len)%word ->
    sel (map (fun i => alloc_state_to_valu (a $ i)) (seq 0 len)) bn = $0 ->
    a bn = Avail.
  Proof.
    intros.
    replace (bn) with (bn ^+ $0).
    eapply sel_avail'; eauto.
    rewrite wplus_comm. rewrite wplus_unit. auto.
  Qed.


  Theorem sel_avail : forall bmap bnblock bnoff nblocks,
     sel (map (fun nblock => blockbits bmap (nblock * valulen))
              (seq 0 (wordToNat nblocks))) bnblock $0 ^& wbit valulen bnoff = $ 0
    -> (bnblock < nblocks)%word
    -> (bnoff < $ valulen)%word
    -> bmap (bnblock ^* $ valulen ^+ bnoff) = Avail.
  Proof.
    unfold sel; intros.
    apply wlt_lt in H0 as H0'.
    rewrite selN_map_seq in H; auto.
    admit.
  Qed.
*)

  Hint Rewrite natToWord_wordToNat selN_map_seq.

  Theorem alloc'_ok: forall lxp xp,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) * [[ (Fm * rep' xp bmap)%pred m ]] *
           [[ (wordToN (BmapNBlocks xp) * N.of_nat valulen < Npow2 addrlen)%N ]]
    POST:r [[ r = None ]] * LOG.rep lxp (ActiveTxn mbase m) \/
           exists bn m', [[ r = Some bn ]] * [[ bmap bn = Avail ]] *
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (Fm * rep' xp (fupd bmap bn InUse))%pred m' ]]
    CRASH  LOG.log_intact lxp mbase
    >} alloc' lxp xp.
  Proof.
    unfold alloc', rep', LOG.log_intact.
    hoare.
    eapply pimpl_ok2. apply get_ok. (* XXX why doesn't eauto with prog work? *)
    apply items_per_valu_not_0.

    cancel.
    hoare.
    eapply pimpl_ok2. apply put_ok.
    apply items_per_valu_not_0.
    cancel.
    hoare.
    apply pimpl_or_r. right.
    (* XXX word automation *)
    apply wlt_mult_inj in H3.
    rewrite wordToNat_natToWord_idempotent in H3 by (simpl; rewrite valulen_is; compute; trivial).
    cancel.
    rewrite <- H10. unfold bmap_bits, sel.
    autorewrite with core; auto.
    erewrite upd_bmap_bits; trivial.
    step.
    step.
  Qed.

  Hint Extern 1 ({{_}} progseq (alloc' _) _) => apply alloc'_ok : prog.

  Theorem free'_recover_ok : forall lxp xp bn,
    {< Fm mbase m bmap,
    PRE     LOG.rep lxp (ActiveTxn mbase m) *
            [[ (Fm * rep' xp bmap)%pred m ]] *
            [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:r  [[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m) \/
            [[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep' xp (fupd bmap bn Avail))%pred m' ]]
    CRASH:r LOG.rep lxp (NoTransaction mbase)
    >} free' lxp xp bn >> LOG.recover lxp.
  Proof.
    unfold forall_helper; intros.
    exists (LOG.log_intact lxp v0); intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2.
    eapply free'_ok.
    eapply LOG.recover_ok.

    cancel.
    cancel.
    hoare.
    cancel.
    hoare.
  Qed.

  (* Different names just so that we can state another theorem about them *)
  Definition alloc := alloc'.
  Definition free := free'.

  Definition rep xp (freeblocks : list addr) :=
    (exists bmap,
     rep' xp bmap *
     [[ forall a, In a freeblocks <-> bmap a = Avail ]] *
     listpred (fun a => exists v, a |-> v) freeblocks)%pred.  

  Theorem alloc_ok : forall lxp xp,
    {< Fm mbase m freeblocks,
    PRE    LOG.rep lxp (ActiveTxn mbase m) * [[ (Fm * rep xp freeblocks)%pred m ]]
    POST:r [[ r = None ]] * LOG.rep lxp (ActiveTxn mbase m) \/
           exists bn m' freeblocks', [[ r = Some bn ]] *
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (Fm * bn |->? * rep xp freeblocks')%pred m' ]]
    CRASH  LOG.log_intact lxp mbase
    >} alloc lxp xp.
  Proof.
    admit.
  Qed.

  Theorem free_ok : forall lxp xp bn,
    {< Fm mbase m freeblocks,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (Fm * rep xp freeblocks * bn |->?)%pred m ]] *
           [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:r ([[ r = true ]] * exists m' freeblocks', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep xp freeblocks')%pred m' ]]) \/
           ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m))
    CRASH  LOG.log_intact lxp mbase
    >} free lxp xp bn.
  Proof.
    admit.
  Qed.

End BALLOC.
