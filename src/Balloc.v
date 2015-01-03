Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Nomega.
Require Import Idempotent.
Require Import Psatz.
Require Import AddrMap.
Require Import Rec.
Require Import NArith.
Require Import Log.
Require Import RecArray.

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
    ([[ goodSize addrlen (wordToNat (BmapNBlocks xp) * valulen) ]] *
     RecArray.array_item itemtype items_per_valu blocksz (xp_to_raxp xp)
       (bmap_bits xp bmap))%pred.

  Definition free' T lxp xp bn rx : prog T :=
    RecArray.put itemtype items_per_valu blocksz
      lxp (xp_to_raxp xp) bn (alloc_state_to_bit Avail) rx.

  Lemma selN_seq : forall a b c d, c < b -> selN (seq a b) c d = a + c.
  Proof.
    intros. rewrite nth_selN_eq. apply seq_nth; assumption.
  Qed.

  (* The third hypothesis isn't necessary but makes things simpler *)
  Lemma upd_bmap_bits : forall xp a bn b state,
    b = alloc_state_to_bit state ->
    goodSize addrlen (wordToNat (BmapNBlocks xp) * valulen) ->
    wordToNat bn < wordToNat (BmapNBlocks xp) * valulen ->
    upd (bmap_bits xp a) bn b = bmap_bits xp (fupd a bn state).
  Proof.
    intros. rewrite H. unfold bmap_bits, upd.
    rewrite updN_map_seq by assumption.
    eapply list_selN_ext with (default := $ (0)).
    repeat rewrite map_length; trivial.
    intros pos Hl.
    rewrite map_length in Hl. rewrite seq_length in Hl.
    repeat rewrite selN_map with (default' := 0) by (rewrite seq_length; assumption).
    rewrite selN_seq by assumption. simpl.
    destruct (Nat.eq_dec pos (wordToNat bn)).
    rewrite e. rewrite natToWord_wordToNat. rewrite fupd_same; trivial.
    rewrite fupd_other. trivial.
    eapply f_neq.
    rewrite wordToNat_natToWord_idempotent'.
    auto.
    eapply Nat.lt_trans. apply Hl.
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
    (* XXX for some extremely mysterious reason inlining [word2nat_simpl] here saves it from hanging *)
    try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in); (* XXX this causes problems: simpl; *)
    unfold wplus, wminus, wmult, wdiv, wmod, wordBin in *;
    repeat match goal with
    | [ H : _ <> _ |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); mynsimp H
    | [ H : _ = _ -> False |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); mynsimp H
    | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H || apply (f_equal wordToNat) in H
               || apply Nlt_out in H || apply Nge_out in H); mynsimp H
    end;
    autorewrite with W2Nat in *;
    repeat match goal with
    | [ H : _ < _ |- _ ] => apply lt_ovf in H; destruct H
    end.
    word2nat_auto.
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

  Hint Rewrite natToWord_wordToNat selN_map_seq.

  Theorem alloc'_ok: forall lxp xp,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) * [[ (Fm * rep' xp bmap)%pred m ]]
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
     (* XXX for some extremely mysterious reason inlining [word2nat_simpl] here saves it from hanging *)
    try (apply nat_of_N_eq || apply Nneq_in || apply Nlt_in || apply Nge_in); (* XXX this causes problems: simpl; *)
    unfold wplus, wminus, wmult, wdiv, wmod, wordBin in *;
    repeat match goal with
    | [ H : _ <> _ |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); mynsimp H
    | [ H : _ = _ -> False |- _ ] => (apply Nneq_out in H || apply Wneq_out in H); mynsimp H
    | [ H : _ |- _ ] => (apply (f_equal nat_of_N) in H || apply (f_equal wordToNat) in H
               || apply Nlt_out in H || apply Nge_out in H); mynsimp H
    end;
    autorewrite with W2Nat in *;
    repeat match goal with
    | [ H : _ < _ |- _ ] => apply lt_ovf in H; destruct H
    end.
    word2nat_auto.
    clear H6. (* XXX need to hunt down this [pow2 addrlen] *)
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
     listpred (fun a => a |->?) freeblocks)%pred.

  Lemma remove_not_In :
    forall T dec (a : T) l, ~ In a l -> remove dec a l = l.   
  Proof.
    induction l.
    auto.
    intro Hni. simpl.
    destruct (dec a a0).
    subst. destruct Hni. simpl. tauto.
    rewrite IHl. trivial.
    simpl in Hni. tauto.
  Qed.

  Lemma listpred_pick : forall T P (x : T) l, In x l -> listpred P l =p=> exists F, P x * F.
    induction l; intro Hi.
    inversion Hi.
    simpl.
    destruct Hi.
    cancel.
    rewrite IHl by assumption.
    cancel.
  Qed.

  Lemma disj_union : forall a b c, mem_disjoint a (mem_union b c) -> mem_disjoint a b.
  Proof.
    unfold mem_disjoint, mem_union.
    intros.
    intro He.
    destruct H.
    do 4 destruct He as [? He].
    repeat eexists. apply H.
    rewrite He. tauto.
  Qed.

  Lemma listpred_remove : forall x l,
    In x l ->
    listpred (fun a => a |->?) l =p=>
        (fun a => a |->?) x * listpred (fun a => a |->?) (remove (@weq _) x l).
  Proof.
    induction l; intro Hi.
    inversion Hi.
    simpl; destruct ((@weq _) x a).
    + intros m Hp.
      (* have to prove [x] can't be in [l] (or the left side couldn't be disjoint) *)
      rewrite e.
      rewrite remove_not_In. trivial.
      subst. intro Hil.
      rewrite listpred_pick with (x := a) in Hp by assumption; subst.
      unfold sep_star in Hp; rewrite sep_star_is in Hp; unfold sep_star_impl in Hp.
      destruct Hp as [m1 Hp]. destruct Hp as [x1 Hp]. repeat destruct Hp as [? Hp].
      subst.
      apply disj_union in H0. unfold mem_disjoint in H0.
      unfold ptsto in H1. destruct H1.
      unfold ptsto in H4. destruct H4.
      destruct H0. repeat eexists. apply H. apply H1.
    + simpl. rewrite <- sep_star_assoc.
      rewrite (sep_star_comm (x |->?) (a |->?)). rewrite IHl.
      rewrite sep_star_assoc. auto.
      destruct Hi; subst; tauto.
  Qed.

  Lemma remove_still_In : forall T dec (a b : T) l,
    In a (remove dec b l) -> In a l.
  Proof.
    induction l; simpl; [tauto|].
    destruct (dec b a0).
    right; apply IHl; assumption.
    intro H. destruct H. subst. auto.
    right; apply IHl; assumption.
  Qed.

  Lemma remove_still_In_ne : forall T dec (a b : T) l,
    In a (remove dec b l) -> b <> a.
  Proof.
    induction l; simpl; [tauto|].
    destruct (dec b a0).
    assumption.
    intro H. destruct H. subst. auto.
    apply IHl; assumption.
  Qed.

  Lemma remove_other_In : forall T dec (a b : T) l,
    b <> a -> In a l -> In a (remove dec b l).
  Proof.
    induction l.
    auto.
    simpl. destruct (dec b a0).
    subst. intros. destruct H0; [subst; tauto | apply IHl; auto].
    simpl. intros. destruct H0; [left; auto | right; apply IHl; auto].
  Qed.

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
    unfold alloc.
    intros.
    eapply pimpl_ok2. apply alloc'_ok.
    unfold rep, rep'.
    cancel.
    step.
    apply pimpl_or_r. right.
    norm. (* We can't just [cancel] here because it introduces evars too early *)
    cancel.
    split; [split; trivial |].
    pred_apply.
    instantiate (a1 := remove (@weq addrlen) a0 l).
    erewrite listpred_remove. cancel.
    assert (a a2 = Avail) as Ha.
    apply H8.
    eapply remove_still_In; apply H0.
    rewrite <- Ha.
    apply fupd_other.
    eapply remove_still_In_ne; apply H0.
    assert (a0 <> a2).
    intro He. subst. rewrite fupd_same in H0. discriminate. trivial.
    rewrite fupd_other in H0 by assumption. 
    apply remove_other_In. assumption.
    rewrite H8; assumption.
    rewrite H8; assumption.
  Qed.

  Theorem free_ok : forall lxp xp bn,
    {< Fm mbase m freeblocks,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (Fm * rep xp freeblocks * bn |->?)%pred m ]] *
           [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:r ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep xp (bn :: freeblocks))%pred m' ]]) \/
           ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m))
    CRASH  LOG.log_intact lxp mbase
    >} free lxp xp bn.
  Proof.
    unfold free.
    intros.
    eapply pimpl_ok2. apply free'_ok.
    unfold rep, rep'.
    cancel.
    step.
    apply pimpl_or_r. left.
    cancel.
    subst; apply fupd_same; trivial.
    rewrite H10 in H6.
    destruct (weq bn a0).
    subst; apply fupd_same; trivial.
    rewrite <- H6; apply fupd_other; assumption.
    destruct (weq bn a0).
    left. auto.
    right. rewrite fupd_other in H3 by assumption. apply H10; assumption.
  Qed.

End BALLOC.
