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
Require Import MemLog.
Require Import RecArray.
Require Import ListPred.
Require Import GenSep.


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

  Definition free' T lxp xp ms bn rx : prog T :=
    RecArray.put itemtype items_per_valu blocksz
      lxp (xp_to_raxp xp) ms bn (alloc_state_to_bit Avail) rx.

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

  Theorem free'_ok : forall lxp xp ms bn,
    {< Fm mbase m bmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (Fm * rep' xp bmap)%pred (list2mem m) ]] *
             [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:ms' exists m', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (Fm * rep' xp (fupd bmap bn Avail))%pred (list2mem m') ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} free' lxp xp ms bn.
  Proof.
    unfold free', rep', MEMLOG.log_intact.
    intros. eapply pimpl_ok2. apply put_ok. (* XXX why doesn't eauto with prog work? *)

    cancel.
    step.
    erewrite upd_bmap_bits; try trivial.
    cancel.
    auto.
    word2nat_auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (free' _ _ _ _) _) => apply free'_ok : prog.

  Definition alloc' T lxp xp ms rx : prog T :=
    For i < (BmapNBlocks xp ^* $ (valulen))
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        MEMLOG.rep lxp (ActiveTxn mbase m) ms
      OnCrash
        MEMLOG.log_intact lxp mbase
      Begin
        bit <- RecArray.get itemtype items_per_valu blocksz
          lxp (xp_to_raxp xp) ms i;
        let state := bit_to_alloc_state bit in
        If (alloc_state_dec state Avail) {
          ms' <- RecArray.put itemtype items_per_valu blocksz
            lxp (xp_to_raxp xp) ms i (alloc_state_to_bit InUse);
          rx (Some i, ms')
        } else {
          lrx tt
        }
      Rof;;
    rx (None, ms).

  Hint Rewrite natToWord_wordToNat selN_map_seq.

  Theorem alloc'_ok: forall lxp xp ms,
    {< Fm mbase m bmap,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ (Fm * rep' xp bmap)%pred (list2mem m) ]]
    POST:p exists r ms', [[ p = (r, ms') ]] *
           ([[ r = None ]] * MEMLOG.rep lxp (ActiveTxn mbase m) ms' \/
            exists bn m', [[ r = Some bn ]] * [[ bmap bn = Avail ]] *
            MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
            [[ (Fm * rep' xp (fupd bmap bn InUse))%pred (list2mem m') ]])
    CRASH  MEMLOG.log_intact lxp mbase
    >} alloc' lxp xp ms.
  Proof.
    unfold alloc', rep'.
    hoare.
    eapply pimpl_ok2. apply get_ok. (* XXX why doesn't eauto with prog work? *)

    cancel.
    hoare.
    eapply pimpl_ok2. apply put_ok.
    cancel.
    hoare.
    apply pimpl_or_r. right.
    word2nat_auto.
    cancel.
    rewrite <- H9. unfold bmap_bits, sel.
    autorewrite with core; auto.
    erewrite upd_bmap_bits; trivial.
    cancel.
    trivial.
    cancel.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (alloc' _ _ _) _) => apply alloc'_ok : prog.

  Theorem free'_recover_ok : forall lxp xp bn ms,
    {< Fm mbase m bmap,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (Fm * rep' xp bmap)%pred (list2mem m) ]] *
             [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:ms' exists m', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (Fm * rep' xp (fupd bmap bn Avail))%pred (list2mem m') ]]
    CRASH:r  MEMLOG.rep lxp (NoTransaction mbase) ms_empty
    >} free' lxp xp ms bn >> MEMLOG.recover lxp.
  Proof.
    unfold forall_helper; intros.
    exists (MEMLOG.log_intact lxp v0); intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2.
    eapply free'_ok.
    eapply MEMLOG.recover_ok.

    cancel.
    cancel.
    hoare.
    fold (@sep_star valu).
    cancel.
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

  Lemma listpred_pick : forall V T (P : T -> @pred V) (x : T) l, 
    In x l -> listpred P l =p=> exists F, P x * F.
  Proof.
    induction l; intro Hi.
    inversion Hi.
    simpl.
    destruct Hi.
    cancel.
    rewrite IHl by assumption.
    cancel.
  Qed.

  Lemma disj_union : forall V (a : @mem V) b c, 
    mem_disjoint a (mem_union b c) -> mem_disjoint a b.
  Proof.
    unfold mem_disjoint, mem_union.
    intros.
    intro He.
    destruct H.
    do 4 destruct He as [? He].
    repeat eexists. apply H.
    rewrite He. tauto.
  Qed.

  Lemma listpred_nodup :
    forall V T P l (m : @mem V),
      (forall x y : T, {x = y} + {x <> y}) ->
      (forall (y : T) m', ~ (P y * P y)%pred m') ->
      listpred P l m -> NoDup l.
  Proof.
    induction l; intuition; constructor; simpl in H0.
    intro Hin.
    revert H0.
    erewrite listpred_pick by (apply Hin).
    (* XXX should be possible not to bash this *)
    unfold_sep_star; intuition.
    do 2 destruct H0. intuition. destruct H4. do 2 destruct H3. intuition.
    eapply H.
    unfold_sep_star.
    exists x. exists x2.
    repeat split; [ subst; eapply disj_union; eauto | | ]; intuition; eauto.

    revert H0.
    unfold_sep_star.
    intuition. do 2 destruct H0. intuition.
    eapply IHl; eauto.
  Qed.

  Lemma listpred_nodup' :
    forall V T (P : T -> @pred V) l,
      (forall x y : T, {x = y} + {x <> y}) ->
      (forall (y : T) m', ~ (P y * P y)%pred m') ->
      listpred P l =p=> [[ NoDup l ]] * listpred P l.
    intros. apply lift_impl. intros. eapply listpred_nodup; eauto.
  Qed.

  Lemma listpred_remove :
    forall V T (dec : forall x y : T, {x = y} + {x <> y}) (P : T -> @pred V) (x : T) l,
      (forall (y : T) m', ~ (P y * P y)%pred m') ->
      In x l ->
      listpred P l =p=> P x * listpred P (remove dec x l).
  Proof.
    intros.
    induction l.
    cancel.
    rewrite listpred_nodup'; eauto.
    simpl; destruct (dec x a).
    cancel; inversion H2; rewrite remove_not_In; eauto.
    rewrite IHl; [ cancel | destruct H0; subst; tauto ].
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

  Lemma ptsto_conflict : forall V x (m : @mem V), ~ (x |->? * x |->?)%pred m.
  Proof.
    unfold_sep_star; firstorder discriminate.
  Qed.

  Theorem alloc_ok : forall lxp xp ms,
    {< Fm mbase m freeblocks,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms * [[ (Fm * rep xp freeblocks)%pred (list2mem m) ]]
    POST:p exists r ms', [[ p = (r, ms') ]] *
           ([[ r = None ]] * MEMLOG.rep lxp (ActiveTxn mbase m) ms' \/
            exists bn m' freeblocks', [[ r = Some bn ]] *
            MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
            [[ (Fm * bn |->? * rep xp freeblocks')%pred (list2mem m') ]])
    CRASH  MEMLOG.log_intact lxp mbase
    >} alloc lxp xp ms.
  Proof.
    unfold alloc.
    intros.
    eapply pimpl_ok2. apply alloc'_ok.
    unfold rep, rep'.
    cancel.
    step.
    inversion H.
    cancel.
    apply pimpl_or_r. right.
    norm. (* We can't just [cancel] here because it introduces evars too early *)
    inversion H.
    cancel.
    intuition.
    inversion H.
    subst; trivial.
    pred_apply.
    (* instantiate (a1 := remove (@weq addrlen) a0 l). *)
    erewrite listpred_remove with (dec := @weq addrlen). cancel.
    assert (a a3 = Avail) as Ha.
    apply H8.
    eapply remove_still_In; eauto.
    rewrite <- Ha.
    apply fupd_other.
    eapply remove_still_In_ne; eauto.
    assert (a1 <> a3).
    intro He. subst. rewrite fupd_same in *. discriminate. trivial.
    rewrite fupd_other in * by assumption.
    apply remove_other_In. assumption.
    rewrite H8; assumption.
    apply ptsto_conflict.
    rewrite H8; assumption.
  Qed.

  Theorem free_ok : forall lxp xp bn ms,
    {< Fm mbase m freeblocks,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (Fm * rep xp freeblocks * bn |->?)%pred (list2mem m) ]] *
             [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:ms' exists m', MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (Fm * rep xp (bn :: freeblocks))%pred (list2mem m') ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} free lxp xp ms bn.
  Proof.
    unfold free.
    intros.
    eapply pimpl_ok2. apply free'_ok.
    unfold rep, rep'.
    cancel.
    step.
    subst; apply fupd_same; trivial.
    rewrite H10 in H3.
    destruct (weq bn a0).
    subst; apply fupd_same; trivial.
    rewrite <- H3; apply fupd_other; assumption.
    destruct (weq bn a0).
    left. auto.
    right. rewrite fupd_other in H0 by assumption. apply H10; assumption.
  Qed.


  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.

  Hint Extern 1 ({{_}} progseq (BALLOC.alloc _ _) _) => apply BALLOC.alloc_ok : prog.
  Hint Extern 1 ({{_}} progseq (BALLOC.free _ _ _) _) => apply BALLOC.free_ok : prog.


End BALLOC.
