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

Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
    BmapStart : addr;
  BmapNBlocks : addr
}.

Module BALLOC.
  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_to_valu a pos : valu :=
    match a with
    | Avail => $0
    | InUse => wbit _ ($ pos : addr)
    end.

  Definition blockbits (bmap : addr -> alloc_state) offset :=
    fold_right (@wor _) $0
               (map (fun i => alloc_state_to_valu (bmap $ (offset + i)) i)
                    (seq 0 valulen)).

  Definition rep xp (bmap : addr -> alloc_state) :=
    array (BmapStart xp)
          (map (fun nblock => blockbits bmap (nblock * valulen))
               (seq 0 (wordToNat (BmapNBlocks xp)))) $1.

  Theorem selN_list_eq' : forall len vs vs',
    length vs = len
    -> length vs' = len
    -> (forall i, i < len -> selN vs i = selN vs' i)
    -> vs = vs'.
  Proof.
    induction len.
    - destruct vs; destruct vs'; simpl; intros; try congruence.
    - destruct vs; destruct vs'; simpl; intros; try congruence.
      f_equal.
      apply (H1 0); omega.
      apply IHlen; eauto.
      intros.
      apply (H1 (S i)); omega.
  Qed.

  Theorem selN_list_eq : forall vs vs',
    length vs = length vs'
    -> (forall i, i < length vs -> selN vs i = selN vs' i)
    -> vs = vs'.
  Proof.
    intros.
    eapply selN_list_eq'; [ apply eq_refl | auto | auto ].
  Qed.

  Theorem selN_map_seq' : forall i n f base, i < n
    -> selN (map f (seq base n)) i = f (i + base).
  Proof.
    induction i; destruct n; simpl; intros; try omega; auto.
    replace (S (i + base)) with (i + (S base)) by omega.
    apply IHi; omega.
  Qed.

  Theorem selN_map_seq : forall i n f, i < n
    -> selN (map f (seq 0 n)) i = f i.
  Proof.
    intros.
    replace i with (i + 0) at 2 by omega.
    apply selN_map_seq'; auto.
  Qed.

  Theorem selN_updN_ne : forall vs n n' v, n < length vs
    -> n <> n'
    -> selN (updN vs n v) n' = selN vs n'.
  Proof.
    induction vs; destruct n'; destruct n; simpl; intuition; try omega.
  Qed.

  Hint Rewrite length_updN.
  Hint Rewrite map_length.
  Hint Rewrite seq_length.

  Theorem blockbits_bupd_other : forall bmap bn x i bnblock,
    (bnblock ^* $ valulen <= bn)%word
    -> (bn < bnblock ^* $ valulen ^+ $ valulen)%word
    -> i <> wordToNat bnblock
    -> blockbits (fupd bmap bn x) (i * valulen) = blockbits bmap (i * valulen).
  Proof.
    unfold blockbits.
    intros.
    f_equal.
    apply selN_list_eq; autorewrite with core; auto.

    intros.
    repeat rewrite selN_map_seq; auto.
    f_equal.
    rewrite fupd_other; auto.
    unfold not in *; intros; apply H1; clear H1; subst.
    admit.
  Qed.

  Theorem valulen_bound : valulen <= wordToNat ($ valulen : addr).
  Proof.
    rewrite wordToNat_natToWord_idempotent'; auto.
    rewrite valulen_is.
    unfold addrlen.
    unfold pow2; omega.
  Qed.

  Theorem wordToNat_wminus : forall sz (a b : word sz), (b <= a)%word
    -> wordToNat (a ^- b) = wordToNat a - wordToNat b.
  Proof.
    admit.
  Qed.

  Theorem blockbits_bupd_same_avail': forall vlen start bmap bn bnblock,
    start + vlen = valulen
    -> (bnblock ^* $ valulen <= bn)%word
    -> (bn < bnblock ^* $ valulen ^+ $ valulen)%word
    -> fold_right (wor (sz:=valulen)) $ (0)
         (map (fun i : nat => alloc_state_to_valu (bmap $ (wordToNat bnblock * valulen + i)) i)
            (seq start vlen)) ^& wnot (wbit valulen (bn ^- bnblock ^* $ (valulen))) =
       fold_right (wor (sz:=valulen)) $ (0)
         (map
            (fun i : nat =>
             alloc_state_to_valu (fupd bmap bn Avail $ (wordToNat bnblock * valulen + i)) i)
            (seq start vlen)).
  Proof.
    induction vlen; simpl; intros.
    rewrite wand_kill; auto.
    rewrite wand_or_distr; f_equal.
    - destruct (weq bn $ (wordToNat bnblock * valulen + start)).
      + subst. rewrite fupd_same; auto. simpl.
        destruct (bmap $ (wordToNat bnblock * valulen + start)); simpl; try apply wand_kill.
        replace ($ (wordToNat bnblock * valulen + start) ^- bnblock ^* $ valulen)
          with ($ start : addr) by words.
        rewrite wbit_and_not; auto.
        clear H0 H1 IHvlen.
        erewrite wordToNat_natToWord_bound; try omega.
        eapply le_trans; [| apply valulen_bound ].
        omega.
      + rewrite fupd_other; auto.
        destruct (bmap $ (wordToNat bnblock * valulen + start)); simpl; try apply wand_kill.
        rewrite wbit_and_not_other; auto.
        erewrite wordToNat_natToWord_bound; try omega.
        eapply le_trans; [| apply valulen_bound ]; omega.

        rewrite wordToNat_wminus; auto.
        apply wlt_lt in H1.
        admit.

        unfold not in *; intros; apply n.
        rewrite natToWord_plus.
        rewrite H2.
        words.
    - apply IHvlen; auto; omega.
  Qed.

  Theorem blockbits_bupd_same_avail : forall bmap bn bnblock,
    (bnblock ^* $ valulen <= bn)%word
    -> (bn < bnblock ^* $ valulen ^+ $ valulen)%word
    -> blockbits bmap (wordToNat bnblock * valulen)
         ^& wnot (wbit valulen (bn ^- bnblock ^* $ (valulen))) =
       blockbits (fupd bmap bn Avail) (wordToNat bnblock * valulen).
  Proof.
    intros.
    unfold blockbits.
    rewrite blockbits_bupd_same_avail'; auto.
  Qed.

  Theorem blockbits_bupd_same_inuse : forall bmap bn bnblock,
    (bnblock ^* $ valulen <= bn)%word
    -> (bn < bnblock ^* $ valulen ^+ $ valulen)%word
    -> blockbits bmap (wordToNat bnblock * valulen)
         ^| wbit valulen (bn ^- bnblock ^* $ valulen) =
       blockbits (fupd bmap bn InUse) (wordToNat bnblock * valulen).
  Proof.
    intros.
    unfold blockbits.
    admit.
  Qed.

  Theorem upd_bupd_avail : forall bmap astart nblocks bn bnblock oldblocks,
    (bn >= bnblock ^* $ valulen)%word
    -> (bn < bnblock ^* $ valulen ^+ $ valulen)%word
    -> (bnblock < nblocks)%word
    -> oldblocks = (map (fun nblock => blockbits bmap (nblock * valulen))
                        (seq 0 (wordToNat nblocks)))
    -> array astart (upd oldblocks bnblock
                         (sel oldblocks bnblock ^&
                          wnot (wbit valulen (bn ^- bnblock ^* $ valulen)))) =
       array astart
         (map (fun nblock => blockbits (fupd bmap bn Avail) (nblock * valulen))
              (seq 0 (wordToNat nblocks))).
  Proof.
    intros.
    f_equal.
    unfold upd.
    apply selN_list_eq.
    - subst; autorewrite with core. auto.
    - unfold sel; intros.
      apply wlt_lt in H1 as H1'.
      destruct (eq_nat_dec (wordToNat bnblock) i); subst.
      + rewrite selN_updN_eq; autorewrite with core; auto.
        repeat rewrite selN_map_seq; auto.
        erewrite blockbits_bupd_same_avail; eauto.
      + rewrite selN_updN_ne; autorewrite with core; auto.
        autorewrite with core in *.
        repeat rewrite selN_map_seq; auto.
        erewrite blockbits_bupd_other; eauto.
  Qed.

  Theorem upd_bupd_inuse : forall bmap astart nblocks bnblock bnoff oldblocks,
    (bnoff < $ valulen)%word
    -> (bnblock < nblocks)%word
    -> oldblocks = (map (fun nblock => blockbits bmap (nblock * valulen))
                        (seq 0 (wordToNat nblocks)))
    -> array astart (upd oldblocks bnblock
                         (sel oldblocks bnblock ^| wbit valulen bnoff)) =
       array astart
         (map (fun nblock => blockbits (fupd bmap (bnblock ^* $ valulen ^+ bnoff) InUse)
                                       (nblock * valulen))
              (seq 0 (wordToNat nblocks))).
  Proof.
    intros.
    f_equal.
    unfold upd.
    apply selN_list_eq.
    - subst; autorewrite with core. auto.
    - unfold sel; intros.
      apply wlt_lt in H0 as H0'.
      destruct (eq_nat_dec (wordToNat bnblock) i); subst.
      + rewrite selN_updN_eq; autorewrite with core; auto.
        repeat rewrite selN_map_seq; auto.
        replace (bnoff) with ((bnblock ^* $ valulen ^+ bnoff) ^- bnblock ^* $ valulen) at 1 by ring.
        erewrite blockbits_bupd_same_inuse; eauto.
        admit.
        admit.
      + rewrite selN_updN_ne; autorewrite with core; auto.
        autorewrite with core in *.
        repeat rewrite selN_map_seq; auto.
        erewrite blockbits_bupd_other; eauto.
        admit.
        admit.
  Qed.

  Definition free T lxp xp bn rx : prog T :=
    For i < (BmapNBlocks xp)
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        LOG.rep lxp (ActiveTxn mbase m) * [[ (i ^* $ valulen <= bn)%word ]]
      OnCrash
        LOG.log_intact lxp mbase
      Begin
        If (wlt_dec bn (i ^* $ valulen ^+ $ valulen)) {
          b <- LOG.read_array lxp (BmapStart xp) i $1 ;
          ok <- LOG.write_array lxp (BmapStart xp) i $1
                (b ^& wnot (wbit _ (bn ^- (i ^* $ valulen)))) ;
          rx ok
        } else {
          lrx tt
        }
    Rof ;;
    rx false.

  Theorem free_ok : forall lxp xp bn,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (Fm * rep xp bmap)%pred m ]] *
           [[ (bn < BmapNBlocks xp ^* $ valulen)%word ]]
    POST:r ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep xp (fupd bmap bn Avail))%pred m' ]]) \/
           ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m))
    CRASH  LOG.log_intact lxp mbase
    >} free lxp xp bn.
  Proof.
    unfold free, rep, LOG.log_intact.
    hoare.

    apply wlt_lt in H2.
    ring_simplify ($ 0 ^* $ valulen : addr) in H2; simpl in H2; omega.

    eexists; pred_apply. cancel.

    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.

    eapply pimpl_or_r; left.
    cancel.
    erewrite upd_bupd_avail; eauto.

    rewrite wmult_plus_distr in *.
    rewrite wmult_unit in *.
    auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (free _ _ _) _) => apply free_ok : prog.

  Definition alloc T lxp xp rx : prog T :=
    For i < (BmapNBlocks xp)
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        LOG.rep lxp (ActiveTxn mbase m)
      OnCrash
        LOG.log_intact lxp mbase
      Begin
        blk <- LOG.read_array lxp (BmapStart xp) i $1;

        For j < $ valulen
          Ghost mbase' m'
          Loopvar _ <- tt
          Continuation lrx_inner
          Invariant
            LOG.rep lxp (ActiveTxn mbase' m')
          OnCrash
            LOG.log_intact lxp mbase'
          Begin
            If (weq (blk ^& wbit _ j) $0) {
              ok <- LOG.write_array lxp (BmapStart xp) i $1 (blk ^| wbit _ j) ;
              If (bool_dec ok true) {
                rx (Some (i ^* $ valulen ^+ j))
              } else {
                rx None
              }
            } else {
              lrx_inner tt
            }
          Rof;;
        lrx tt
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
*)

  Theorem sel_avail : forall bmap bnblock bnoff nblocks,
     sel (map (fun nblock => blockbits bmap (nblock * valulen))
              (seq 0 (wordToNat nblocks))) bnblock ^& wbit valulen bnoff = $ 0
    -> (bnblock < nblocks)%word
    -> (bnoff < $ valulen)%word
    -> bmap (bnblock ^* $ valulen ^+ bnoff) = Avail.
  Proof.
    unfold sel; intros.
    apply wlt_lt in H0 as H0'.
    rewrite selN_map_seq in H; auto.
    admit.
  Qed.

  Theorem alloc_ok: forall lxp xp,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) * [[ (Fm * rep xp bmap)%pred m ]]
    POST:r [[ r = None ]] * LOG.rep lxp (ActiveTxn mbase m) \/
           exists bn m', [[ r = Some bn ]] * [[ bmap bn = Avail ]] *
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (Fm * rep xp (fupd bmap bn InUse))%pred m' ]]
    CRASH  LOG.log_intact lxp mbase
    >} alloc lxp xp.
  Proof.
    unfold alloc, rep, LOG.log_intact.
    hoare.

    eexists. pred_apply. cancel.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.

    apply pimpl_or_r. right.
    cancel.

    eapply sel_avail; eauto.
    erewrite upd_bupd_inuse; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (alloc _) _) => apply alloc_ok : prog.

(*
  Theorem free_recover_ok : forall lxp xp bn,
    {< Fm mbase m bmap,
    PRE     LOG.rep lxp (ActiveTxn mbase m) *
            [[ (Fm * rep xp bmap)%pred m ]] *
            [[ (bn < BmapLen xp)%word ]]
    POST:r  [[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m) \/
            [[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep xp (bupd bmap bn Avail))%pred m' ]]
    CRASH:r LOG.rep lxp (NoTransaction mbase)
    IDEM    LOG.log_intact lxp mbase
    >} free lxp xp bn >> LOG.recover lxp.
  Proof.
    intros.
    eapply pimpl_ok3.
    eapply corr3_from_corr2.
    eapply free_ok.
    eapply LOG.recover_ok.

    cancel.
    cancel.
    hoare.
    cancel.
    cancel.
    hoare.
  Qed.
*)

End BALLOC.
