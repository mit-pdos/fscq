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

Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
  BmapStart : addr;
    BmapLen : addr
}.

Module BALLOC.
  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_to_valu a : valu :=
    match a with
    | Avail => $0
    | InUse => $1
    end.

  Definition rep xp (bmap : addr -> alloc_state) :=
    array (BmapStart xp)
          (map (fun i => alloc_state_to_valu (bmap $ i)) (seq 0 (wordToNat (BmapLen xp)))).

  Definition free lxp xp bn rx :=
    ok <- LOG.write_array lxp (BmapStart xp) bn (natToWord valulen 0);
    rx ok.

  Definition bupd (m : addr -> alloc_state) n a :=
    fun n' => if addr_eq_dec n n' then a else m n'.

  Lemma bupd_same: forall m n n' a,
    n = n' -> bupd m n a n' = a.
  Proof.
    intros; unfold bupd; destruct (addr_eq_dec n n'); congruence.
  Qed.

  Lemma bupd_other: forall m n n' a,
    n <> n' -> bupd m n a n' = m n'.
  Proof.
    intros; unfold bupd; destruct (addr_eq_dec n n'); congruence.
  Qed.

  Lemma upd_bupd_outb : forall len a bn s start (bound : addr),
    start > wordToNat bn ->
    start + len <= wordToNat bound ->
    map (fun i => alloc_state_to_valu (a $ i)) (seq start len) =
    map (fun i => alloc_state_to_valu (bupd a bn s $ i)) (seq start len).
  Proof.
    induction len; auto.
    simpl; intros.
    f_equal.
    - f_equal.
      rewrite bupd_other; auto.
      unfold not; intros; subst bn.
      erewrite wordToNat_natToWord_bound in H; try omega.
      instantiate (1:=bound).
      omega.
    - apply IHlen with (bound:=bound); omega.
  Qed.

  Theorem upd_bupd' : forall len a bn v s start (bound1 : addr) (bound2 : addr),
    start + len <= wordToNat bound1 ->
    start + wordToNat bn <= wordToNat bound2 ->
    v = alloc_state_to_valu s ->
    upd (map (fun i => alloc_state_to_valu (a $ i)) (seq start len)) bn v =
    map (fun i => alloc_state_to_valu (bupd a (bn ^+ $ start) s $ i)) (seq start len).
  Proof.
    simpl.
    induction len; intros.
    (* len = 0 *)
    simpl.
    unfold upd, updN.
    auto.
    (* some len *)
    simpl.
    unfold upd, updN.
    destruct (wordToNat bn) eqn:bn'.
    (* bn = 0 *)
    assert (bn = wzero addrlen) by ( apply wordToNat_eq_natToWord; auto ).
    f_equal.
    subst.
    ring_simplify (wzero addrlen ^+ $ (start)).
    unfold bupd.
    destruct (addr_eq_dec $ (start) $ (start)).
    auto.
    congruence.
    (* bn = 0, rest of list *)
    erewrite <- upd_bupd_outb; auto.
    subst.
    ring_simplify (wzero addrlen ^+ $ (start)).
    erewrite wordToNat_natToWord_bound; try omega.
    eapply le_trans; [|eauto]; omega.
    instantiate (1:=bound1).
    omega.
    (* bn != 0 *)
    f_equal.
    f_equal.
    rewrite bupd_other; auto.
    unfold not; intros.
    assert (bn ^+ $ start ^- $ start = $ start ^- $ start) by ( rewrite H2; auto ); clear H2.
    rewrite wminus_def in H3.
    rewrite <- wplus_assoc in H3.
    rewrite <- wminus_def in H3.
    replace ($ (start) ^- $ (start)) with (wzero addrlen) in H3 by ring.
    replace (bn ^+ wzero addrlen) with (bn) in H3 by ring.
    rewrite H3 in bn'.
    rewrite roundTrip_0 in bn'.
    congruence.
    fold updN.
    replace (bn ^+ $ (start)) with ((bn ^- $ 1) ^+ $ (S start)).

    assert (wordToNat (bn ^- $ (1)) = n).
    rewrite wminus_Alt. rewrite wminus_Alt2. unfold wordBinN.
    erewrite wordToNat_natToWord_bound.
    rewrite bn'. unfold addrlen; rewrite roundTrip_1. omega.
    rewrite bn'. instantiate (1:=bound2). omega.
    unfold not; intros. apply wlt_lt in H2. rewrite bn' in H2. simpl in H2. omega.

    rewrite <- IHlen with (v:=v) (bound1:=bound1) (bound2:=bound2).
    unfold upd.
    f_equal.
    auto.
    omega.
    rewrite H2; omega.

    assumption.
    rewrite natToWord_S with (n:=start). ring.
  Qed.

  Theorem upd_bupd : forall (len : addr) a bn v s,
    v = alloc_state_to_valu s ->
    upd (map (fun i => alloc_state_to_valu (a $ i)) (seq 0 (wordToNat len))) bn v =
    map (fun i => alloc_state_to_valu (bupd a bn s $ i)) (seq 0 (wordToNat len)).
  Proof.
    intros.
    replace (bn) with (bn ^+ $0).
    replace (bn ^+ $0) with (bn) at 1.
    eapply upd_bupd'.
    instantiate (1:=len); omega.
    instantiate (1:=bn); omega.
    auto.
    replace ($0) with (wzero addrlen) by auto; ring.
    replace ($0) with (wzero addrlen) by auto; ring.
  Qed.

  Theorem free_ok : forall lxp xp bn,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ (Fm * rep xp bmap)%pred m ]] *
           [[ (bn < BmapLen xp)%word ]]
    POST:r ([[ r = true ]] * exists m', LOG.rep lxp (ActiveTxn mbase m') *
            [[ (Fm * rep xp (bupd bmap bn Avail))%pred m' ]]) \/
           ([[ r = false ]] * LOG.rep lxp (ActiveTxn mbase m))
    CRASH  LOG.log_intact lxp mbase
    >} free lxp xp bn.
  Proof.
    unfold free, rep, LOG.log_intact.
    hoare.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.
    eapply pimpl_or_r; left.
    erewrite <- upd_bupd; [|eauto].
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (free _ _ _) _) => apply free_ok : prog.

  Definition alloc lxp xp rx :=
    For i < (BmapLen xp)
      Ghost mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        LOG.rep lxp (ActiveTxn mbase m)
      OnCrash
        LOG.log_intact lxp mbase
      Begin
        f <- LOG.read_array lxp (BmapStart xp) i;
        If (weq f $0) {
          ok <- LOG.write_array lxp (BmapStart xp) i $1;
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

  Theorem alloc_ok: forall lxp xp,
    {< Fm mbase m bmap,
    PRE    LOG.rep lxp (ActiveTxn mbase m) * [[ (Fm * rep xp bmap)%pred m ]]
    POST:r [[ r = None ]] * LOG.rep lxp (ActiveTxn mbase m) \/
           exists bn m', [[ r = Some bn ]] * [[ bmap bn = Avail ]] *
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (Fm * rep xp (bupd bmap bn InUse))%pred m' ]]
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
    rewrite natToWord_wordToNat; eauto.

    erewrite <- upd_bupd; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (alloc _) _) => apply alloc_ok : prog.

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

End BALLOC.
