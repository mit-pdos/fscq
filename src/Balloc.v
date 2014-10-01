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

  Theorem free_ok : forall lxp xp bn rx rec,
    {{ exists F Fm mbase m bmap, F * LOG.rep lxp (ActiveTxn mbase m)
     * [[ (Fm * rep xp bmap)%pred m ]]
     * [[ (bn < BmapLen xp)%word ]]
     * [[ {{ exists m', F * LOG.rep lxp (ActiveTxn mbase m')
           * [[ (Fm * rep xp (bupd bmap bn Avail))%pred m' ]] }} rx true >> LOG.recover lxp ;; rec tt ]]
     * [[ {{ F * LOG.rep lxp (ActiveTxn mbase m) }} rx false >> LOG.recover lxp ;; rec tt ]]
     * [[ {{ F * LOG.rep lxp (NoTransaction mbase) }} rec tt >> LOG.recover lxp ;; rec tt ]]
    }} free lxp xp bn rx >> LOG.recover lxp ;; rec tt.
  Proof.
    unfold free, rep.
    step.
    pred_apply; cancel.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.
    step.
    erewrite <- upd_bupd; [|eauto].
    pred_apply; cancel.
    step.

    (* XXX LOG.recover infinite loop... *)
    admit.
  Qed.

  Definition alloc lxp xp rx :=
    For i < (BmapLen xp)
      Ghost F mbase m
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        F * LOG.rep lxp (ActiveTxn mbase m)
      OnCrash
        any
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

  Theorem sel_avail : forall a bn len, (bn < len)%word ->
    sel (map (fun i => alloc_state_to_valu (a $ i)) (seq 0 (wordToNat len))) bn = $0 ->
    a bn = Avail.
  Admitted.

  Theorem alloc_ok: forall lxp xp rx rec,
    {{ exists F Fm mbase m bmap, F * LOG.rep lxp (ActiveTxn mbase m)
     * [[ (Fm * rep xp bmap)%pred m ]]
     * [[ forall bn, bmap bn = Avail
          -> {{ exists m', F * LOG.rep lxp (ActiveTxn mbase m')
              * [[ (Fm * rep xp (bupd bmap bn InUse))%pred m' ]] }} rx (Some bn) >> LOG.recover lxp rec ]]
     * [[ {{ F * LOG.rep lxp (ActiveTxn mbase m) }} rx None >> LOG.recover lxp rec ]]
     * [[ {{ F * LOG.rep lxp (NoTransaction mbase) }} rec tt >> LOG.recover lxp rec ]]
    }} alloc lxp xp rx >> LOG.recover lxp rec.
  Proof.
    unfold alloc, rep.
    step.
    step.
    eexists. pred_apply. cancel.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.
    step.
    step.
    pred_apply. cancel.
    rewrite map_length. rewrite seq_length. apply wlt_lt. auto.

    (* XXX interesting case: there are two possible hoare tuples about
     * the continuation [rx], and [eauto with prog] picks the wrong one:
     * it chooses [rx None] when we should be using [rx (Some bn)].
     *)
    eapply pimpl_ok_cont.
    match goal with
    | [ H: forall bn, _ -> {{ _ }} rx (Some bn) >> _ |- _ ] => apply H
    end.

    eapply sel_avail; [| eauto ]; auto.

    cancel.

(* XXX broke because change in upd_bupd
    pred_apply. erewrite <- upd_bupd. cancel.
    apply wlt_lt; auto.
    eauto.

    cancel.

    step.

    (* XXX recovery loop *)
    admit.

    step.

    (* XXX recovery loop *)
    admit.

    step.
  Qed.
*)

  Admitted.



End BALLOC.
