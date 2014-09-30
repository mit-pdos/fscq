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

  Lemma updN_split: forall a l n v,
    (updN (a :: l) n v) = (updN (a::nil) n v) ++ (updN l n v).
  Proof.
  Admitted.

  Lemma upd_bupd_outb : forall a bn s len start, 
    start = S(wordToNat bn) -> 
    map (fun i => alloc_state_to_valu (a $ i)) (seq start len) =
    map (fun i => alloc_state_to_valu (bupd a bn s $ i)) (seq start len).
   Proof.
   Admitted.
  

  Theorem upd_bupd : forall len a bn v s start, 
    start <= wordToNat bn -> 
    wordToNat bn < start + len ->
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
    assert (bn = wzero addrlen) by admit.
    f_equal.
    subst.
    ring_simplify (wzero addrlen ^+ $ (start)).
    unfold bupd.
    destruct (addr_eq_dec $ (start) $ (start)).
    auto.
    congruence.
    (* bn = 0, rest of list *)
    rewrite <- upd_bupd_outb.
    auto.
    subst.
    ring_simplify (wzero addrlen ^+ $ (start)). 
    admit.
    (* bn != 0 *) 
    f_equal.
    f_equal.
    admit.
    fold updN.
    replace (bn ^+ $ (start)) with ((bn ^- $ 1) ^+ $ (S start)).
    erewrite <- IHlen.
    unfold upd.
    f_equal.
    admit.
    admit.
    admit.
    assumption.
    admit.
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
(* XXX broke because updated upd_bupd 
    erewrite <- upd_bupd; [| apply wlt_lt; eauto | eauto ].
    pred_apply; cancel.

    step.
    admit.

    (* XXX LOG.recover infinite loop... *)
    admit.
  Qed.
*)
  Admitted.

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
