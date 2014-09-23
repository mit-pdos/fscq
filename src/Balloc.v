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

Set Implicit Arguments.


(* Block allocator *)

Record xparams := {
  BmapStart : addr;
    BmapLen : nat
}.

Module Balloc.
  Inductive alloc_state :=
  | Avail
  | InUse.

  Definition alloc_state_to_bit a : valu :=
    match a with
    | Avail => $0
    | InUse => $1
    end.

  Definition rep xp (bmap : addr -> alloc_state) :=
    array (BmapStart xp) (map (fun i => alloc_state_to_bit (bmap $ i)) (seq 0 (BmapLen xp))).

  Definition free lxp xp bn rx :=
    ok <- LOG.write_array lxp (BmapStart xp) bn (natToWord valulen 0);
    rx ok.

  Definition bupd (m : addr -> alloc_state) n a :=
    fun n' => if addr_eq_dec n n' then a else m n'.

  Theorem upd_bupd : forall a bn len, wordToNat bn < len ->
    upd (map (fun i => alloc_state_to_bit (a $ i)) (seq 0 len)) bn $0 =
    map (fun i => alloc_state_to_bit (bupd a bn Avail $ i)) (seq 0 len).
  Admitted.

  Theorem free_ok : forall lxp xp bn rx rec,
    {{ exists F Fm mbase m bmap, F * LOG.rep lxp (ActiveTxn mbase m)
     * [[ (Fm * rep xp bmap)%pred m ]]
     * [[ wordToNat bn < BmapLen xp ]]
     * [[ {{ exists m', F * LOG.rep lxp (ActiveTxn mbase m')
           * [[ (Fm * rep xp (bupd bmap bn Avail))%pred m' ]] }} rx true >> LOG.recover lxp ;; rec tt ]]
     * [[ {{ F * LOG.rep lxp (ActiveTxn mbase m) }} rx false >> LOG.recover lxp ;; rec tt ]]
     * [[ {{ F * LOG.rep lxp (NoTransaction mbase) }} rec tt >> LOG.recover lxp ;; rec tt ]]
    }} free lxp xp bn rx >> LOG.recover lxp ;; rec tt.
  Proof.
    unfold free, rep.
    step.
    pred_apply; cancel.
    rewrite map_length. rewrite seq_length. auto.

    step.
    rewrite <- upd_bupd; eauto.
    pred_apply; cancel.

    step.

    (* XXX LOG.recover infinite loop... *)
    admit.
  Qed.

  Definition alloc xp rx :=
    For i < (BmapLen xp)
      Ghost bmap
      Loopvar _ <- tt
      Continuation lrx
      Invariant
        rep xp bmap
      OnCrash
        any
        (* XXX figure out how to wrap this in transactions,
         * so we don't have to specify crash cases.. *)
      Begin
        f <- !(BmapStart xp + i);
        If (eq_nat_dec f 0) {
          (BmapStart xp + i) <-- 1;; rx (Some i)
        } else {
          lrx tt
        }
    Rof;;
    rx None.

  Theorem alloc_ok: forall xp rx rec,
    {{ exists F bmap, F * rep xp bmap
     * [[ exists bn, bmap bn = Avail
          -> {{ F * rep xp (bupd bmap bn InUse) }} rx (Some bn) >> rec ]]
     * [[ {{ F * rep xp bmap }} rx None >> rec ]]
     * [[ {{ any }} rec >> rec ]]
    }} alloc xp rx >> rec.
  Proof.
    unfold alloc, rep.

    intros.
    eapply pimpl_ok.
    eauto with prog.
    norm.
    cancel.
    intuition.
    (* XXX again, if intuition goes first, it mismatches existential variables *)

    cancel.

    step.
    (* XXX need to extract a bitmap entry *)
  Abort.

End Balloc.
