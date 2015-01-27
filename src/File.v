Require Import Arith.
Require Import Pred.
Require Import Word.
Require Import Prog.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import Omega.
Require Import MemLog.
Require Import Array.
Require Import List.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Rec.
Require Import Inode.
Require Import Balloc.
Require Import WordAuto.
Require Import GenSep.
Require Import ListPred.
Import ListNotations.

Set Implicit Arguments.

Module FILE.

  (* interface implementation *)

  Definition flen T lxp ixp inum ms rx : prog T :=
    n <- INODE.igetlen lxp ixp inum ms;
    rx n.

  Definition fread T lxp ixp inum off ms rx : prog T :=
    b <-INODE.iget lxp ixp inum off ms;
    fblock <- MEMLOG.read lxp b ms;
    rx fblock.

  Definition fwrite T lxp ixp inum off v ms rx : prog T :=
    b <-INODE.iget lxp ixp inum off ms;
    ok <- MEMLOG.write lxp b v ms;
    rx ok.

  Definition fgrow T lxp bxp ixp inum ms rx : prog T :=
    r <- BALLOC.alloc lxp bxp ms;
    match r with
    | (None, ms') => rx ms'
    | (Some bnum, ms') =>
        ok <- INODE.igrow lxp ixp inum bnum ms';
        rx ok
    end.

  Definition fshrink T lxp bxp ixp inum ms rx : prog T :=
    n <- INODE.igetlen lxp ixp inum ms;
    b <- INODE.iget lxp ixp inum n ms;
    ms' <- BALLOC.free lxp bxp b ms;
    r <- INODE.ishrink lxp ixp inum ms';
    rx r.


  (* representation invariants *)

  Record file := {
    FData : list valu
  }.

  Definition file0 := Build_file nil.

  Definition data_match (v : valu) a := ( a |-> v)%pred.

  Definition file_match f i : @pred valu := (
     listmatch data_match (FData f) (INODE.IBlocks i)
    )%pred.

  Definition rep bxp ixp (flist : list file) :=
    (exists freeblocks ilist,
     BALLOC.rep bxp freeblocks * INODE.rep ixp ilist *
     listmatch file_match flist ilist
    )%pred.


  Fact resolve_sel_file0 : forall l i d,
    d = file0 -> sel l i d = sel l i file0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_file0 : forall l i d,
    d = file0 -> selN l i d = selN l i file0.
  Proof.
    intros; subst; auto.
  Qed.


  Hint Rewrite resolve_sel_file0  using reflexivity : defaults.
  Hint Rewrite resolve_selN_file0 using reflexivity : defaults.

  Ltac file_bounds' := match goal with
    | [ H : ?p%pred ?mem |- length ?l <= _ ] =>
      match p with
      | context [ (INODE.rep _ ?l') ] =>
        first [ constr_eq l l'; eapply INODE.rep_bound with (m := mem)
              | eapply INODE.blocks_bound with (m := mem)
              ]; pred_apply; cancel
      end
  end.

  Ltac file_bounds := eauto; try list2mem_bound; try solve_length_eq;
                      repeat file_bounds';
                      try list2mem_bound; eauto.

  (* correctness theorems *)

  Theorem flen_ok : forall lxp bxp ixp inum ms,
    {< F A mbase m flist f,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ r = $ (length (FData f)) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} flen lxp ixp inum ms.
  Proof.
    unfold flen, rep.
    hoare.
    list2mem_ptsto_cancel; file_bounds.

    rewrite_list2mem_pred.
    destruct_listmatch.
    subst; unfold sel; auto.
    f_equal; apply eq_sym; eauto.
  Qed.


  Theorem fread_ok : forall lxp bxp ixp inum off ms,
    {<F A B mbase m flist f v,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]] *
           [[ (B * off |-> v)%pred (list2mem (FData f)) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ r = v ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} fread lxp ixp inum off ms.
  Proof.
    unfold fread, rep.
    hoare.

    list2mem_ptsto_cancel; file_bounds.
    repeat rewrite_list2mem_pred.
    destruct_listmatch.
    list2mem_ptsto_cancel; file_bounds.

    repeat rewrite_list2mem_pred.
    repeat destruct_listmatch.
    erewrite listmatch_isolate with (i := wordToNat inum); file_bounds.
    unfold file_match at 2; autorewrite with defaults.
    erewrite listmatch_isolate with (prd := data_match) (i := wordToNat off); try omega.
    unfold data_match, sel; autorewrite with defaults.
    cancel.

    unfold MEMLOG.log_intact; cancel.
  Qed.


  Lemma fwrite_ok : forall lxp bxp ixp inum off v ms,
    {<F A B mbase m flist f v0,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * inum |-> f)%pred (list2mem flist) ]] *
             [[ (B * off |-> v0)%pred (list2mem (FData f)) ]]
    POST:ms' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * inum |-> f')%pred (list2mem flist') ]] *
             [[ (B * off |-> v)%pred (list2mem (FData f')) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} fwrite lxp ixp inum off v ms.
  Proof.
    unfold fwrite, rep.
    step.
    list2mem_ptsto_cancel; file_bounds.
    repeat rewrite_list2mem_pred.
    destruct_listmatch.
    list2mem_ptsto_cancel; file_bounds.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.

    (* constructing new file and disk *)
    instantiate (a := upd d0 off v).
    instantiate (a1 := Build_file (upd (FData f) off v)).

    admit. (* MEMLOG layer should have lemma for this *)

    2: eapply list2mem_upd; eauto.
    2: simpl; eapply list2mem_upd; eauto.

    repeat rewrite_list2mem_pred.
    admit.
  Qed.


  Theorem fgrow_ok : forall lxp bxp ixp inum ms,
    {< F A mbase m flist f,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (FData f) < INODE.blocks_per_inode ]] *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:ms' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * inum |-> f')%pred (list2mem flist') ]] *
             [[ length (FData f') = length (FData f) + 1 ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} fgrow lxp bxp ixp inum ms.
  Proof.
    unfold fgrow, rep.
    (* step doesn't work? *)
    hoare.

    destruct_listmatch.
    destruct (r_); simpl; step.


    (* FIXME: where are these evars from? *)
    instantiate (a5:=INODE.inode0).
    instantiate (a0:=emp).
    instantiate (a1:=fun _ => True).

    2: list2mem_ptsto_cancel; file_bounds.
    rewrite_list2mem_pred; file_bounds.
    eapply list2mem_array; file_bounds.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.
    apply pimpl_or_r; left; cancel.
    apply pimpl_or_r; right; cancel.

    instantiate (a1 := Build_file (FData f ++ [w0])).
    2: simpl; eapply list2mem_upd; eauto.
    2: simpl; rewrite app_length; simpl; eauto.

    rewrite_list2mem_pred_upd H15; file_bounds.
    subst; unfold upd.
    eapply listmatch_updN_selN_r; autorewrite with defaults; file_bounds.
    unfold file_match; cancel_exact; simpl.

    inversion H10; clear H10; subst.
    eapply list2mem_array_app_eq in H14 as Heq; eauto.
    rewrite Heq; clear Heq.
    rewrite_list2mem_pred_sel H4; subst f.
    eapply listmatch_app_r; file_bounds.
    repeat rewrite_list2mem_pred.

    destruct_listmatch.
    instantiate (bd := INODE.inode0).
    instantiate (b := natToWord addrlen INODE.blocks_per_inode); file_bounds.
    eapply INODE.blocks_bound in H13 as Heq; unfold sel in Heq.
    rewrite selN_updN_eq in Heq; file_bounds.
  Qed.


  Theorem fshrink_ok : forall lxp bxp ixp inum,
    {< F A mbase m flist f,
    PRE    LOG.rep lxp (ActiveTxn mbase m) *
           [[ length (FData f) > 0 ]] *
           [[ (F * rep bxp ixp flist)%pred m ]] *
           [[ (A * inum |-> f)%pred (list2mem flist) ]]
    POST:r [[ r = false ]] * (exists m', LOG.rep lxp (ActiveTxn mbase m')) \/
           [[ r = true  ]] * exists m' flist' f',
           LOG.rep lxp (ActiveTxn mbase m') *
           [[ (F * rep bxp ixp flist')%pred m' ]] *
           [[ (A * inum |-> f')%pred (list2mem flist') ]] *
           [[ length (FData f') = length (FData f) - 1 ]]
    CRASH  LOG.log_intact lxp mbase
    >} fshrink lxp bxp ixp inum.
  Proof.
    admit.
  Qed.

End FILE.
