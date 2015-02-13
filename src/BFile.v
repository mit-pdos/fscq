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
Require Import GenSepN.
Require Import ListPred.
Import ListNotations.

Set Implicit Arguments.

Module BFILE.

  (* interface implementation *)

  Definition bflen T lxp ixp inum ms rx : prog T :=
    n <- INODE.ilen lxp ixp inum ms;
    rx n.

  Definition bfread T lxp ixp inum off ms rx : prog T :=
    b <-INODE.iget lxp ixp inum off ms;
    fblock <- MEMLOG.read lxp b ms;
    rx fblock.

  Definition bfwrite T lxp ixp inum off v ms rx : prog T :=
    b <-INODE.iget lxp ixp inum off ms;
    ok <- MEMLOG.write lxp b v ms;
    rx ok.

  Definition bfgrow T lxp bxp ixp inum ms rx : prog T :=
    r <- BALLOC.alloc lxp bxp ms;
    let (bn, ms) := r in
    match bn with
    | None => rx (false, ms)
    | Some bnum =>
        r <- INODE.igrow lxp bxp ixp inum bnum ms;
        rx r
    end.

  Definition bfshrink T lxp bxp ixp inum ms rx : prog T :=
    n <- INODE.ilen lxp ixp inum ms;
    b <- INODE.iget lxp ixp inum (n ^- $1) ms;
    ms <- BALLOC.free lxp bxp b ms;
    ms <- INODE.ishrink lxp bxp ixp inum ms;
    rx ms.


  (* representation invariants *)

  Record bfile := {
    BFData : list valu
  }.

  Definition bfile0 := Build_bfile nil.

  Definition data_match bxp (v : valu) a : @pred _ (@weq addrlen) _ :=
    (a |-> v * [[ BALLOC.valid_block bxp a ]])%pred.

  Definition file_match bxp f i :=
    listmatch (data_match bxp) (BFData f) (INODE.IBlocks i).

  Definition rep bxp ixp (flist : list bfile) :=
    (exists freeblocks ilist,
     BALLOC.rep bxp freeblocks * INODE.rep bxp ixp ilist *
     listmatch (file_match bxp) flist ilist
    )%pred.


  Fact resolve_sel_bfile0 : forall l i d,
    d = bfile0 -> sel l i d = sel l i bfile0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_bfile0 : forall l i d,
    d = bfile0 -> selN l i d = selN l i bfile0.
  Proof.
    intros; subst; auto.
  Qed.


  Hint Rewrite resolve_sel_bfile0  using reflexivity : defaults.
  Hint Rewrite resolve_selN_bfile0 using reflexivity : defaults.

  Ltac file_bounds' := match goal with
    | [ H : ?p%pred ?mem |- length ?l <= _ ] =>
      match p with
      | context [ (INODE.rep _ _ ?l') ] =>
        first [ constr_eq l l'; eapply INODE.rep_bound with (m := mem)
              | eapply INODE.blocks_bound with (m := mem)
              ]; pred_apply; cancel
      end
  end.

  Ltac file_bounds := eauto; try list2nmem_bound; try solve_length_eq;
                      repeat file_bounds';
                      try list2nmem_bound; eauto.

  (* correctness theorems *)

  Theorem bflen_ok : forall lxp bxp ixp inum ms,
    {< F A mbase m flist f,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ r = $ (length (BFData f)) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bflen lxp ixp inum ms.
  Proof.
    unfold bflen, rep.
    hoare.
    list2nmem_ptsto_cancel; file_bounds.

    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    subst; unfold sel; auto.
    f_equal; apply eq_sym; eauto.
  Qed.


  Theorem bfread_ok : forall lxp bxp ixp inum off ms,
    {<F A B mbase m flist f v,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFData f)) ]]
    POST:r MEMLOG.rep lxp (ActiveTxn mbase m) ms *
           [[ r = v ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bfread lxp ixp inum off ms.
  Proof.
    unfold bfread, rep.
    hoare.

    list2nmem_ptsto_cancel; file_bounds.
    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    list2nmem_ptsto_cancel; file_bounds.

    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    erewrite listmatch_isolate with (i := wordToNat inum) by file_bounds.
    unfold file_match at 2; autorewrite with defaults.
    erewrite listmatch_isolate with (prd := data_match bxp) (i := wordToNat off) by file_bounds.
    unfold data_match, sel; autorewrite with defaults.
    cancel.

    unfold MEMLOG.log_intact; cancel.
  Qed.


  Lemma bfwrite_ok : forall lxp bxp ixp inum off v ms,
    {<F A B mbase m flist f v0,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (B * #off |-> v0)%pred (list2nmem (BFData f)) ]]
    POST:ms' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ (B * #off |-> v)%pred (list2nmem (BFData f')) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bfwrite lxp ixp inum off v ms.
  Proof.
    unfold bfwrite, rep.
    step.
    list2nmem_ptsto_cancel; file_bounds.
    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    list2nmem_ptsto_cancel; file_bounds.

    step.
    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    erewrite listmatch_isolate with (i := wordToNat inum) by file_bounds.
    unfold file_match at 2; autorewrite with defaults.
    erewrite listmatch_isolate with (prd := data_match bxp) (i := wordToNat off) by file_bounds.
    unfold data_match at 2, sel; autorewrite with defaults.
    cancel.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.

    instantiate (a1 := Build_bfile (upd (BFData b) off v)).
    2: eapply list2nmem_upd; eauto.
    2: simpl; eapply list2nmem_upd; eauto.

    eapply pimpl_trans2.
    erewrite listmatch_isolate with (i := wordToNat inum);
      autorewrite with defaults; autorewrite with core; file_bounds.
    unfold file_match at 3.

    repeat rewrite_list2nmem_pred.
    eapply pimpl_trans2.
    erewrite listmatch_isolate with (prd := data_match bxp) (i := wordToNat off);
      autorewrite with defaults; autorewrite with core; file_bounds.
    unfold upd; autorewrite with core; simpl; rewrite length_updN; file_bounds.
    erewrite listmatch_extract with (i := wordToNat inum) in H3; file_bounds.
    destruct_lift H3; file_bounds.

    unfold sel, upd; unfold data_match at 3.
    simpl; rewrite removeN_updN, selN_updN_eq; file_bounds.
    cancel.

    (* extract BALLOC.valid_block out of [listmatch (file_match bxp)] *)
    erewrite listmatch_extract with (i := # inum) in H3 by file_bounds.
    autorewrite with defaults in *.
    unfold file_match at 2 in H3.
    destruct_lift H3.
    setoid_rewrite listmatch_extract with (i := # off) at 2 in H3.
    autorewrite with defaults in *.
    unfold data_match in H3.
    autorewrite with defaults in H3.
    destruct_lift H3.
    eauto.
    file_bounds.

    unfold MEMLOG.log_intact; cancel.
  Qed.


  Theorem bfgrow_ok : forall lxp bxp ixp inum ms,
    {< F A B mbase m flist f,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (BFData f) < INODE.blocks_per_inode ]] *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ B %pred (list2nmem (BFData f)) ]]
    POST:r   exists m', MEMLOG.rep lxp (ActiveTxn mbase m') (snd r) *
            ([[ fst r = false ]] \/ 
             [[ fst r = true ]] * exists flist' f' v,
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ (B * length (BFData f) |-> v)%pred (list2nmem (BFData f')) ]] )
    CRASH    MEMLOG.log_intact lxp mbase
    >} bfgrow lxp bxp ixp inum ms.
  Proof.
    unfold bfgrow, rep.
    hoare.

    destruct_listmatch_n.
    destruct a; subst; simpl.

    step.

    (* FIXME: where are these evars from? *)
    instantiate (a := emp).
    instantiate (a0 := emp).
    instantiate (a1 := emp).
    instantiate (a2 := nil).
    instantiate (a3 := nil).
    instantiate (a4 := nil).
    instantiate (a5 := INODE.inode0).
    instantiate (a6 := nil).
    instantiate (a7 := emp).

    inversion H0; subst; cancel.
    2: subst; inversion H0; subst; pred_apply; cancel.
    2: list2nmem_ptsto_cancel; file_bounds.
    rewrite_list2nmem_pred; unfold file_match in *; file_bounds.
    eapply list2nmem_array; file_bounds.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.
    eapply pimpl_or_r; left; cancel.
    eapply pimpl_or_r; right; cancel.

    instantiate (a0 := Build_bfile (BFData b ++ [w0])).
    2: simpl; eapply list2nmem_upd; eauto.

    rewrite_list2nmem_pred_upd H16; file_bounds.
    subst; unfold upd.
    eapply listmatch_updN_selN_r; autorewrite with defaults; file_bounds.
    unfold file_match; cancel_exact; simpl.

    inversion H0; clear H0; subst.
    eapply list2nmem_array_app_eq in H17 as Heq; eauto.
    rewrite Heq; clear Heq.
    rewrite_list2nmem_pred_sel H5; subst b.
    eapply listmatch_app_r; file_bounds.
    unfold data_match; cancel.

    apply list2nmem_app; eauto.
    cancel.

    step.
    instantiate (a := d0).
    instantiate (a0 := nil).
    inversion H0; subst; cancel.
    cancel.
  Qed.

  Lemma le_minus_one_lt : forall a b,
    a > 0 -> a <= b -> a - 1 < b.
  Proof.
    intros; omega.
  Qed.

  Theorem bfshrink_ok : forall lxp bxp ixp inum ms,
    {< F A B mbase m flist f v,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) ms *
             [[ length (BFData f) > 0 ]] *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (B * ((length (BFData f)) - 1) |-> v)%pred (list2nmem (BFData f)) ]]
    POST:ms' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') ms' *
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ B %pred (list2nmem (BFData f')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} bfshrink lxp bxp ixp inum ms.
  Proof.
    unfold bfshrink, rep.
    step.
    list2nmem_ptsto_cancel; file_bounds.
    step.
    list2nmem_ptsto_cancel; file_bounds.

    repeat rewrite_list2nmem_pred.
    destruct_listmatch_n.
    subst r_; list2nmem_ptsto_cancel; file_bounds.
    rewrite wordToNat_minus_one.
    erewrite wordToNat_natToWord_bound; unfold file_match in *; file_bounds.
    apply gt0_wneq0; file_bounds.
    erewrite wordToNat_natToWord_bound; unfold file_match in *; file_bounds.

    step.
    rewrite wordToNat_minus_one.
    erewrite wordToNat_natToWord_bound; file_bounds.

    rewrite listmatch_isolate with (i := wordToNat inum); file_bounds.
    unfold file_match at 2; autorewrite with defaults.
    rewrite listmatch_isolate with (prd := data_match bxp)
      (i := length (BFData b) - 1); autorewrite with defaults.
    unfold data_match at 2.
    destruct_listmatch_n.
    apply listmatch_length_r in H as Heq.
    rewrite <- Heq.
    repeat rewrite_list2nmem_pred.
    cancel.

    repeat rewrite_list2nmem_pred; omega.
    destruct_listmatch_n.
    apply listmatch_length_r in H as Heq.
    rewrite <- Heq.
    repeat rewrite_list2nmem_pred; omega.

    apply gt0_wneq0; file_bounds.
    erewrite wordToNat_natToWord_bound; file_bounds.
    destruct_listmatch_n.
    repeat rewrite_list2nmem_pred.
    apply listmatch_length_r in H as Heq.
    rewrite <- Heq; auto.

    (* extract BALLOC.valid_block out of [listmatch (file_match bxp)] *)
    erewrite listmatch_extract with (i := # inum) in H by file_bounds.
    autorewrite with defaults in H.
    unfold file_match in H at 2.
    destruct_lift H.
    setoid_rewrite listmatch_extract with (prd := (data_match bxp))
      (i := # ($ (length (INODE.IBlocks (sel l0 inum _))) ^- $ (1))) in H.
    autorewrite with defaults in H.
    unfold data_match in H.
    destruct_lift H.
    subst; eauto.

    repeat rewrite_list2nmem_pred.
    apply listmatch_length_r in H as Heq; file_bounds.
    unfold sel; rewrite wordToNat_minus_one.
    apply le_minus_one_lt.
    erewrite wordToNat_natToWord_bound; file_bounds.
    erewrite wordToNat_natToWord_bound; file_bounds.
    apply gt0_wneq0.
    erewrite wordToNat_natToWord_bound; file_bounds.

    step.

    2: list2nmem_ptsto_cancel; file_bounds.
    repeat rewrite_list2nmem_pred.
    erewrite listmatch_extract with (i := wordToNat inum) in H; file_bounds.
    destruct_lift H.
    apply listmatch_length_r in H as Heq; file_bounds.
    contradict H7; rewrite Heq; autorewrite with defaults.
    rewrite H0; simpl; omega.
    eapply list2nmem_array_exis; autorewrite with defaults.
    list2nmem_ptsto_cancel; file_bounds.

    repeat rewrite_list2nmem_pred.
    erewrite listmatch_extract in H; eauto.
    destruct_lift H.
    apply listmatch_length_r in H as Heq; file_bounds.
    rewrite <- Heq; autorewrite with defaults.
    apply le_minus_one_lt; auto.

    eapply pimpl_ok2; eauto with prog; intros.
    cancel.

    instantiate (a1 := Build_bfile (removelast (BFData b))).
    2: simpl; eapply list2nmem_upd; eauto.
    eapply list2nmem_array_upd in H12; file_bounds.
    subst l2; unfold upd, sel.
    eapply pimpl_trans2.
    rewrite listmatch_isolate with (i := wordToNat inum); 
      autorewrite with defaults; try rewrite length_updN; file_bounds.
    repeat rewrite removeN_updN.
    repeat rewrite selN_updN_eq; file_bounds; simpl.
    unfold file_match; cancel.

    repeat rewrite_list2nmem_pred.
    erewrite listmatch_extract in H; eauto.
    destruct_lift H.
    apply listmatch_length_r in H as Heq; file_bounds.
    rewrite Heq at 2.
    repeat rewrite removeN_removelast; file_bounds.
    erewrite list2nmem_array_removelast_eq with (nl := INODE.IBlocks i); file_bounds.

    simpl; eapply list2nmem_removelast; eauto.
    contradict H7; rewrite H7.
    simpl; omega.
  Qed.


  Hint Extern 1 ({{_}} progseq (bflen _ _ _ _) _) => apply bflen_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfread _ _ _ _ _) _) => apply bfread_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfwrite _ _ _ _ _ _) _) => apply bfwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfgrow _ _ _ _ _) _) => apply bfgrow_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfshrink _ _ _ _ _) _) => apply bfshrink_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


End BFILE.
