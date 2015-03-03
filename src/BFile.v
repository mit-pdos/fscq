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

  Definition bflen T lxp ixp inum mscs rx : prog T :=
    let2 (mscs, n) <- INODE.ilen lxp ixp inum mscs;
    rx (mscs, n).

  Definition bfread T lxp ixp inum off mscs rx : prog T :=
    let2 (mscs, b) <-INODE.iget lxp ixp inum off mscs;
    let2 (mscs, fblock) <- MEMLOG.read lxp b mscs;
    rx (mscs, fblock).

  Definition bfwrite T lxp ixp inum off v mscs rx : prog T :=
    let2 (mscs, b) <-INODE.iget lxp ixp inum off mscs;
    let2 (mscs, ok) <- MEMLOG.write lxp b v mscs;
    rx (mscs, ok).

  Definition bfgrow T lxp bxp ixp inum mscs rx : prog T :=
    let2 (mscs, len) <- INODE.ilen lxp ixp inum mscs;
    let2 (mscs, bn) <- BALLOC.alloc lxp bxp mscs;
    match bn with
    | None => rx (mscs, false)
    | Some bnum =>
        If (wlt_dec len (natToWord addrlen INODE.blocks_per_inode)) {
          let2 (mscs, ok) <- INODE.igrow lxp bxp ixp inum bnum mscs;
          rx (mscs, ok)
        } else {
          rx (mscs, false)
        }
    end.

  Definition bfshrink T lxp bxp ixp inum mscs rx : prog T :=
    let2 (mscs, n) <- INODE.ilen lxp ixp inum mscs;
    let2 (mscs, b) <- INODE.iget lxp ixp inum (n ^- $1) mscs;
    mscs <- BALLOC.free lxp bxp b mscs;
    mscs <- INODE.ishrink lxp bxp ixp inum mscs;
    rx mscs.

  Definition bfgetsz T lxp ixp inum mscs rx : prog T :=
    let2 (mscs, n) <- INODE.igetsz lxp ixp inum mscs;
    rx (mscs, n).

  Definition bfsetsz T lxp ixp inum sz mscs rx : prog T :=
    mscs <- INODE.isetsz lxp ixp inum sz mscs;
    rx mscs.


  (* representation invariants *)

  Record bfile := {
    BFData : list valu;
    BFSize : addr
  }.

  Definition bfile0 := Build_bfile nil $0.

  Definition data_match bxp (v : valu) a : @pred _ (@weq addrlen) _ :=
    (a |-> v * [[ BALLOC.valid_block bxp a ]])%pred.

  Definition file_match bxp f i :=
    (listmatch (data_match bxp) (BFData f) (INODE.IBlocks i) *
     [[ BFSize f = INODE.ISize i ]])%pred.

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

  Ltac file_bounds' :=
    match goal with
      | [ H : ?p%pred ?mem |- length ?l <= _ ] =>
        match p with
        | context [ (INODE.rep _ _ ?l') ] => 
          first [ constr_eq l l'; eapply INODE.rep_bound with (m := mem) |
            match l with
            | INODE.IBlocks (selN l' _ _) => 
                eapply INODE.blocks_bound with (m := mem)
            end
          ]; pred_apply; cancel
        end
    end.


  Ltac file_bounds := eauto; try list2nmem_bound; try solve_length_eq;
                      repeat file_bounds';
                      try list2nmem_bound; eauto.


  Theorem bfdata_bound : forall F m bxp ixp l i,
    (F * rep bxp ixp l)%pred m
    -> wordToNat i < length l
    -> length (BFData (sel l i bfile0)) <= INODE.blocks_per_inode.
  Proof.
    unfold rep, sel; intros.
    destruct_lift H.
    rewrite listmatch_extract with (i := wordToNat i) in H by auto.
    autorewrite with defaults in *.
    unfold file_match at 2, listmatch at 2 in H.
    destruct_lift H.
    rewrite H6.
    erewrite <- wordToNat_natToWord_bound with (sz := addrlen).
    eapply INODE.blocks_bound with (m := m).
    pred_apply; cancel.
    instantiate (bound := INODE.wnr_direct ^+ INODE.wnr_indirect).
    auto.
  Qed.

  Theorem bfdata_bound' : forall F m bxp ixp l i,
    (F * rep bxp ixp l)%pred m
    -> wordToNat i < length l
    -> length (BFData (sel l i bfile0)) <= wordToNat (natToWord addrlen INODE.blocks_per_inode).
  Proof.
    intros.
    erewrite wordToNat_natToWord_bound.
    eapply bfdata_bound; eauto.
    instantiate (bound := INODE.wnr_direct ^+ INODE.wnr_indirect).
    auto.
  Qed.


  (* correctness theorems *)

  Theorem bflen_ok : forall lxp bxp ixp inum mscs,
    {< F A mbase m flist f,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = $ (length (BFData f)) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bflen lxp ixp inum mscs.
  Proof.
    unfold bflen, rep.
    hoare.
    list2nmem_ptsto_cancel; file_bounds.

    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    subst; unfold sel; auto.
    f_equal; apply eq_sym; eauto.
  Qed.


  Theorem bfread_ok : forall lxp bxp ixp inum off mscs,
    {<F A B mbase m flist f v,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFData f)) ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = v ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bfread lxp ixp inum off mscs.
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


  Lemma bfwrite_ok : forall lxp bxp ixp inum off v mscs,
    {<F A B mbase m flist f v0,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (B * #off |-> v0)%pred (list2nmem (BFData f)) ]]
    POST:mscs' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ (B * #off |-> v)%pred (list2nmem (BFData f')) ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bfwrite lxp ixp inum off v mscs.
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

    instantiate (a1 := Build_bfile (upd (BFData b) off v) (BFSize b)).
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
    unfold file_match in H3; destruct_lift H3; file_bounds.

    unfold sel, upd; unfold data_match at 3.
    simpl; rewrite removeN_updN, selN_updN_eq; file_bounds.
    erewrite listmatch_extract with (i := # inum) in H3 by file_bounds.
    unfold file_match at 2 in H3.
    (* extract BALLOC.valid_block out of [listmatch (file_match bxp)] *)
    setoid_rewrite listmatch_extract with (i := # off) at 2  in H3; file_bounds.
    unfold data_match in H3.
    autorewrite with defaults in H3.
    destruct_lift H3.
    cancel.

    unfold MEMLOG.log_intact; cancel.
  Qed.

  Lemma helper_wlt_lt_blocks_per_inode : forall n (b : addr),
    n <= wordToNat b
    -> ((natToWord addrlen n) < (natToWord addrlen INODE.blocks_per_inode))%word
    -> n < INODE.blocks_per_inode.
  Proof.
    intros; apply wlt_lt in H0.
    erewrite wordToNat_natToWord_bound in H0; eauto.
  Qed.

  Theorem bfgrow_ok : forall lxp bxp ixp inum mscs,
    {< F A B mbase m flist f,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ B %pred (list2nmem (BFData f)) ]]
    POST:(mscs',r)
            exists m', MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
            ([[ r = false ]] \/ 
             [[ r = true ]] * exists flist' f' v,
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ (B * length (BFData f) |-> v)%pred (list2nmem (BFData f')) ]] )
    CRASH    MEMLOG.log_intact lxp mbase
    >} bfgrow lxp bxp ixp inum mscs.
  Proof.
    unfold bfgrow, rep.
    step.
    list2nmem_ptsto_cancel; file_bounds.
    hoare.

    destruct_listmatch_n.
    destruct b2; subst; simpl.
    step; inversion H3; subst.

    step.
    rewrite_list2nmem_pred; unfold file_match in *; file_bounds.
    2: list2nmem_ptsto_cancel; file_bounds.
    eapply helper_wlt_lt_blocks_per_inode; file_bounds.
    eapply list2nmem_array; file_bounds.

    eapply pimpl_ok2; eauto with prog.
    intros; cancel.
    eapply pimpl_or_r; left; cancel.
    eapply pimpl_or_r; right; cancel.

    instantiate (a0 := Build_bfile (BFData b ++ [w0]) (BFSize b)).
    2: simpl; eapply list2nmem_upd; eauto.

    rewrite_list2nmem_pred_upd H17; file_bounds.
    subst; unfold upd.
    eapply listmatch_updN_selN_r; autorewrite with defaults; file_bounds.
    unfold file_match; simpl.
    repeat rewrite_list2nmem_pred.
    cancel.
    rewrite sep_star_comm.
    eapply list2nmem_array_app_eq in H18 as Heq; eauto.
    rewrite Heq; clear Heq.
    eapply listmatch_app_r.
    file_bounds.

    eapply list2nmem_array_app_eq in H18 as Heq; eauto.
    rewrite <- Heq; clear Heq.
    unfold data_match; cancel.
    admit.

    apply list2nmem_app; eauto.
    step.
    step.
  Qed.


  Ltac shrink_bounds' :=
    match goal with
      | [ |- context [ wordToNat (?w ^- $1) ] ] =>
          rewrite wordToNat_minus_one
      | [ |- context [ wordToNat (natToWord _ (length _)) ] ] =>
          erewrite wordToNat_natToWord_bound
      | [ |- natToWord _ _ <> $0 ] =>
          apply gt0_wneq0
    end.

  Ltac shrink_bounds := repeat shrink_bounds'; file_bounds.

  Lemma helper_minus_one_lt : forall n m,
    n > 0 -> m = n -> n - 1 < m.
  Proof.
    intros; omega.
  Qed.

  Hint Resolve helper_minus_one_lt.


  Theorem bfshrink_ok : forall lxp bxp ixp inum mscs,
    {< F A B mbase m flist f v,
    PRE      MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
             [[ length (BFData f) > 0 ]] *
             [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (B * ((length (BFData f)) - 1) |-> v)%pred (list2nmem (BFData f)) ]]
    POST:mscs' exists m' flist' f',
             MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
             [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ B %pred (list2nmem (BFData f')) ]]
    CRASH    MEMLOG.log_intact lxp mbase
    >} bfshrink lxp bxp ixp inum mscs.
  Proof.
    unfold bfshrink, rep.
    step.
    list2nmem_ptsto_cancel; file_bounds.

    (* extract some lifted facts early *)
    destruct_listmatch_n.
    assert (Heq := H).
    setoid_rewrite listmatch_extract with (prd := (data_match bxp))
      (i := # ($ (length (INODE.IBlocks (sel l0 inum _))) ^- $ (1))) in Heq.
    autorewrite with defaults in Heq.
    unfold data_match in Heq.
    destruct_lift Heq; clear H0.

    step.
    list2nmem_ptsto_cancel; file_bounds.
    repeat rewrite_list2nmem_pred.
    subst; list2nmem_ptsto_cancel; shrink_bounds.

    repeat rewrite_list2nmem_pred.
    step.
    rewrite listmatch_isolate with (prd := data_match bxp)
      (i := length (BFData (selN l1 (wordToNat inum) bfile0)) - 1); auto.
    autorewrite with defaults; shrink_bounds.
    unfold data_match at 2.
    rewrite H9.
    cancel.

    step.
    2: list2nmem_ptsto_cancel; file_bounds.
    2: list2nmem_ptsto_cancel; file_bounds.
    file_bounds.
    eapply pimpl_ok2; eauto with prog.
    intros; cancel.

    instantiate (a1 := Build_bfile 
      (removelast (BFData (selN l1 (wordToNat inum) bfile0)))
                  (BFSize (selN l1 (wordToNat inum) bfile0))).
    2: simpl; eapply list2nmem_upd; eauto.

    erewrite list2nmem_array_upd with (nl := l2); file_bounds.
    unfold upd, sel.
    setoid_rewrite listmatch_isolate with (i := wordToNat inum) at 3;
      autorewrite with defaults core; file_bounds.
    instantiate (ad := bfile0); instantiate (bd := INODE.inode0).
    unfold file_match at 3; simpl.
    erewrite list2nmem_array_removelast_eq with (nl := INODE.IBlocks i); file_bounds.
    rewrite <- H9 at 1; repeat rewrite removeN_removelast; file_bounds.
    cancel.

    simpl.
    eapply list2nmem_removelast; eauto.
    apply length_not_nil; eauto.
    apply listmatch_length_r in Heq.
    repeat rewrite_list2nmem_pred.
    unfold sel; shrink_bounds.
  Qed.

  Theorem bfgetsz_ok : forall lxp bxp ixp inum mscs,
    {< F A mbase m flist f,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST:(mscs',r)
           MEMLOG.rep lxp (ActiveTxn mbase m) mscs' *
           [[ r = BFSize f ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bfgetsz lxp ixp inum mscs.
  Proof.
    unfold bfgetsz, rep.
    hoare.
    list2nmem_ptsto_cancel; file_bounds.

    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    congruence.
  Qed.

  Theorem bfsetsz_ok : forall lxp bxp ixp inum sz mscs,
    {< F A mbase m flist f,
    PRE    MEMLOG.rep lxp (ActiveTxn mbase m) mscs *
           [[ (F * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST:mscs'
           exists m' flist' f',
           MEMLOG.rep lxp (ActiveTxn mbase m') mscs' *
           [[ (F * rep bxp ixp flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ BFSize f' = sz ]] *
           [[ BFData f' = BFData f ]]
    CRASH  MEMLOG.log_intact lxp mbase
    >} bfsetsz lxp ixp inum sz mscs.
  Proof.
    unfold bfsetsz, rep.
    hoare.
    list2nmem_ptsto_cancel; file_bounds.

    admit.
    rewrite_list2nmem_pred.
    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    admit.
  Qed.

  Hint Extern 1 ({{_}} progseq (bflen _ _ _ _) _) => apply bflen_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfread _ _ _ _ _) _) => apply bfread_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfwrite _ _ _ _ _ _) _) => apply bfwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfgrow _ _ _ _ _) _) => apply bfgrow_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfshrink _ _ _ _ _) _) => apply bfshrink_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfgetsz _ _ _ _) _) => apply bfgetsz_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfsetsz _ _ _ _ _) _) => apply bfsetsz_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.


End BFILE.
