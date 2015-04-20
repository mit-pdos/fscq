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
    let^ (mscs, n) <- INODE.ilen lxp ixp inum mscs;
    rx ^(mscs, n).

  Definition bfread T lxp ixp inum off mscs rx : prog T :=
    let^ (mscs, b) <-INODE.iget lxp ixp inum off mscs;
    let^ (mscs, fblock) <- LOG.read lxp b mscs;
    rx ^(mscs, fblock).

  Definition bfwrite T lxp ixp inum off v mscs rx : prog T :=
    let^ (mscs, b) <-INODE.iget lxp ixp inum off mscs;
    let^ (mscs, ok) <- LOG.write lxp b v mscs;
    rx ^(mscs, ok).

  Definition bfgrow T lxp bxp ixp inum mscs rx : prog T :=
    let^ (mscs, len) <- INODE.ilen lxp ixp inum mscs;
    let^ (mscs, bn) <- BALLOC.alloc lxp bxp mscs;
    match bn with
    | None => rx ^(mscs, false)
    | Some bnum =>
        If (wlt_dec len (natToWord addrlen INODE.blocks_per_inode)) {
          let^ (mscs, ok) <- INODE.igrow lxp bxp ixp inum bnum mscs;
          rx ^(mscs, ok)
        } else {
          rx ^(mscs, false)
        }
    end.

  Definition bfshrink T lxp bxp ixp inum mscs rx : prog T :=
    let^ (mscs, n) <- INODE.ilen lxp ixp inum mscs;
    let^ (mscs, b) <- INODE.iget lxp ixp inum (n ^- $1) mscs;
    mscs <- BALLOC.free lxp bxp b mscs;
    mscs <- INODE.ishrink lxp bxp ixp inum mscs;
    rx mscs.

  Definition bfgetattr T lxp ixp inum mscs rx : prog T :=
    let^ (mscs, n) <- INODE.igetattr lxp ixp inum mscs;
    rx ^(mscs, n).

  Definition bfsetattr T lxp ixp inum sz mscs rx : prog T :=
    mscs <- INODE.isetattr lxp ixp inum sz mscs;
    rx mscs.


  (* representation invariants *)

  Definition bfattr := INODE.iattr.
  Definition bfattr0 := INODE.iattr0.

  Record bfile := {
    BFData : list valu;
    BFAttr : bfattr
  }.

  Definition bfile0 := Build_bfile nil bfattr0.

  Definition data_match bxp (v : valu) a : @pred _ (@weq addrlen) _ :=
    (a |-> v * [[ BALLOC.valid_block bxp a ]])%pred.

  Definition file_match bxp f i :=
    (listmatch (data_match bxp) (BFData f) (INODE.IBlocks i) *
     [[ BFAttr f = INODE.IAttr i ]])%pred.

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

  Theorem bfdata_bound_ptsto : forall F A m bxp ixp l (i : addr) f,
    (F * rep bxp ixp l)%pred m
    -> (A * # i |-> f)%pred (list2nmem l)
    -> length (BFData f) <= wordToNat (natToWord addrlen INODE.blocks_per_inode).
  Proof.
    intros.
    rewrite_list2nmem_pred.
    eapply bfdata_bound'; eauto.
  Qed.

  (* correctness theorems *)

  Theorem bflen_ok : forall lxp bxp ixp inum mscs,
    {< F Fm A mbase m flist f,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = $ (length (BFData f)) ]]
    CRASH  LOG.would_recover_old lxp F mbase
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


  Theorem bfgetattr_ok : forall lxp bxp ixp inum mscs,
    {< F Fm A mbase m flist f,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = BFAttr f ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bfgetattr lxp ixp inum mscs.
  Proof.
    unfold bfgetattr, rep.
    hoare.
    list2nmem_ptsto_cancel; file_bounds.

    rewrite_list2nmem_pred.
    destruct_listmatch_n.
    congruence.
  Qed.

  Theorem bfsetattr_ok : forall lxp bxp ixp inum attr mscs,
    {< F Fm A mbase m flist f,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:mscs
           exists m' flist' f',
           LOG.rep lxp F (ActiveTxn mbase m') mscs *
           [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
           [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
           [[ f' = Build_bfile (BFData f) attr ]]
    CRASH  LOG.would_recover_old lxp F mbase
    >} bfsetattr lxp ixp inum attr mscs.
  Proof.
    unfold bfsetattr, rep.
    hoare.
    list2nmem_ptsto_cancel; file_bounds.
    2: eapply list2nmem_updN; eauto.

    repeat rewrite_list2nmem_pred; file_bounds.
    destruct_listmatch_n.
    eapply listmatch_updN_selN; file_bounds.
    autorewrite with defaults; unfold file_match.
    cancel.
  Qed.


  Theorem bfread_ok : forall lxp bxp ixp inum off mscs,
    {< F Fm A B mbase m flist f v,
    PRE    LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
           [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
           [[ (B * #off |-> v)%pred (list2nmem (BFData f)) ]]
    POST RET:^(mscs,r)
           LOG.rep lxp F (ActiveTxn mbase m) mscs *
           [[ r = v ]]
    CRASH  LOG.would_recover_old lxp F mbase
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
    rewrite LOG.activetxn_would_recover_old; cancel.
  Qed.


  Lemma bfwrite_ok : forall lxp bxp ixp inum off v mscs,
    {< F Fm A B mbase m flist f v0,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (B * #off |-> v0)%pred (list2nmem (BFData f)) ]]
    POST RET:mscs
             exists m' flist' f',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ (B * #off |-> v)%pred (list2nmem (BFData f')) ]] *
             [[ f' = Build_bfile (upd (BFData f) off v) (BFAttr f) ]]
    CRASH  LOG.would_recover_old lxp F mbase
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

    step.
    2: eapply list2nmem_updN; eauto.
    2: simpl; eapply list2nmem_updN; eauto.

    eapply pimpl_trans2.
    erewrite listmatch_isolate with (i := wordToNat inum);
      autorewrite with defaults; autorewrite with core; file_bounds.
    unfold file_match at 3.

    repeat rewrite_list2nmem_pred.
    eapply pimpl_trans2.
    erewrite listmatch_isolate with (prd := data_match bxp) (i := wordToNat off);
      autorewrite with defaults; autorewrite with core; file_bounds.
    unfold upd; autorewrite with core; simpl; rewrite length_updN; file_bounds.
    erewrite listmatch_extract with (i := wordToNat inum) in H3; file_bounds;
      autorewrite with defaults in H3.
    unfold file_match at 2 in H3; destruct_lift H3; file_bounds.

    unfold sel, upd; unfold data_match at 3.
    simpl; rewrite removeN_updN, selN_updN_eq; file_bounds.
    erewrite listmatch_extract with (i := # inum) in H3 by file_bounds;
      autorewrite with defaults in H3.
    unfold file_match at 2 in H3; destruct_lift H3; file_bounds.
    (* extract BALLOC.valid_block out of [listmatch (file_match bxp)] *)
    setoid_rewrite listmatch_extract with (i := # off) at 2  in H3; file_bounds;
      autorewrite with defaults in H3.
    unfold data_match in H3; destruct_lift H3.
    cancel.

    apply LOG.activetxn_would_recover_old.
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
    {< F Fm A B mbase m flist f,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ B %pred (list2nmem (BFData f)) ]]
    POST RET:^(mscs,r)
            exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
            ([[ r = false ]] \/ 
             [[ r = true ]] * exists flist' f' v,
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ (B * length (BFData f) |-> v)%pred (list2nmem (BFData f')) ]] *
             [[ f' = Build_bfile (BFData f ++ [v]) (BFAttr f) ]])
    CRASH    LOG.would_recover_old lxp F mbase
    >} bfgrow lxp bxp ixp inum mscs.
  Proof.
    unfold bfgrow, rep.
    step.
    list2nmem_ptsto_cancel; file_bounds.
    hoare.

    destruct_listmatch_n.
    2: list2nmem_ptsto_cancel; file_bounds.
    eapply helper_wlt_lt_blocks_per_inode; file_bounds.
    eapply list2nmem_array; file_bounds.

    eapply pimpl_or_r; right; cancel.
    2: simpl; eapply list2nmem_updN; eauto.
    instantiate (a1 := w0).

    erewrite listmatch_extract with (i := # inum) in H3 by file_bounds;
      autorewrite with defaults in H3.
    unfold file_match at 2 in H3; destruct_lift H3.
    repeat rewrite_list2nmem_pred; file_bounds.
    eapply listmatch_updN_selN_r; autorewrite with defaults; file_bounds.
    unfold file_match; simpl.
    cancel.
    rewrite sep_star_comm; eapply listmatch_app_r; file_bounds.
    unfold data_match; cancel.
    apply list2nmem_app; eauto.
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

  Ltac shrink_bounds := repeat shrink_bounds'; eauto; try list2nmem_bound;
                      repeat file_bounds'; try list2nmem_bound; eauto.

  Lemma helper_minus_one_lt : forall n m,
    n > 0 -> m = n -> n - 1 < m.
  Proof.
    intros; omega.
  Qed.

  Hint Resolve helper_minus_one_lt.


  Theorem bfshrink_ok : forall lxp bxp ixp inum mscs,
    {< F Fm A B mbase m flist f v,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ length (BFData f) > 0 ]] *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ (B * ((length (BFData f)) - 1) |-> v)%pred (list2nmem (BFData f)) ]]
    POST RET:mscs
             exists m' flist' f',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ B %pred (list2nmem (BFData f')) ]] *
             [[ f' = Build_bfile (removelast (BFData f)) (BFAttr f) ]]
    CRASH    LOG.would_recover_old lxp F mbase
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
    subst; list2nmem_ptsto_cancel; shrink_bounds; file_bounds.

    repeat rewrite_list2nmem_pred.
    step.
    rewrite listmatch_isolate with (prd := data_match bxp)
      (i := length (BFData (selN l1 (wordToNat inum) bfile0)) - 1); auto.
    autorewrite with defaults; shrink_bounds; [ | file_bounds].
    unfold data_match at 2; rewrite H9.
    cancel.

    step.
    2: list2nmem_ptsto_cancel; file_bounds.
    2: list2nmem_ptsto_cancel; file_bounds.
    file_bounds.
    step.
    2: simpl; eapply list2nmem_updN; eauto.

    erewrite list2nmem_array_upd with (nl := l2); [ | file_bounds ..].
    unfold upd, sel.
    setoid_rewrite listmatch_isolate with (i := wordToNat inum) at 3;
      autorewrite with defaults core; [ | file_bounds .. ].

    unfold file_match at 3; simpl.
    rewrite <- H9 at 1; repeat rewrite removeN_removelast; file_bounds.
    cancel.

    eapply list2nmem_removelast; eauto.
    apply length_not_nil; eauto.
    apply listmatch_length_r in Heq.
    repeat rewrite_list2nmem_pred.
    unfold sel; shrink_bounds; file_bounds.

    Grab Existential Variables.
    exact INODE.inode0. exact bfile0.
  Qed.


  Hint Extern 1 ({{_}} progseq (bflen _ _ _ _) _) => apply bflen_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfread _ _ _ _ _) _) => apply bfread_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfwrite _ _ _ _ _ _) _) => apply bfwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfgrow _ _ _ _ _) _) => apply bfgrow_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfshrink _ _ _ _ _) _) => apply bfshrink_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfgetattr _ _ _ _) _) => apply bfgetattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (bfsetattr _ _ _ _ _) _) => apply bfsetattr_ok : prog.

  Definition bftrunc_shrink T lxp bxp ixp inum newsz mscs rx : prog T :=
    let^ (mscs, n) <- bflen lxp ixp inum mscs;
    let^ (mscs) <- For i < (n ^- newsz)
      Ghost [ mbase F Fm A f ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant
        exists m' flist' f',
        LOG.rep lxp F (ActiveTxn mbase m') mscs *
        [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ f' = Build_bfile (firstn (# (n ^- i)) (BFData f)) (BFAttr f) ]]
      OnCrash
        LOG.would_recover_old lxp F mbase
      Begin
        mscs <- bfshrink lxp bxp ixp inum mscs;
        lrx ^(mscs)
      Rof ^(mscs);
    rx mscs.

  Definition bftrunc_grow T lxp bxp ixp inum newsz mscs rx : prog T :=
    let^ (mscs, n) <- bflen lxp ixp inum mscs;
    let^ (mscs) <- For i < (newsz ^- n)
      Ghost [ mbase F Fm A f ]
      Loopvar [ mscs ]
      Continuation lrx
      Invariant
        exists m' flist' f',
        LOG.rep lxp F (ActiveTxn mbase m') mscs *
        [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
        [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
        [[ f' = Build_bfile ((BFData f) ++ (repeat $0 #i)) (BFAttr f) ]]
      OnCrash
        LOG.would_recover_old lxp F mbase
      Begin
        let^ (mscs, ok) <- bfgrow lxp bxp ixp inum mscs;
        If (bool_dec ok true) {
          mscs <- bfwrite lxp ixp inum (n ^+ i) $0 mscs;
          lrx ^(mscs)
        } else {
          rx ^(mscs, false)
        }
      Rof ^(mscs);
    rx ^(mscs, true).

  Lemma sep_star_bfdata_bound : forall F A bxp ixp l l0 l1 (inum : addr) f m,
    (F * BALLOC.rep bxp l * INODE.rep bxp ixp l0 * listmatch (file_match bxp) l1 l0)%pred m
    -> (A * # inum |-> f)%pred (list2nmem l1)
    ->  length (BFData f) <= wordToNat (natToWord addrlen INODE.blocks_per_inode).
  Proof.
    intros.
    rewrite_list2nmem_pred.
    eapply bfdata_bound' with (m := m); auto.
    unfold rep; pred_apply; cancel.
  Qed.

  Ltac bftrunc_bfdata_bound :=
    match goal with
    | [ H1 : context [ listmatch (file_match _) ?ll _ ],
        H2 : (_ * _ |-> ?ff)%pred (list2nmem ?ll)
           |- length (BFData ?ff) <= _ ] =>
      eapply sep_star_bfdata_bound with (f := ff) (l1 := ll); eauto
    | [ H1 : context [ listmatch (file_match _) ?ll _ ],
        H2 : (_ * (# ?ix) |-> {| BFData := ?fdata ; BFAttr := _ |})%pred (list2nmem ?ll)
           |- length ?fdata <= _ ] => let Hx := fresh in
        pose proof (sep_star_bfdata_bound ix H1 H2) as Hx; simpl in Hx; apply Hx
    end.

  Local Arguments wordToNat : simpl never.
  Local Hint Extern 1 (length (BFData _) <= _) => bftrunc_bfdata_bound.

  Lemma helper_wordToNat_wminus_0 : forall n (b : addr),
    n <= #b -> n = # ((natToWord addrlen n) ^- $0).
  Proof.
    intros.
    ring_simplify ((natToWord addrlen n) ^- (natToWord addrlen 0)).
    erewrite wordToNat_natToWord_bound; eauto.
  Qed.

  Lemma helper_bfdata_length : forall (m sz bound : addr) n,
    (m < $ n ^- sz)%word -> # sz <= n -> n <= # bound
    -> # ($ n ^- m) > 0 /\ # ($ n ^- m) <= n.
  Proof.
    intros; apply wlt_lt in H.
    rewrite wminus_minus in *; try apply le_wle;
    erewrite wordToNat_natToWord_bound in *; eauto; try omega.
  Qed.


  Lemma helper_sub_1_wplus_1_eq : forall n (m sz bound : addr),
    (m < $ n ^- sz)%word -> # sz <= n -> n <= # bound
    -> # ($ n ^- m ) - 1 = # ($ n ^- (m ^+ $1)).
  Proof.
    intros; apply wlt_lt in H as Hx.
    rewrite wminus_minus in *; try apply le_wle;
      erewrite wordToNat_natToWord_bound in *; eauto; try omega.
    rewrite wminus_minus; try apply le_wle;
      try erewrite wordToNat_plusone by eauto;
      erewrite wordToNat_natToWord_bound by eauto; omega.
  Qed.

  Local Hint Resolve wlt_wle_incl.
  Local Hint Resolve helper_wordToNat_wminus_0.
  Local Hint Unfold rep : hoare_unfold.

  Theorem bftrunc_shrink_ok : forall lxp bxp ixp inum sz mscs,
    {< F Fm A mbase m flist f,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ # sz <= length (BFData f) ]]
    POST RET:mscs
             exists m' flist' f',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ f' = Build_bfile (firstn (# sz) (BFData f)) (BFAttr f) ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} bftrunc_shrink lxp bxp ixp inum sz mscs.
  Proof.
    unfold bftrunc_shrink.
    step.
    step.

    ring_simplify (a ^- $ (0)).
    instantiate (a4 := b); subst.
    erewrite wordToNat_natToWord_bound; eauto.
    rewrite firstn_oob by omega.
    destruct b; pred_apply; cancel.

    step.
    subst; simpl; rewrite firstn_length_l;
      eapply helper_bfdata_length; eauto.
    list2nmem_ptsto_cancel.
    apply helper_minus_one_lt; eauto.
    subst; simpl; rewrite firstn_length_l;
      eapply helper_bfdata_length; eauto.

    step.
    apply ptsto_value_eq; f_equal.
    rewrite removelast_firstn_sub;
    try eapply helper_bfdata_length; eauto; f_equal.
    eapply helper_sub_1_wplus_1_eq; eauto.

    step.
    apply ptsto_value_eq; repeat f_equal; ring.
  Qed.


  Lemma helper_wplus_length_app_repeat : forall (l : list valu) (bound m : addr),
    (length (l ++ repeat $0 (# m))) <= # bound
    -> # ($ (length l) ^+ m) = length (l ++ repeat $0 (# m)).
  Proof.
    intros.
    rewrite app_length in *; rewrite repeat_length in *.
    word2nat_auto.
  Qed.

  Theorem bftrunc_grow_ok : forall lxp bxp ixp inum sz mscs,
    {< F Fm A mbase m flist f,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]] *
             [[ # sz >= length (BFData f) ]]
    POST RET:^(mscs, r)
             exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
            ([[ r = false ]] \/
             [[ r = true  ]] * exists flist' f',
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ f' = Build_bfile ((BFData f) ++
                                  (repeat $0 (#sz - (length (BFData f))))) (BFAttr f) ]])
    CRASH    LOG.would_recover_old lxp F mbase
    >} bftrunc_grow lxp bxp ixp inum sz mscs.
  Proof.
    unfold bftrunc_grow.
    step.
    step.

    instantiate (a4 := b); subst.
    unfold repeat; rewrite app_nil_r.
    destruct b; pred_apply; eauto.

    step; subst; simpl.
    apply list2nmem_array.
    step; subst; step; simpl.
    erewrite helper_wplus_length_app_repeat by bftrunc_bfdata_bound.
    pred_apply; cancel.

    step.
    apply ptsto_value_eq; unfold upd; f_equal.
    erewrite wordToNat_plusone; eauto.
    rewrite repeat_app_tail; rewrite app_assoc.
    erewrite helper_wplus_length_app_repeat by bftrunc_bfdata_bound.
    apply updN_app_tail.

    step.
    apply pimpl_or_r; right; cancel.
    apply ptsto_value_eq.
    rewrite wminus_minus; try apply le_wle;
      erewrite wordToNat_natToWord_bound; eauto.

    Grab Existential Variables.
    all: try exact nil; try exact $0; try exact emp.
    exact bfile0. exact bxp.
  Qed.

  Hint Extern 1 ({{_}} progseq (bftrunc_shrink _ _ _ _ _ _) _) => apply bftrunc_shrink_ok : prog.
  Hint Extern 1 ({{_}} progseq (bftrunc_grow   _ _ _ _ _ _) _) => apply bftrunc_grow_ok : prog.

  Definition bfreset T lxp bxp ixp inum mscs rx : prog T :=
    mscs <- bftrunc_shrink lxp bxp ixp inum $0 mscs;
    mscs <- bfsetattr lxp ixp inum bfattr0 mscs;
    rx mscs.

  Definition bftrunc T lxp bxp ixp inum newsz mscs rx : prog T :=
    let^ (mscs, n) <- bflen lxp ixp inum mscs;
    If (wlt_dec newsz n) {
      mscs <- bftrunc_shrink lxp bxp ixp inum newsz mscs;
      rx ^(mscs, true)
    } else {
      let^ (mscs, ok) <- bftrunc_grow lxp bxp ixp inum newsz mscs;
      rx ^(mscs, ok)
    }.

  Theorem bfreset_ok : forall lxp bxp ixp inum mscs,
    {< F Fm A mbase m flist f,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:mscs
             exists m' flist',
             LOG.rep lxp F (ActiveTxn mbase m') mscs *
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> bfile0)%pred (list2nmem flist') ]]
    CRASH    LOG.would_recover_old lxp F mbase
    >} bfreset lxp bxp ixp inum mscs.
  Proof.
    unfold bfreset.
    hoare.
  Qed.

  Theorem bftrunc_ok : forall lxp bxp ixp inum newsz mscs,
    {< F Fm A mbase m flist f,
    PRE      LOG.rep lxp F (ActiveTxn mbase m) mscs *
             [[ (Fm * rep bxp ixp flist)%pred (list2mem m) ]] *
             [[ (A * #inum |-> f)%pred (list2nmem flist) ]]
    POST RET:^(mscs, r)
             exists m', LOG.rep lxp F (ActiveTxn mbase m') mscs *
            ([[ r = false ]] \/
             [[ r = true  ]] * exists flist' f',
             [[ (Fm * rep bxp ixp flist')%pred (list2mem m') ]] *
             [[ (A * #inum |-> f')%pred (list2nmem flist') ]] *
             [[ f' = Build_bfile (setlen (BFData f) #newsz $0) (BFAttr f) ]])
    CRASH    LOG.would_recover_old lxp F mbase
    >} bftrunc lxp bxp ixp inum newsz mscs.
  Proof.
    unfold bftrunc, setlen.
    hoare.

    (* case 1 : shrinking *)
    word2nat_auto.
    apply pimpl_or_r; right; cancel.
    apply ptsto_value_eq; f_equal.
    rewrite repeat_is_nil.
    rewrite app_nil_r; auto.
    apply Nat.sub_0_le; word2nat_auto.

    (* case 2 : growing *)
    erewrite <- wordToNat_natToWord_bound; eauto.
    apply wle_le; auto.
    apply pimpl_or_r; right; cancel.
    apply ptsto_value_eq; f_equal.

    rewrite firstn_oob; auto.
    erewrite <- wordToNat_natToWord_bound; eauto.
    apply wle_le; auto.
  Qed.


  Hint Extern 1 ({{_}} progseq (bfreset _ _ _ _ _) _) => apply bfreset_ok : prog.
  Hint Extern 1 ({{_}} progseq (bftrunc _ _ _ _ _ _) _) => apply bftrunc_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.

End BFILE.
