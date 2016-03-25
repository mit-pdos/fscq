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
Require Import List ListUtils.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Setoid.
Require Import Rec.
Require Import FunctionalExtensionality.
Require Import NArith.
Require Import WordAuto.
Require Import RecArrayUtils LogRecArray.
Require Import GenSepN.
Require Import Balloc.
Require Import ListPred.
Require Import FSLayout.
Require Import AsyncDisk.
Require Import Inode.
Require Import GenSepAuto.

Import ListNotations.

Set Implicit Arguments.

(** BFILE is a block-based file implemented on top of the log and the
inode representation. The API provides reading/writing single blocks,
changing the size of the file, and managing file attributes (which are
the same as the inode attributes). *)

Module BFILE.


  (* interface implementation *)

  Definition getlen T lxp ixp inum ms rx : prog T :=
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    rx ^(ms, n).

  Definition getattrs T lxp ixp inum ms rx : prog T :=
    let^ (ms, n) <- INODE.getattrs lxp ixp inum ms;
    rx ^(ms, n).

  Definition setattrs T lxp ixp inum a ms rx : prog T :=
    ms <- INODE.setattrs lxp ixp inum a ms;
    rx ms.

  Definition updattr T lxp ixp inum kv ms rx : prog T :=
    ms <- INODE.updattr lxp ixp inum kv ms;
    rx ms.

  Definition read T lxp ixp inum off ms rx : prog T :=
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    let^ (ms, v) <- LOG.read lxp (# bn) ms;
    rx ^(ms, v).

  Definition write T lxp ixp inum off v ms rx : prog T :=
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    ms <- LOG.write lxp (# bn) v ms;
    rx ms.

  Definition dwrite T lxp ixp inum off v ms rx : prog T :=
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    ms <- LOG.dwrite lxp (# bn) v ms;
    rx ms.

  Definition grow T lxp bxp ixp inum v ms rx : prog T :=
    let^ (ms, len) <- INODE.getlen lxp ixp inum ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (ms, r) <- BALLOC.alloc lxp bxp ms;
      match r with
      | None => rx ^(ms, false)
      | Some bn =>
           let^ (ms, succ) <- INODE.grow lxp bxp ixp inum bn ms;
           If (bool_dec succ true) {
              ms <- LOG.write lxp bn v ms;
              rx ^(ms, true)
           } else {
             rx ^(ms, false)
           }
      end
    } else {
      rx ^(ms, false)
    }.

  Definition shrink T lxp bxp ixp inum nr ms rx : prog T :=
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    ms <- BALLOC.freevec lxp bxp l ms;
    ms <- INODE.shrink lxp bxp ixp inum nr ms;
    rx ms.


  (* rep invariants *)

  Definition attr := INODE.iattr.
  Definition attr0 := INODE.iattr0.

  Definition datatype := valuset.

  Record bfile := mk_bfile {
    BFData : list datatype;
    BFAttr : attr
  }.

  Definition bfile0 := mk_bfile nil attr0.

  Definition file_match f i : @pred _ addr_eq_dec datatype :=
    (listmatch (fun v a => a |-> v ) (BFData f) (map (@wordToNat _) (INODE.IBlocks i)) *
     [[ BFAttr f = INODE.IAttr i ]])%pred.

  Definition rep bxp ixp (flist : list bfile) :=
    (exists freeblocks ilist,
     BALLOC.rep bxp freeblocks * INODE.rep bxp ixp ilist *
     listmatch file_match flist ilist
    )%pred.


  (**** automation **)

  Fact resolve_selN_bfile0 : forall l i d,
    d = bfile0 -> selN l i d = selN l i bfile0.
  Proof.
    intros; subst; auto.
  Qed.

  Fact resolve_selN_vs0 : forall l i (d : valuset),
    d = ($0, nil) -> selN l i d = selN l i ($0, nil).
  Proof.
    intros; subst; auto.
  Qed.

  Hint Rewrite resolve_selN_bfile0 using reflexivity : defaults.
  Hint Rewrite resolve_selN_vs0 using reflexivity : defaults.

  (*** specification *)

  Theorem getlen_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:^(ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = length (BFData f) ]]
    CRASH  LOG.intact lxp F m0
    >} getlen lxp ixp inum ms.
  Proof.
    unfold getlen, rep.
    hoare.

    sepauto.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    destruct_lift H; eauto.
  Qed.


  Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:^(ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = BFAttr f ]]
    CRASH  LOG.intact lxp F m0
    >} getattrs lxp ixp inum ms.
  Proof.
    unfold getattrs, rep.
    hoare.

    sepauto.
    extract; seprewrite.
    subst; eauto.
  Qed.


  Theorem setattrs_ok : forall lxp bxp ixp inum a ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) a ]]
    CRASH  LOG.intact lxp F m0
    >} setattrs lxp ixp inum a ms.
  Proof.
    unfold setattrs, rep.
    hoare.

    sepauto.
    repeat extract. seprewrite.
    2: sepauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.
    Unshelve. exact INODE.inode0.
  Qed.


  Theorem updattr_ok : forall lxp bxp ixp inum kv ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (INODE.iattr_upd (BFAttr f) kv) ]]
    CRASH  LOG.intact lxp F m0
    >} updattr lxp ixp inum kv ms.
  Proof.
    unfold updattr, rep.
    hoare.

    sepauto.
    repeat extract. seprewrite.
    2: sepauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.
    Unshelve. exact INODE.inode0.
  Qed.


  Theorem read_ok : forall lxp bxp ixp inum off ms,
    {< F Fm Fi Fd m0 m flist f vs,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ r = fst vs ]]
    CRASH  LOG.intact lxp F m0
    >} read lxp ixp inum off ms.
  Proof.
    unfold read, rep.
    prestep; norml.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    rewrite map_length in *.
    destruct_lift H; cancel; eauto.

    sepauto.
    setoid_rewrite listmatch_extract with (i := off) in H at 2; try omega.
    destruct_lift H; filldef.
    step.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 2; cancel.
    step.
    Unshelve. eauto.
  Qed.


  Theorem write_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd m0 m flist f vs0,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs0) ]]]
    POST RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, nil)) (BFAttr f) ]]
    CRASH  LOG.intact lxp F m0
    >} write lxp ixp inum off v ms.
  Proof.
    unfold write, rep.
    prestep; norml.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    rewrite map_length in *.
    destruct_lift H; cancel; eauto.

    sepauto.
    setoid_rewrite listmatch_extract with (i := off) in H at 2; try omega.
    destruct_lift H; filldef.
    step.

    setoid_rewrite INODE.inode_rep_bn_nonzero_pimpl in H.
    destruct_lift H; denote (_ <> 0) as Hx; subst.
    eapply Hx; eauto; omega.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 2; cancel.

    step; [ | sepauto .. ].
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (ix := off) at 15.
    rewrite listmatch_updN_removeN by omega.
    erewrite selN_map by omega; filldef.
    cancel.

    Unshelve. all: eauto.
    Grab Existential Variables. eauto.
  Qed.


  Theorem grow_ok : forall lxp bxp ixp inum v ms,
    {< F Fm Fi Fd m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST RET:^(ms, r) exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms  \/
           [[ r = true  ]] * exists flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * (length (BFData f)) |-> (v, nil)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ [(v, nil)]) (BFAttr f) ]]
    CRASH  LOG.intact lxp F m0
    >} grow lxp bxp ixp inum v ms.
  Proof.
    unfold grow, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; cancel; eauto.

    sepauto.
    step.

    (* file size ok, do allocation *)
    step.
    step.
    sepauto.

    hoare.
    eapply BALLOC.bn_valid_facts; eauto.

    or_r; cancel.
    2: sepauto.
    seprewrite.
    rewrite listmatch_updN_removeN by simplen.
    unfold file_match; cancel.
    rewrite map_app; simpl.
    rewrite <- listmatch_app_tail.
    cancel.
    rewrite map_length; omega.
    rewrite wordToNat_natToWord_idempotent'; auto.
    eapply BALLOC.bn_valid_goodSize; eauto.
    apply list2nmem_app; eauto.

    step.
    Unshelve. all: easy.
  Qed.

  Local Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.

  Theorem shrink_ok : forall lxp bxp ixp inum nr ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (firstn ((length (BFData f)) - nr) (BFData f)) (BFAttr f) ]]
    CRASH  LOG.intact lxp F m0
    >} shrink lxp bxp ixp inum nr ms.
  Proof.
    unfold shrink, rep.
    step.
    sepauto.
    extract; seprewrite; subst; denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.

    step.
    rewrite INODE.inode_rep_bn_valid_piff in Hx; destruct_lift Hx.
    denote Forall as Hv; specialize (Hv inum); subst.
    apply Forall_map; apply forall_skipn; apply Hv; eauto.
    erewrite <- listmatch_ptsto_listpred.
    setoid_rewrite listmatch_split at 2.
    rewrite skipn_map_comm; cancel.
    destruct_lift Hx; denote (length (BFData _)) as Heq.

    step.
    sepauto.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    prestep; norm; [ cancel | intuition ]; [ | sepauto ].
    pred_apply; cancel.
    seprewrite.
    rewrite listmatch_updN_removeN by omega.
    rewrite firstn_map_comm, Heq.
    unfold file_match, cuttail; cancel; eauto.

    Unshelve. easy. exact bfile0.
  Qed.


  Theorem dwrite_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd m flist f vs,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m m) ms *
           [[ off < length (BFData f) ]] *
           [[[ m  ::: (Fm  * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m' m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, vsmerge vs)) (BFAttr f) ]]
    CRASH  LOG.intact lxp F m \/
           exists m' flist' f', LOG.intact lxp F m' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, vsmerge vs)) (BFAttr f) ]]
    >} dwrite lxp ixp inum off v ms.
  Proof.
    unfold dwrite, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; cancel; eauto.

    sepauto.
    denote removeN as Hx.
    setoid_rewrite listmatch_extract with (i := off) (bd := 0) in Hx; try omega.
    destruct_lift Hx.
    step.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 2; cancel.

    safestep; auto; sepauto.
    cancel.
    abstract (
      setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4;
      rewrite listmatch_updN_removeN by omega;
      unfold file_match at 3; cancel; eauto;
      setoid_rewrite <- updN_selN_eq with (l := INODE.IBlocks _) (ix := off) at 3;
      erewrite map_updN by omega; filldef;
      rewrite listmatch_updN_removeN by omega;
      cancel
    ) using dwrite_ok_helper.

    or_l; cancel; eauto.
    or_r; cancel; sepauto.
    pred_apply; cancel.
    eapply dwrite_ok_helper; eauto.
    or_l; cancel; eauto.
    cancel; or_l; eauto.
    Unshelve. all: easy.
  Qed.


  Hint Extern 1 ({{_}} progseq (getlen _ _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} progseq (getattrs _ _ _ _) _) => apply getattrs_ok : prog.
  Hint Extern 1 ({{_}} progseq (setattrs _ _ _ _ _) _) => apply setattrs_ok : prog.
  Hint Extern 1 ({{_}} progseq (updattr _ _ _ _ _) _) => apply updattr_ok : prog.
  Hint Extern 1 ({{_}} progseq (read _ _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (dwrite _ _ _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} progseq (grow _ _ _ _ _ _) _) => apply grow_ok : prog.
  Hint Extern 1 ({{_}} progseq (shrink _ _ _ _ _ _) _) => apply shrink_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.



  Definition grown T lxp bxp ixp inum l ms rx : prog T :=
    let^ (ms) <- ForN i < length l
      Ghost [ F Fm Fi m0 f ]
      Loopvar [ ms ]
      Continuation lrx
      Invariant
        exists m' flist' f',
        LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
        [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
        [[[ flist' ::: (Fi * inum |-> f') ]]] *
        [[ f' = mk_bfile ((BFData f) ++ synced_list (firstn i l)) (BFAttr f) ]]
      OnCrash
        LOG.intact lxp F m0
      Begin
        let^ (ms, ok) <- grow lxp bxp ixp inum (selN l i $0) ms;
        If (bool_dec ok true) {
          lrx ^(ms)
        } else {
          rx ^(ms, false)
        }
      Rof ^(ms);
    rx ^(ms, true).



  Definition truncate T lxp bxp xp inum newsz ms rx : prog T :=
    let^ (ms, sz) <- getlen lxp xp inum ms;
    If (lt_dec newsz sz) {
      ms <- shrink lxp bxp xp inum (sz - newsz) ms;
      rx ^(ms, true)
    } else {
      let^ (ms, ok) <- grown lxp bxp xp inum (repeat $0 (newsz - sz))  ms;
      rx ^(ms, ok)
    }.


  Definition reset T lxp bxp xp inum ms rx : prog T :=
    let^ (ms, sz) <- getlen lxp xp inum ms;
    ms <- shrink lxp bxp xp inum sz ms;
    ms <- setattrs lxp xp inum attr0 ms;
    rx ms.


  Theorem grown_ok : forall lxp bxp ixp inum l ms,
    {< F Fm Fi Fd m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST RET:^(ms, r) exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms  \/
           [[ r = true  ]] * exists flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * arrayN (length (BFData f)) (synced_list l)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ (synced_list l)) (BFAttr f) ]]
    CRASH  LOG.intact lxp F m0
    >} grown lxp bxp ixp inum l ms.
  Proof.
    unfold grown; intros.
    step.

    unfold synced_list; simpl; rewrite app_nil_r.
    replace f with ({| BFData := BFData f; BFAttr := BFAttr f|}) at 1; try cancel.
    destruct f; simpl; auto.

    step.
    subst; simpl; apply list2nmem_arrayN_app; eauto.
    hoare.

    erewrite firstn_S_selN_expand by omega.
    rewrite synced_list_app, <- app_assoc.
    unfold synced_list at 3; simpl; eauto.

    step.
    or_r; cancel.
    rewrite firstn_oob; auto.
    apply list2nmem_arrayN_app; auto.
    Unshelve. all: easy.
  Qed.


  Hint Extern 1 ({{_}} progseq (grown _ _ _ _ _ _) _) => apply grown_ok : prog.

  Theorem truncate_ok : forall lxp bxp ixp inum sz ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:^(ms, r) exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms  \/
           [[ r = true  ]] * exists flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (setlen (BFData f) sz ($0, nil)) (BFAttr f) ]]
    CRASH  LOG.intact lxp F m0
    >} truncate lxp bxp ixp inum sz ms.
  Proof.
    unfold truncate; intros.
    hoare.
    or_r; cancel.
    rewrite setlen_inbound, Rounding.sub_sub_assoc by omega; auto.
    apply list2nmem_array.
    or_r; cancel.
    rewrite setlen_oob by omega.
    unfold synced_list.
    rewrite repeat_length, combine_repeat; auto.
  Qed.

  Theorem reset_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist f,
    PRE    LOG.rep lxp F (LOG.ActiveTxn m0 m) ms *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST RET:ms exists m' flist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> bfile0) ]]]
    CRASH  LOG.intact lxp F m0
    >} reset lxp bxp ixp inum ms.
  Proof.
    unfold reset; intros.
    hoare.
    rewrite Nat.sub_diag; simpl; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (truncate _ _ _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} progseq (reset _ _ _ _ _) _) => apply reset_ok : prog.


End BFILE.


