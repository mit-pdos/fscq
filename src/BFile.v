Require Import Arith.
Require Import Pred PredCrash.
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
Require Import NEList.


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

  Definition datasync T lxp ixp inum ms rx : prog T :=
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    ms <- LOG.dsync_vecs lxp (map (@wordToNat _) bns) ms;
    rx ms.

(*
  Definition grow T lxp bxp1 bxp2 ixp inum v ms rx : prog T :=
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

*)
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

  Definition rep bxp1 bxp2 ixp (flist : list bfile) ilist freeblocks :=
    (exists freeblocks1 freeblocks2,
     BALLOC.rep bxp1 freeblocks1 * BALLOC.rep bxp2 freeblocks2 * INODE.rep bxp1 ixp ilist *
     listmatch file_match flist ilist *
     [[ freeblocks = freeblocks1 ++ freeblocks2 ]] (* select based on memstate *)
    )%pred.

  Definition block_belong_to_file ilist bn inum off :=
    bn = selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0.

  Definition block_is_unused freeblocks (bn : addr) := In bn freeblocks.

  Definition ilist_safe ilist1 free1 ilist2 free2 :=
    incl free2 free1 /\
    forall inum off bn,
        block_belong_to_file ilist2 bn inum off ->
        (block_belong_to_file ilist1 bn inum off \/
         block_is_unused free1 # bn).

  Theorem ilist_safe_trans : forall i1 f1 i2 f2 i3 f3,
    ilist_safe i1 f1 i2 f2 ->
    ilist_safe i2 f2 i3 f3 ->
    ilist_safe i1 f1 i3 f3.
  Admitted.

  Theorem rep_safe_used: forall bxp1 bxp2 ixp flist ilist m bn inum off free v,
    rep bxp1 bxp2 ixp flist ilist free (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    let f := selN flist inum bfile0 in
    let f' := mk_bfile (updN (BFData f) off v) (BFAttr f) in
    let flist' := updN flist inum f' in
    rep bxp1 bxp2 ixp flist' ilist free (list2nmem (updN m #bn v)).
  Admitted.

  Theorem rep_safe_unused: forall bxp1 bxp2 ixp flist ilist m free bn v,
    rep bxp1 bxp2 ixp flist ilist free (list2nmem m) ->
    block_is_unused free bn ->
    rep bxp1 bxp2 ixp flist ilist free (list2nmem (updN m bn v)).
  Admitted.

  Definition synced_file f := mk_bfile (synced_list (map fst (BFData f))) (BFAttr f).

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

  Theorem getlen_ok : forall lxp bxp1 bxp2 ixp inum ms,
    {< F Fm Fi m0 m f flist ilist free,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp1 bxp2 ixp flist ilist free) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = length (BFData f) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} getlen lxp ixp inum ms.
  Proof.
    unfold getlen, rep.
    hoare.

    sepauto.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    destruct_lift H; eauto.
    simplen.
  Qed.


(*
  Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms,r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = BFAttr f ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} getattrs lxp ixp inum ms.
  Proof.
    unfold getattrs, rep.
    hoare.

    sepauto.
    extract; seprewrite.
    subst; eauto.
  Qed.
*)


  Theorem setattrs_ok : forall lxp bxp1 bxp2 ixp inum a ms,
    {< F Fm Fi m0 m flist ilist free f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp1 bxp2 ixp flist ilist free) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms  exists m' flist' f' ilist' free',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp1 bxp2 ixp flist' ilist' free') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) a ]] *
           [[ ilist_safe ilist free ilist' free' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} setattrs lxp ixp inum a ms.
  Proof.
    unfold setattrs, rep.
    safestep.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    3: sepauto.
    3: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.
    reflexivity.
    Unshelve. exact INODE.inode0.
  Admitted.


  Theorem updattr_ok : forall lxp bxp ixp inum kv ms,
    {< F Fm Fi m0 m flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (INODE.iattr_upd (BFAttr f) kv) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} updattr lxp ixp inum kv ms.
  Proof.
    unfold updattr, rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    eapply listmatch_updN_selN; try omega.
    2: eauto.
    unfold file_match; cancel.
    Unshelve. exact INODE.inode0.
  Qed.


  Theorem read_ok : forall lxp bxp ixp inum off ms,
    {< F Fm Fi Fd m0 m flist f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(ms, r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm' *
           [[ r = fst vs ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} read lxp ixp inum off ms.
  Proof.
    unfold read, rep.
    prestep; norml.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    rewrite map_length in *.
    destruct_lift H.
    safecancel.
    eauto.

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
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs0) ]]]
    POST:hm' RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, nil)) (BFAttr f) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write lxp ixp inum off v ms.
  Proof.
    unfold write, rep.
    prestep; norml.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    rewrite map_length in *.
    destruct_lift H; safecancel.
    eauto.
    sepauto.

    setoid_rewrite listmatch_extract with (i := off) in H at 2; try omega.
    destruct_lift H; filldef.
    step.

    setoid_rewrite INODE.inode_rep_bn_nonzero_pimpl in H.
    destruct_lift H; denote (_ <> 0) as Hx; subst.
    eapply Hx; eauto; omega.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 2; cancel.

    safestep; [ | sepauto .. ].
    rename dummy0 into ilist.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (ix := off) at 15.
    rewrite listmatch_updN_removeN by omega.
    erewrite selN_map by omega; filldef.
    cancel.
    sepauto.

    pimpl_crash; cancel; auto.
    Grab Existential Variables. all: eauto.
  Qed.


  Theorem grow_ok : forall lxp bxp ixp inum v ms,
    {< F Fm Fi Fd m0 m flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms, r) exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' \/
           [[ r = true  ]] * exists flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * (length (BFData f)) |-> (v, nil)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ [(v, nil)]) (BFAttr f) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow lxp bxp ixp inum v ms.
  Proof.
    unfold grow, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; safecancel.
    eauto.

    sepauto.
    step.

    (* file size ok, do allocation *)
    step.
    safestep.
    sepauto.

    step; step.
    eapply BALLOC.bn_valid_facts; eauto.
    step.

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
    cancel.
    or_l; cancel.

    step.
    cancel; eauto.
    Unshelve. all: easy.
  Qed.

  Local Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.

  Theorem shrink_ok : forall lxp bxp ixp inum nr ms,
    {< F Fm Fi m0 m flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (firstn ((length (BFData f)) - nr) (BFData f)) (BFAttr f) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
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
    rewrite <- Forall_map.
    apply forall_skipn; apply Hv; eauto.
    erewrite <- listmatch_ptsto_listpred.
    setoid_rewrite listmatch_split at 2.
    rewrite skipn_map_comm; cancel.
    destruct_lift Hx; denote (length (BFData _)) as Heq.

    step.
    sepauto.
    denote listmatch as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    prestep; norm; [ cancel | intuition ]; [ | sepauto ].
    pred_apply; cancel.
    seprewrite.
    rewrite listmatch_updN_removeN by omega.
    rewrite firstn_map_comm, Heq.
    unfold file_match, cuttail; cancel; eauto.

    Unshelve. easy. exact bfile0.
  Qed.


  Theorem dwrite_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd ds flist f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) ms hm *
           [[ off < length (BFData f) ]] *
           [[[ ds!! ::: (Fm  * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:ms  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn (m', nil) m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, vsmerge vs)) (BFAttr f) ]]
    XCRASH:hm'  LOG.recover_any lxp F ds hm' \/
           exists m' flist' f', LOG.intact lxp F (m', nil) hm' *
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

    prestep. norm. cancel.
    intuition simpl. pred_apply.
    3: sepauto. 2: sepauto.
    rename dummy0 into ilist; cancel.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (l := INODE.IBlocks _) (ix := off) at 3.
    erewrite map_updN by omega; filldef.
    rewrite listmatch_updN_removeN by omega.
    cancel.

    eauto.
    xcrash.
    or_r; cancel.
    xform_normr.
    rewrite LOG.active_intact.
    norm. cancel.
    intuition simpl. pred_apply.
    3: sepauto. 2: sepauto.

    rename dummy0 into ilist; cancel.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (l := INODE.IBlocks _) (ix := off) at 3.
    erewrite map_updN by omega; filldef.
    rewrite listmatch_updN_removeN by omega.
    cancel.

    xcrash.
    or_l; cancel.
    rewrite LOG.active_intact, LOG.intact_any; auto.
    Unshelve. all: easy.
  Qed.

  Lemma synced_list_map_fst_map : forall (vsl : list valuset),
    synced_list (map fst vsl) = map (fun x => (fst x, nil)) vsl.
  Proof.
    unfold synced_list; induction vsl; simpl; auto.
    f_equal; auto.
  Qed.

  Theorem datasync_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi ds flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) ms hm *
           [[[ ds!!  ::: (Fm  * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms  exists m' flist',
           LOG.rep lxp F (LOG.ActiveTxn (m', nil) m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> synced_file f) ]]]
    XCRASH:hm' LOG.recover_any lxp F ds hm'
    >} datasync lxp ixp inum ms.
  Proof.
    unfold datasync, synced_file, rep.
    step.
    sepauto.

    extract.
    step.
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    2: sepauto.

    cancel.
    rename dummy0 into ilist.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 3.
    rewrite listmatch_updN_removeN by simplen.
    unfold file_match; cancel; eauto.
    rewrite synced_list_map_fst_map.
    rewrite listmatch_map_l; sepauto.
    sepauto.
    eauto.

    (* crashes *)
    xcrash.
    xcrash.
    rewrite LOG.active_intact, LOG.intact_any; auto.
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
  Hint Extern 1 ({{_}} progseq (datasync _ _ _ _) _) => apply datasync_ok : prog.

  Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.



  Definition read_array T lxp ixp inum a i ms rx : prog T :=
    let^ (ms, r) <- read lxp ixp inum (a + i) ms;
    rx ^(ms, r).

  Definition write_array T lxp ixp inum a i v ms rx : prog T :=
    ms <- write lxp ixp inum (a + i) v ms;
    rx ms.

  Theorem read_array_ok : forall lxp bxp ixp inum a i ms,
    {< F Fm Fi Fd m0 m flist f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
           [[ r = fst (selN vsl i ($0, nil)) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} read_array lxp ixp inum a i ms.
  Proof.
    unfold read_array.
    hoare.

    denote (arrayN a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    rewrite isolateN_fwd with (i:=i) by auto.
    cancel.
  Qed.


  Theorem write_array_ok : forall lxp bxp ixp inum a i v ms,
    {< F Fm Fi Fd m0 m flist f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:ms' exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: Fd * arrayN a (updN vsl i (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) (a + i) (v, nil)) (BFAttr f) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_array lxp ixp inum a i v ms.
  Proof.
    unfold write_array.
    safestep.
    denote (arrayN a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    rewrite isolateN_fwd with (i:=i) by auto; filldef; cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto; cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _ _ _) _) => apply write_array_ok : prog.


  Definition read_range T A lxp ixp inum a nr (vfold : A -> valu -> A) v0 ms rx : prog T :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi Fd crash m0 m flist f vsl ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
      [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vsl)) v0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array lxp ixp inum a i ms;
      lrx ^(ms, vfold pf v)
    Rof ^(ms, v0);
    rx ^(ms, r).


  Theorem read_range_ok : forall A lxp bxp ixp inum a nr (vfold : A -> valu -> A) v0 ms,
    {< F Fm Fi Fd m0 m flist f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
           [[ nr <= length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
           [[ r = fold_left vfold (firstn nr (map fst vsl)) v0 ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} read_range lxp ixp inum a nr vfold v0 ms.
  Proof.
    unfold read_range.
    safestep. eauto.
    safestep.

    assert (m1 < length vsl).
    denote (arrayN a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    safestep.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    cancel.

    safestep.
    cancel.
    erewrite <- LOG.rep_hashmap_subset; eauto.
    Unshelve. all: eauto; exact tt.
  Qed.


  (* like read_range, but stops when cond is true *)
  Definition read_cond T A lxp ixp inum (vfold : A -> valu -> A) 
                       v0 (cond : A -> bool) ms rx : prog T :=
    let^ (ms, nr) <- getlen lxp ixp inum ms;
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi crash m0 m flist f ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
      [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[ pf = fold_left vfold (firstn i (map fst (BFData f))) v0 ]] *
      [[ cond pf = false ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read lxp ixp inum i ms;
      let pf' := vfold pf v in
      If (bool_dec (cond pf') true) {
        rx ^(ms, Some pf')
      } else {
        lrx ^(ms, pf')
      }
    Rof ^(ms, v0);
    rx ^(ms, None).


  Theorem read_cond_ok : forall A lxp bxp ixp inum (vfold : A -> valu -> A)
                                v0 (cond : A -> bool) ms,
    {< F Fm Fi m0 m flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ cond v0 = false ]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm' *
           ( exists v, 
             [[ r = Some v /\ cond v = true ]] \/
             [[ r = None /\ cond (fold_left vfold (map fst (BFData f)) v0) = false ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms' hm'
    >} read_cond lxp ixp inum vfold v0 cond ms.
  Proof.
    unfold read_cond.
    safestep.
    safestep. eauto.
    safestep.
    sepauto.

    safestep.
    safestep.
    or_l; cancel; filldef; eauto.

    safestep.
    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    apply not_true_is_false; auto.

    cancel.
    safestep.
    or_r; cancel.
    denote cond as Hx; rewrite firstn_oob in Hx; auto.
    rewrite map_length; auto.
    cancel.
    apply LOG.rep_hashmap_subset; eauto.

    Unshelve. all: try easy. exact ($0, nil).
  Qed.


  Hint Extern 1 ({{_}} progseq (read_range _ _ _ _ _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (read_cond _ _ _ _ _ _ _) _) => apply read_cond_ok : prog.


  Definition grown T lxp bxp ixp inum l ms rx : prog T :=
    let^ (ms) <- ForN i < length l
      Hashmap hm
      Ghost [ F Fm Fi m0 f ]
      Loopvar [ ms ]
      Continuation lrx
      Invariant
        exists m' flist' f',
        LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm *
        [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
        [[[ flist' ::: (Fi * inum |-> f') ]]] *
        [[ f' = mk_bfile ((BFData f) ++ synced_list (firstn i l)) (BFAttr f) ]]
      OnCrash
        LOG.intact lxp F m0 hm
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
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms, r) exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' \/
           [[ r = true  ]] * exists flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * arrayN (length (BFData f)) (synced_list l)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ (synced_list l)) (BFAttr f) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grown lxp bxp ixp inum l ms.
  Proof.
    unfold grown; intros.
    safestep.
    unfold synced_list; simpl; rewrite app_nil_r.
    eassign f; destruct f; auto.
    eauto.

    safestep.
    subst; simpl; apply list2nmem_arrayN_app; eauto.

    safestep; safestep.
    or_l; cancel.
    erewrite firstn_S_selN_expand by omega.
    rewrite synced_list_app, <- app_assoc.
    unfold synced_list at 3; simpl; eauto.

    step.
    safestep.
    or_r; cancel.
    rewrite firstn_oob; auto.
    apply list2nmem_arrayN_app; auto.
    rewrite firstn_oob; auto.

    cancel.
    Unshelve. all: easy.
  Qed.


  Hint Extern 1 ({{_}} progseq (grown _ _ _ _ _ _) _) => apply grown_ok : prog.

  Theorem truncate_ok : forall lxp bxp ixp inum sz ms,
    {< F Fm Fi m0 m flist f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms, r) exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' \/
           [[ r = true  ]] * exists flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (setlen (BFData f) sz ($0, nil)) (BFAttr f) ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
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
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * rep bxp ixp flist) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms exists m' flist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist') ]]] *
           [[[ flist' ::: (Fi * inum |-> bfile0) ]]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} reset lxp bxp ixp inum ms.
  Proof.
    unfold reset; intros.
    hoare.
    rewrite Nat.sub_diag; simpl; auto.
  Qed.

  Hint Extern 1 ({{_}} progseq (truncate _ _ _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} progseq (reset _ _ _ _ _) _) => apply reset_ok : prog.



  (** crash and recovery *)

  Definition FSynced f : Prop :=
     forall n, snd (selN (BFData f) n ($0, nil)) = nil.

  Definition file_crash f f' : Prop :=
    exists vs, possible_crash_list (BFData f) vs /\
    f' = mk_bfile (synced_list vs) (BFAttr f).

  Definition flist_crash fl fl' : Prop :=
    Forall2 file_crash fl fl'.

  Lemma flist_crash_length : forall a b,
    flist_crash a b -> length a = length b.
  Proof.
    unfold flist_crash; intros.
    eapply forall2_length; eauto.
  Qed.

  Lemma fsynced_synced_file : forall f,
    FSynced (synced_file f).
  Proof.
    unfold FSynced, synced_file, synced_list; simpl; intros.
    setoid_rewrite selN_combine; simpl.
    destruct (lt_dec n (length (BFData f))).
    rewrite repeat_selN; auto.
    rewrite map_length; auto.
    rewrite selN_oob; auto.
    rewrite repeat_length, map_length.
    apply not_lt; auto.
    rewrite repeat_length, map_length; auto.
  Qed.

  Lemma arrayN_synced_list_fsynced : forall f l,
    arrayN 0 (synced_list l) (list2nmem (BFData f)) ->
    FSynced f.
  Proof.
    unfold FSynced; intros.
    erewrite list2nmem_array_eq with (l' := (BFData f)) by eauto.
    rewrite synced_list_selN; simpl; auto.
  Qed.

  Lemma file_crash_attr : forall f f',
    file_crash f f' -> BFAttr f' = BFAttr f.
  Proof.
    unfold file_crash; intros.
    destruct H; intuition; subst; auto.
  Qed.

  Lemma file_crash_possible_crash_list : forall f f',
    file_crash f f' ->
    possible_crash_list (BFData f) (map fst (BFData f')).
  Proof.
    unfold file_crash; intros; destruct H; intuition subst.
    unfold synced_list; simpl.
    rewrite map_fst_combine; auto.
    rewrite repeat_length; auto.
  Qed.

  Lemma file_crash_data_length : forall f f',
    file_crash f f' -> length (BFData f) = length (BFData f').
  Proof.
    unfold file_crash; intros.
    destruct H; intuition subst; simpl.
    rewrite synced_list_length.
    apply possible_crash_list_length; auto.
  Qed.

  Lemma file_crash_synced : forall f f',
    file_crash f f' ->
    FSynced f ->
    f = f'.
  Proof.
    unfold FSynced, file_crash; intuition.
    destruct H; intuition subst; simpl.
    destruct f; simpl in *.
    f_equal.
    eapply list_selN_ext.
    rewrite synced_list_length.
    apply possible_crash_list_length; auto.
    intros.
    setoid_rewrite synced_list_selN.
    rewrite surjective_pairing at 1.
    rewrite H0.
    f_equal.
    erewrite possible_crash_list_unique with (b := x); eauto.
    erewrite selN_map; eauto.
  Qed.

  Lemma file_crash_fsynced : forall f f',
    file_crash f f' ->
    FSynced f'.
  Proof.
    unfold FSynced, file_crash; intuition.
    destruct H; intuition subst; simpl.
    rewrite synced_list_selN; auto.
  Qed.

  Lemma file_crash_ptsto : forall f f' vs F a,
    file_crash f f' ->
    (F * a |-> vs)%pred (list2nmem (BFData f)) ->
    (exists v, [[ In v (vsmerge vs) ]]  *
       crash_xform F * a |=> v)%pred (list2nmem (BFData f')).
  Proof.
    unfold file_crash; intros.
    repeat deex.
    eapply list2nmem_crash_xform in H0; eauto.
    pred_apply.
    xform_norm.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.

  Lemma xform_file_match : forall f ino,
    crash_xform (file_match f ino) =p=> 
      exists f', [[ file_crash f f' ]] * file_match f' ino.
  Proof.
    unfold file_match, file_crash; intros.
    xform_norm.
    rewrite xform_listmatch_ptsto.
    cancel; eauto; simpl; auto.
  Qed.

  Lemma xform_file_list : forall fs inos,
    crash_xform (listmatch file_match fs inos) =p=>
      exists fs', [[ flist_crash fs fs' ]] * listmatch file_match fs' inos.
  Proof.
    unfold listmatch, pprd.
    induction fs; destruct inos; xform_norm.
    cancel. instantiate(1 := nil); simpl; auto.
    apply Forall2_nil. simpl; auto.
    inversion H0.
    inversion H0.

    specialize (IHfs inos).
    rewrite crash_xform_sep_star_dist, crash_xform_lift_empty in IHfs.
    setoid_rewrite lift_impl with (Q := length fs = length inos) at 4; intros; eauto.
    rewrite IHfs; simpl.

    rewrite xform_file_match.
    cancel.
    eassign (f' :: fs'); cancel.
    apply Forall2_cons; auto.
    simpl; omega.
  Qed.

  Lemma xform_rep : forall bxp ixp flist,
    crash_xform (rep bxp ixp flist) =p=> 
      exists flist', [[ flist_crash flist flist' ]] * rep bxp ixp flist'.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOC.xform_rep.
    rewrite xform_file_list.
    cancel.
  Qed.

  Lemma xform_file_match_ptsto : forall F a vs f ino,
    (F * a |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (file_match f ino) =p=>
      exists f' v, file_match f' ino * 
      [[ In v (vsmerge vs) ]] *
      [[ (crash_xform F * a |=> v)%pred (list2nmem (BFData f')) ]].
  Proof.
    unfold file_crash, file_match; intros.
    xform_norm.
    rewrite xform_listmatch_ptsto.
    xform_norm.
    pose proof (list2nmem_crash_xform _ H1 H) as Hx.
    apply crash_xform_sep_star_dist in Hx.
    rewrite crash_xform_ptsto in Hx; destruct_lift Hx.

    norm.
    eassign (mk_bfile (synced_list l) (BFAttr f)); cancel.
    eassign (dummy).
    intuition subst; eauto.
  Qed.

 Lemma xform_rep_file : forall F bxp ixp fs f i,
    (F * i |-> f)%pred (list2nmem fs) ->
    crash_xform (rep bxp ixp fs) =p=> 
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' *
      [[ (arrayN_ex fs' i * i |-> f')%pred (list2nmem fs') ]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOC.xform_rep.
    rewrite xform_file_list.
    cancel.
    erewrite list2nmem_sel with (x := f) by eauto.
    apply forall2_selN; eauto.
    eapply list2nmem_inbound; eauto.
    apply list2nmem_ptsto_cancel.
    erewrite <- flist_crash_length; eauto.
    eapply list2nmem_inbound; eauto.
    Unshelve. all: eauto.
  Qed.

 Lemma xform_rep_file_pred : forall (F Fd : pred) bxp ixp fs f i,
    (F * i |-> f)%pred (list2nmem fs) ->
    (Fd (list2nmem (BFData f))) ->
    crash_xform (rep bxp ixp fs) =p=>
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' *
      [[ (arrayN_ex fs' i * i |-> f')%pred (list2nmem fs') ]] *
      [[ (crash_xform Fd)%pred (list2nmem (BFData f')) ]].
  Proof.
    intros.
    rewrite xform_rep_file by eauto.
    cancel. eauto.
    unfold file_crash in *.
    repeat deex; simpl.
    eapply list2nmem_crash_xform; eauto.
  Qed.

  Lemma xform_rep_off : forall Fm Fd bxp ixp ino off f fs vs,
    (Fm * ino |-> f)%pred (list2nmem fs) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (rep bxp ixp fs) =p=> 
      exists fs' f' v, [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' * [[ In v (vsmerge vs) ]] *
      [[ (arrayN_ex fs' ino * ino |-> f')%pred (list2nmem fs') ]] *
      [[ (crash_xform Fd * off |=> v)%pred (list2nmem (BFData f')) ]].
  Proof.
    Opaque vsmerge.
    intros.
    rewrite xform_rep_file by eauto.
    xform_norm.
    eapply file_crash_ptsto in H0; eauto.
    destruct_lift H0.
    cancel; eauto.
    Transparent vsmerge.
  Qed.


End BFILE.


