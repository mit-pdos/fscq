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
Require Import DiskSet.


Import ListNotations.

Set Implicit Arguments.

(** BFILE is a block-based file implemented on top of the log and the
inode representation. The API provides reading/writing single blocks,
changing the size of the file, and managing file attributes (which are
the same as the inode attributes). *)

Module BFILE.

  Definition memstate := (bool * LOG.memstate)%type.
  Definition mk_memstate a b : memstate := (a, b).
  Definition MSAlloc (ms : memstate) := fst ms.   (* which block allocator to use? *)
  Definition MSLL (ms : memstate) := snd ms.      (* lower-level state *)


  (* interface implementation *)

  Definition getlen T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    rx ^(mk_memstate al ms, n).

  Definition getattrs T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, n) <- INODE.getattrs lxp ixp inum ms;
    rx ^(mk_memstate al ms, n).

  Definition setattrs T lxp ixp inum a fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    ms <- INODE.setattrs lxp ixp inum a ms;
    rx (mk_memstate al ms).

  Definition updattr T lxp ixp inum kv fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    ms <- INODE.updattr lxp ixp inum kv ms;
    rx (mk_memstate al ms).

  Definition read T lxp ixp inum off fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    let^ (ms, v) <- LOG.read lxp (# bn) ms;
    rx ^(mk_memstate al ms, v).

  Definition write T lxp ixp inum off v fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    ms <- LOG.write lxp (# bn) v ms;
    rx (mk_memstate al ms).

  Definition dwrite T lxp ixp inum off v fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bn) <- INODE.getbnum lxp ixp inum off ms;
    ms <- LOG.dwrite lxp (# bn) v ms;
    rx (mk_memstate al ms).

  Definition datasync T lxp ixp inum fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    ms <- LOG.dsync_vecs lxp (map (@wordToNat _) bns) ms;
    rx (mk_memstate al ms).

  Definition pick_balloc A (a : A * A) (flag : bool) :=
    if flag then fst a else snd a.

  Definition grow T lxp bxps ixp inum v fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, len) <- INODE.getlen lxp ixp inum ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (ms, r) <- BALLOC.alloc lxp (pick_balloc bxps (negb al)) ms;
      match r with
      | None => rx ^(mk_memstate al ms, false)
      | Some bn =>
           let^ (ms, succ) <- INODE.grow lxp (pick_balloc bxps (negb al)) ixp inum bn ms;
           If (bool_dec succ true) {
              ms <- LOG.write lxp bn v ms;
              rx ^(mk_memstate al ms, true)
           } else {
             rx ^(mk_memstate al ms, false)
           }
      end
    } else {
      rx ^(mk_memstate al ms, false)
    }.

  Definition shrink T lxp bxps ixp inum nr fms rx : prog T :=
    let '(al, ms) := (MSAlloc fms, MSLL fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    ms <- BALLOC.freevec lxp (pick_balloc bxps al) l ms;
    ms <- INODE.shrink lxp (pick_balloc bxps al) ixp inum nr ms;
    rx (mk_memstate al ms).


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

  Definition rep (bxps : balloc_xparams * balloc_xparams) ixp (flist : list bfile) ilist frees flag :=
    ( exists free_1 free_2,
     BALLOC.rep (fst bxps) free_1 *
     BALLOC.rep (snd bxps) free_2 *
     INODE.rep (pick_balloc bxps flag) ixp ilist *
     listmatch file_match flist ilist *
     [[ frees = pick_balloc (free_1, free_2) flag ]] *
     [[ BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) ]]
    )%pred.

  Definition block_belong_to_file ilist bn inum off :=
    off < length (INODE.IBlocks (selN ilist inum INODE.inode0)) /\
    bn = # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0).

  Definition block_is_unused freeblocks (bn : addr) := In bn freeblocks.

  Definition ilist_safe ilist1 free1 ilist2 free2 :=
    incl free2 free1 /\
    forall inum off bn,
        block_belong_to_file ilist2 bn inum off ->
        (block_belong_to_file ilist1 bn inum off \/
         block_is_unused free1 bn).

  Theorem ilist_safe_refl : forall i f,
    ilist_safe i f i f.
  Proof.
    unfold ilist_safe; intuition.
  Qed.
  Local Hint Resolve ilist_safe_refl.

  Theorem ilist_safe_trans : forall i1 f1 i2 f2 i3 f3,
    ilist_safe i1 f1 i2 f2 ->
    ilist_safe i2 f2 i3 f3 ->
    ilist_safe i1 f1 i3 f3.
  Proof.
    unfold ilist_safe; intros.
    destruct H.
    destruct H0.
    split.
    - eapply incl_tran; eauto.
    - intros.
      specialize (H2 _ _ _ H3).
      destruct H2; eauto.
      right.
      unfold block_is_unused in *.
      eauto.
  Qed.

  Lemma block_belong_to_file_inum_ok : forall ilist bn inum off,
    block_belong_to_file ilist bn inum off ->
    inum < length ilist.
  Proof.
    intros.
    destruct (lt_dec inum (length ilist)); eauto.
    unfold block_belong_to_file in *.
    rewrite selN_oob in H by omega.
    simpl in H.
    omega.
  Qed.

  Theorem rep_safe_used: forall bxps ixp flist ilist m bn inum off frees v ms,
    rep bxps ixp flist ilist frees ms (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    let f := selN flist inum bfile0 in
    let f' := mk_bfile (updN (BFData f) off v) (BFAttr f) in
    let flist' := updN flist inum f' in
    rep bxps ixp flist' ilist frees ms (list2nmem (updN m bn v)).
  Proof.
    unfold rep; intros.
    destruct_lift H.
    rewrite listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    2: rewrite H6; eapply block_belong_to_file_inum_ok; eauto.

    assert (inum < length ilist) by ( eapply block_belong_to_file_inum_ok; eauto ).
    assert (inum < length flist) by ( rewrite H6; eauto ).

    remember H0 as H0'; clear HeqH0'.
    unfold block_belong_to_file in H0'; intuition.
    unfold file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFData _) in H; destruct_lift H.
    rewrite listmatch_extract with (i := off) (a := BFData _) in H.
    2: rewrite H14; rewrite map_length; eauto.

    erewrite selN_map in H; eauto.

    eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply ].
    2: eassign (natToWord addrlen 0).
    2: cancel.

    cancel.

    eapply pimpl_trans.
    2: eapply listmatch_isolate with (i := inum); eauto.
    2: rewrite length_updN; eauto.

    rewrite removeN_updN. cancel.
    unfold file_match; cancel.
    2: rewrite selN_updN_eq by ( rewrite H6; eauto ).
    2: simpl; eauto.

    eapply pimpl_trans.
    2: eapply listmatch_isolate with (i := off).
    2: rewrite selN_updN_eq by ( rewrite H6; eauto ).
    2: simpl.
    2: rewrite length_updN.
    2: rewrite H14; rewrite map_length; eauto.
    2: rewrite map_length; eauto.

    rewrite selN_updN_eq; eauto; simpl.
    erewrite selN_map by eauto.
    rewrite removeN_updN.
    rewrite selN_updN_eq by ( rewrite H14; rewrite map_length; eauto ).
    cancel.

  Grab Existential Variables.
  all: eauto.
  exact BFILE.bfile0.
  Qed.

  Theorem rep_safe_unused: forall bxps ixp flist ilist m frees bn v ms,
    rep bxps ixp flist ilist frees ms (list2nmem m) ->
    block_is_unused frees bn ->
    rep bxps ixp flist ilist frees ms (list2nmem (updN m bn v)).
  Proof.
    unfold rep, pick_balloc, block_is_unused; intros.
    destruct_lift H.
    destruct ms.
    - unfold BALLOC.rep at 1 in H.
      unfold BALLOC.Alloc.rep in H.
      destruct_lift H.

      remember H7 as H7'; clear HeqH7'.
      rewrite listpred_nodup_piff in H7'; [ | apply addr_eq_dec | apply ptsto_conflict ].
      rewrite listpred_remove in H7'; [ | apply ptsto_conflict | eauto ].
      rewrite H7' in H.
      destruct_lift H.
      eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply; cancel ].
      unfold BALLOC.rep at 2. unfold BALLOC.Alloc.rep.
      cancel; eauto.
      eapply pimpl_trans; [ | eapply listpred_remove'; eauto; apply ptsto_conflict ].
      cancel.
    - unfold BALLOC.rep at 2 in H.
      unfold BALLOC.Alloc.rep in H.
      destruct_lift H.

      remember H7 as H7'; clear HeqH7'.
      rewrite listpred_nodup_piff in H7'; [ | apply addr_eq_dec | apply ptsto_conflict ].
      rewrite listpred_remove in H7'; [ | apply ptsto_conflict | eauto ].
      rewrite H7' in H.
      destruct_lift H.
      eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply; cancel ].
      unfold BALLOC.rep at 3. unfold BALLOC.Alloc.rep.
      cancel; eauto.
      eapply pimpl_trans; [ | eapply listpred_remove'; eauto; apply ptsto_conflict ].
      cancel.

    Unshelve.
    all: apply addr_eq_dec.
  Qed.

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

  Ltac assignms :=
    match goal with
    [ fms : memstate |- LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (MSLL ?e) _ ] =>
      is_evar e; eassign (mk_memstate (MSAlloc fms) ms); simpl; eauto
    end.

  Local Hint Extern 1 (LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (MSLL ?e) _) => assignms.

  (*** specification *)

  Theorem getlen_ok : forall lxp bxps ixp inum ms,
    {< F Fm Fi m0 m f flist ilist frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxps ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = length (BFData f) /\ MSAlloc ms = MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} getlen lxp ixp inum ms.
  Proof.
    unfold getlen, rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite; subst.
    setoid_rewrite listmatch_length_pimpl in H at 2.
    destruct_lift H; eauto.
    simplen.

    cancel.
    eauto.
  Qed.

  Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = BFAttr f /\ MSAlloc ms = MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} getattrs lxp ixp inum ms.
  Proof.
    unfold getattrs, rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite.
    subst; eauto.

    cancel.
    eauto.
  Qed.


  Theorem setattrs_ok : forall lxp bxps ixp inum a ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxps ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' f' ilist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxps ixp flist' ilist' frees (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) a ]] *
           [[ MSAlloc ms = MSAlloc ms' /\ ilist_safe ilist frees ilist' frees ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} setattrs lxp ixp inum a ms.
  Proof.
    unfold setattrs, rep.
    safestep.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.

    rewrite listmatch_length_pimpl in H8; destruct_lift H8.
    assert (inum < length ilist) by ( rewrite <- H12; eapply list2nmem_inbound; eauto ).
    apply arrayN_except_upd in H10; eauto.
    apply list2nmem_array_eq in H10; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      erewrite selN_updN_eq in H7 by eauto. simpl in H7. eauto.
      erewrite selN_updN_eq in H8 by eauto. simpl in H8. eauto.
    - unfold block_belong_to_file in *; intuition.
      erewrite selN_updN_ne in H7 by eauto. simpl in H7. eauto.
      erewrite selN_updN_ne in H8 by eauto. simpl in H8. eauto.
  Qed.


  Theorem updattr_ok : forall lxp bxps ixp inum kv ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxps ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' ilist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxps ixp flist' ilist' frees (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (INODE.iattr_upd (BFAttr f) kv) ]] *
           [[ MSAlloc ms = MSAlloc ms' /\ ilist_safe ilist frees ilist' frees ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} updattr lxp ixp inum kv ms.
  Proof.
    unfold updattr, rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    2: sepauto.
    2: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.

    rewrite listmatch_length_pimpl in H8; destruct_lift H8.
    assert (inum < length ilist) by ( rewrite <- H12; eapply list2nmem_inbound; eauto ).
    apply arrayN_except_upd in H10; eauto.
    apply list2nmem_array_eq in H10; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      erewrite selN_updN_eq in H7 by eauto. simpl in H7. eauto.
      erewrite selN_updN_eq in H8 by eauto. simpl in H8. eauto.
    - unfold block_belong_to_file in *; intuition.
      erewrite selN_updN_ne in H7 by eauto. simpl in H7. eauto.
      erewrite selN_updN_ne in H8 by eauto. simpl in H8. eauto.
  Qed.


  Theorem read_ok : forall lxp bxp ixp inum off ms,
    {< F Fm Fi Fd m0 m flist ilist frees f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = fst vs /\ MSAlloc ms = MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
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
    safestep.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 1.
    cancel.
    step.
    cancel; eauto.
    cancel; eauto.
    Unshelve. eauto.
  Qed.


  Theorem write_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd m0 m flist ilist frees f vs0,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs0) ]]]
    POST:hm' RET:ms'  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist frees (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, nil)) (BFAttr f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]]
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
    setoid_rewrite surjective_pairing at 4.
    cancel.

    safestep; [ | sepauto .. ].
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
    {< F Fm Fi Fd m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms', r) [[ MSAlloc ms = MSAlloc ms' ]] * exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
           [[ r = true  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * (length (BFData f)) |-> (v, nil)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ [(v, nil)]) (BFAttr f) ]] *
           [[ ilist_safe ilist frees ilist' frees' ]]
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
    destruct (MSAlloc ms); simpl.
    - step.
      safestep.
      erewrite INODE.rep_bxp_switch by eassumption. cancel.
      sepauto.

      step; step.
      eapply BALLOC.bn_valid_facts; eauto.
      step.

      or_r; safecancel.
      erewrite INODE.rep_bxp_switch by ( apply eq_sym; eassumption ). cancel.
      2: eauto.
      4: eauto.
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

      2: cancel.
      2: or_l; cancel.

      admit.

    - step.
      safestep.
      erewrite INODE.rep_bxp_switch by eassumption. cancel.
      sepauto.

      step; step.
      eapply BALLOC.bn_valid_facts; eauto.
      step.

      or_r; cancel.
      erewrite INODE.rep_bxp_switch by ( apply eq_sym; eassumption ). cancel.
      2: eauto.
      4: eauto.
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

      2: cancel.
      2: or_l; cancel.

      admit.

    - step.
    - cancel; eauto.
    Unshelve. all: easy.
  Admitted.

  Local Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.

  Theorem shrink_ok : forall lxp bxp ixp inum nr ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' f' ilist' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (firstn ((length (BFData f)) - nr) (BFData f)) (BFAttr f) ]] *
           [[ MSAlloc ms = MSAlloc ms' /\ ilist_safe ilist frees ilist' frees' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} shrink lxp bxp ixp inum nr ms.
  Proof.
    unfold shrink, rep.
    step.
    sepauto.
    extract; seprewrite; subst; denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.

    destruct (MSAlloc ms); simpl.
    - step.
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
      prestep; norm. cancel. intuition simpl.
      2: sepauto.
      pred_apply; cancel.
      seprewrite.
      rewrite listmatch_updN_removeN by omega.
      rewrite firstn_map_comm, Heq.
      unfold file_match, cuttail; cancel; eauto.
      admit.
      eauto.

    - step.
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
      prestep; norm. cancel. intuition simpl.
      2: sepauto.
      pred_apply; cancel.
      seprewrite.
      rewrite listmatch_updN_removeN by omega.
      rewrite firstn_map_comm, Heq.
      unfold file_match, cuttail; cancel; eauto.
      admit.
      eauto.

    Unshelve. easy. exact bfile0.
  Admitted.


  Theorem dwrite_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd ds flist ilist frees f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (MSLL ms) hm *
           [[ off < length (BFData f) ]] *
           [[[ ds!! ::: (Fm  * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:ms'  exists flist' f' bn ds0 ds',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (MSLL ms') hm' *
           [[ ds' = dsupd ds0 bn (v, vsmerge vs) ]] *
           [[ ds0 = ds \/ ds0 = (ds!!, nil) ]] *
           [[ block_belong_to_file ilist bn inum off ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[[ ds'!! ::: (Fm  * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]]
    XCRASH:hm' exists bn,
           [[ block_belong_to_file ilist bn inum off ]] *
          (LOG.recover_any lxp F ds hm' \/
           LOG.intact lxp F (updN (ds !!) bn (v, vsmerge vs), nil) hm' \/
           LOG.intact lxp F (updN (fst ds) bn (v, vsmerge vs), nil) hm')
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
    setoid_rewrite surjective_pairing at 4. cancel.

    prestep. norm. cancel.
    intuition simpl. pred_apply.
    3: sepauto. 2: sepauto.
    cancel.
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
    norm. cancel. intuition. pred_apply.
    3: sepauto. 2: sepauto.

    cancel.
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
    {< F Fm Fi ds flist ilist free f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (MSLL ms) hm *
           [[[ ds!!  ::: (Fm  * rep bxp ixp flist ilist free (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist',
           LOG.rep lxp F (LOG.ActiveTxn (m', nil) m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist free (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> synced_file f) ]]] *
           [[ MSAlloc ms = MSAlloc ms' ]]
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

  Hint Extern 0 (okToUnify (rep _ _ _ _ _ _) (rep _ _ _ _ _ _)) => constructor : okToUnify.



  Definition read_array T lxp ixp inum a i ms rx : prog T :=
    let^ (ms, r) <- read lxp ixp inum (a + i) ms;
    rx ^(ms, r).

  Definition write_array T lxp ixp inum a i v ms rx : prog T :=
    ms <- write lxp ixp inum (a + i) v ms;
    rx ms.

  Theorem read_array_ok : forall lxp bxp ixp inum a i ms,
    {< F Fm Fi Fd m0 m flist ilist free f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist free (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = fst (selN vsl i ($0, nil)) /\ MSAlloc ms = MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
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
    {< F Fm Fi Fd m0 m flist ilist free f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist free (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:ms' exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist free (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: Fd * arrayN a (updN vsl i (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) (a + i) (v, nil)) (BFAttr f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_array lxp ixp inum a i v ms.
  Proof.
    unfold write_array.
    prestep. cancel.
    denote (arrayN a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; try omega.
    rewrite isolateN_fwd with (i:=i) by auto; filldef; cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto; cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (read_array _ _ _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _ _ _ _) _) => apply write_array_ok : prog.


  Definition read_range T A lxp ixp inum a nr (vfold : A -> valu -> A) v0 ms0 rx : prog T :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi Fd crash m0 m flist ilist frees f vsl ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
      [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms0)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vsl)) v0 ]] *
      [[ MSAlloc ms = MSAlloc ms0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array lxp ixp inum a i ms;
      lrx ^(ms, vfold pf v)
    Rof ^(ms0, v0);
    rx ^(ms, r).


  Theorem read_range_ok : forall A lxp bxp ixp inum a nr (vfold : A -> valu -> A) v0 ms,
    {< F Fm Fi Fd m0 m flist ilist frees f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN a vsl ]]] *
           [[ nr <= length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = fold_left vfold (firstn nr (map fst vsl)) v0 ]] *
           [[ MSAlloc ms = MSAlloc ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} read_range lxp ixp inum a nr vfold v0 ms.
  Proof.
    unfold read_range.
    safestep. eauto.
    prestep; norm. cancel. intuition simpl.
    pred_apply; substl (MSAlloc a0); cancel.
    eauto. eauto. omega.

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
                       v0 (cond : A -> bool) ms0 rx : prog T :=
    let^ (ms, nr) <- getlen lxp ixp inum ms0;
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi crash m0 m flist f ilist frees ]
    Loopvar [ ms pf ]
    Continuation lrx
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
      [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms0)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[ pf = fold_left vfold (firstn i (map fst (BFData f))) v0 ]] *
      [[ cond pf = false /\ MSAlloc ms = MSAlloc ms0 ]]
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
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ cond v0 = false ]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           ( exists v, 
             [[ r = Some v /\ cond v = true ]] \/
             [[ r = None /\ cond (fold_left vfold (map fst (BFData f)) v0) = false ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} read_cond lxp ixp inum vfold v0 cond ms.
  Proof.
    unfold read_cond.
    prestep. cancel.
    safestep. eauto.
    prestep; norm. cancel. intuition simpl. eauto.
    pred_apply; substl (MSAlloc a0); cancel.
    sepauto. sepauto.

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


  Definition grown T lxp bxp ixp inum l ms0 rx : prog T :=
    let^ (ms) <- ForN i < length l
      Hashmap hm
      Ghost [ F Fm Fi m0 f ilist frees ]
      Loopvar [ ms ]
      Continuation lrx
      Invariant
        exists m' flist' ilist' frees' f',
        LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms) hm *
        [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAlloc ms0)) ]]] *
        [[[ flist' ::: (Fi * inum |-> f') ]]] *
        [[ f' = mk_bfile ((BFData f) ++ synced_list (firstn i l)) (BFAttr f) ]] *
        [[ MSAlloc ms = MSAlloc ms0 /\ ilist_safe ilist frees ilist' frees' ]]
      OnCrash
        LOG.intact lxp F m0 hm
      Begin
        let^ (ms, ok) <- grow lxp bxp ixp inum (selN l i $0) ms;
        If (bool_dec ok true) {
          lrx ^(ms)
        } else {
          rx ^(ms, false)
        }
      Rof ^(ms0);
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
    {< F Fm Fi Fd m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms', r) [[ MSAlloc ms' = MSAlloc ms ]] * exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
           [[ r = true  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * arrayN (length (BFData f)) (synced_list l)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ (synced_list l)) (BFAttr f) ]] *
           [[ ilist_safe ilist frees ilist' frees' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grown lxp bxp ixp inum l ms.
  Proof.
    unfold grown; intros.
    safestep.
    unfold synced_list; simpl; rewrite app_nil_r.
    eassign f; destruct f; auto.
    eauto. eauto.

    safestep. substl (MSAlloc a); cancel. eauto.
    subst; simpl; apply list2nmem_arrayN_app; eauto.

    safestep; safestep.
    or_l; cancel. substl (MSAlloc ms); cancel. eauto.
    erewrite firstn_S_selN_expand by omega.
    rewrite synced_list_app, <- app_assoc.
    unfold synced_list at 3; simpl; eauto.
    eapply ilist_safe_trans; eauto.
    cancel.

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
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms) ) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms', r) [[ MSAlloc ms = MSAlloc ms' ]] * exists m',
           [[ r = false ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
           [[ r = true  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (setlen (BFData f) sz ($0, nil)) (BFAttr f) ]] *
           [[ ilist_safe ilist frees ilist' frees' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} truncate lxp bxp ixp inum sz ms.
  Proof.
    unfold truncate; intros.
    step.
    step.

    - safestep.
      substl (MSAlloc a); cancel. eauto.
      step.
      or_r; safecancel.
      substl (MSAlloc ms); cancel. eauto.
      rewrite setlen_inbound, Rounding.sub_sub_assoc by omega; auto.
      eauto.
      cancel.

    - safestep.
      substl (MSAlloc a); cancel. eauto.
      apply list2nmem_array.
      step.

      or_r; safecancel.
      substl (MSAlloc ms); cancel. eauto.
      rewrite setlen_oob by omega.
      unfold synced_list.
      rewrite repeat_length, combine_repeat; auto.
      eauto.
      cancel.
  Qed.


  Theorem reset_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAlloc ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms' exists m' flist' ilist' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAlloc ms)) ]]] *
           [[[ flist' ::: (Fi * inum |-> bfile0) ]]] *
           [[ MSAlloc ms = MSAlloc ms' /\ ilist_safe ilist frees ilist' frees' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} reset lxp bxp ixp inum ms.
  Proof.
    unfold reset; intros.
    step.
    prestep; norm. cancel. intuition simpl.
    substl (MSAlloc a); pred_apply; cancel. eauto.
    prestep; norm. cancel. intuition simpl.
    substl (MSAlloc r_); pred_apply; cancel. eauto.
    safestep.
    substl (MSAlloc ms); substl (MSAlloc a); cancel.
    pred_apply; rewrite Nat.sub_diag; simpl; auto.
    eapply ilist_safe_trans; eauto.
    cancel.
    cancel.
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

  Lemma xform_rep : forall bxp ixp flist ilist frees flag,
    crash_xform (rep bxp ixp flist ilist frees flag) =p=> 
      exists flist', [[ flist_crash flist flist' ]] *
      rep bxp ixp flist' ilist frees flag.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOC.xform_rep, BALLOC.xform_rep.
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

 Lemma xform_rep_file : forall F bxp ixp fs f i ilist frees flag,
    (F * i |-> f)%pred (list2nmem fs) ->
    crash_xform (rep bxp ixp fs ilist frees flag) =p=> 
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' ilist frees flag *
      [[ (arrayN_ex fs' i * i |-> f')%pred (list2nmem fs') ]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOC.xform_rep, BALLOC.xform_rep.
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

 Lemma xform_rep_file_pred : forall (F Fd : pred) bxp ixp fs f i ilist frees flag,
    (F * i |-> f)%pred (list2nmem fs) ->
    (Fd (list2nmem (BFData f))) ->
    crash_xform (rep bxp ixp fs ilist frees flag) =p=>
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' ilist frees flag *
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

  Lemma xform_rep_off : forall Fm Fd bxp ixp ino off f fs vs ilist frees flag,
    (Fm * ino |-> f)%pred (list2nmem fs) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (rep bxp ixp fs ilist frees flag) =p=> 
      exists fs' f' v, [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' ilist frees flag * [[ In v (vsmerge vs) ]] *
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


