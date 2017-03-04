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
Require Import Errno.
Require Import Lock.
Require Import FMapAVL.
Require Import FMapMem.
Require Import MapUtils.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import StringUtils.
Require Import Balloc.


Import ListNotations.

Set Implicit Arguments.

(** BFILE is a block-based file implemented on top of the log and the
inode representation. The API provides reading/writing single blocks,
changing the size of the file, and managing file attributes (which are
the same as the inode attributes). *)

Module Dcache := FMapAVL.Make(String_as_OT).
Module DcacheDefs := MapDefs String_as_OT Dcache.
Definition Dcache_type := Dcache.t (option (addr * bool)).

Module BFcache := FMapAVL.Make(Nat_as_OT).
Module BFcacheDefs := MapDefs Nat_as_OT BFcache.
Definition BFcache_type := BFcache.t Dcache_type.
Module BFM := MapMem Nat_as_OT BFcache.

Module BFILE.


  Record memstate := mk_memstate {
    MSAlloc : bool;         (* which block allocator to use? *)
    MSLL : LOG.memstate;    (* lower-level state *)
    MSAllocC: (BALLOCC.BmapCacheType * BALLOCC.BmapCacheType); 
    MSCache : BFcache_type
  }.

  Ltac msalloc_eq :=
    repeat match goal with
    | [ H: MSAlloc _ = MSAlloc _ |- _ ] => rewrite H in *; clear H
    | [ H: MSAllocC _ = MSAllocC _ |- _ ] => rewrite H in *; clear H
    | [ H: MSCache _ = MSCache _ |- _ ] => rewrite H in *; clear H
    end.

  Definition ms_empty sz := mk_memstate
    true
    (LOG.mk_memstate0 (Cache.BUFCACHE.cache0 sz))
    (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0)
    (BFcache.empty _).


  (* interface implementation *)

  Definition getlen lxp ixp inum fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, n) <- INODE.getlen lxp ixp inum ms;
    Ret ^(mk_memstate al ms alc cache, n).

  Definition getattrs lxp ixp inum fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, n) <- INODE.getattrs lxp ixp inum ms;
    Ret ^(mk_memstate al ms alc cache, n).

  Definition setattrs lxp ixp inum a fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms,  MSAllocC fms, MSCache fms) in
    ms <- INODE.setattrs lxp ixp inum a ms;
    Ret (mk_memstate al ms alc cache).

  Definition updattr lxp ixp inum kv fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    ms <- INODE.updattr lxp ixp inum kv ms;
    Ret (mk_memstate al ms alc cache).

  Definition read lxp ixp inum off fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    let^ (ms, v) <- LOG.read lxp (# bn) ms;
    Ret ^(mk_memstate al ms alc cache, v).

  Definition write lxp ixp inum off v fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, bn) <-INODE.getbnum lxp ixp inum off ms;
    ms <- LOG.write lxp (# bn) v ms;
    Ret (mk_memstate al ms alc cache).

  Definition dwrite lxp ixp inum off v fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, bn) <- INODE.getbnum lxp ixp inum off ms;
    ms <- LOG.dwrite lxp (# bn) v ms;
    Ret (mk_memstate al ms alc cache).

  Definition datasync lxp ixp inum fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    ms <- LOG.dsync_vecs lxp (map (@wordToNat _) bns) ms;
    Ret (mk_memstate al ms alc cache).

  Definition sync lxp (ixp : INODE.IRecSig.xparams) fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    ms <- LOG.flushall lxp ms;
    Ret (mk_memstate (negb al) ms alc cache).

  Definition sync_noop lxp (ixp : INODE.IRecSig.xparams) fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    ms <- LOG.flushall_noop lxp ms;
    Ret (mk_memstate (negb al) ms alc cache).

  Definition pick_balloc A (a : A * A) (flag : bool) :=
    if flag then fst a else snd a.

  Definition upd_balloc A (a : A * A) (new : A) (flag : bool) :=
    (if flag then new else fst a,
     if flag then snd a else new).

  Theorem pick_upd_balloc_negb : forall A flag p (new : A),
    pick_balloc p flag = pick_balloc (upd_balloc p new (negb flag)) flag.
  Proof.
    destruct flag, p; intros; reflexivity.
  Qed.

  Theorem pick_negb_upd_balloc : forall A flag p (new : A),
    pick_balloc p (negb flag) = pick_balloc (upd_balloc p new flag) (negb flag).
  Proof.
    destruct flag, p; intros; reflexivity.
  Qed.

  Theorem pick_upd_balloc_lift : forall A flag p (new : A),
    new = pick_balloc (upd_balloc p new flag) flag.
  Proof.
    destruct flag, p; intros; reflexivity.
  Qed.

  Definition grow lxp bxps ixp inum v fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, len) <- INODE.getlen lxp ixp inum ms;
    If (lt_dec len INODE.NBlocks) {
      let^ (cms, r) <- BALLOCC.alloc lxp (pick_balloc bxps al) (BALLOCC.mk_memstate ms (pick_balloc alc al));
      match r with
      | None => Ret ^(mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) al) cache, Err ENOSPCBLOCK)
      | Some bn =>
           let^ (cms, succ) <- INODE.grow lxp (pick_balloc bxps al) ixp inum bn cms;
           match succ with
           | Err e =>
             Ret ^(mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) al) cache, Err e)
           | OK _ =>
             ms <- LOG.write lxp bn v (BALLOCC.MSLog cms);
             Ret ^(mk_memstate al ms (upd_balloc alc (BALLOCC.MSCache cms) al) cache, OK tt)
           end
      end
    } else {
      Ret ^(mk_memstate al ms alc cache, Err EFBIG)
    }.

  Definition shrink lxp bxps ixp inum nr fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    let^ (ms, bns) <- INODE.getallbnum lxp ixp inum ms;
    let l := map (@wordToNat _) (skipn ((length bns) - nr) bns) in
    cms <- BALLOCC.freevec lxp (pick_balloc bxps (negb al)) l (BALLOCC.mk_memstate ms (pick_balloc alc (negb al)));
    cms <- INODE.shrink lxp (pick_balloc bxps (negb al)) ixp inum nr cms;
    Ret (mk_memstate al (BALLOCC.MSLog cms) (upd_balloc alc (BALLOCC.MSCache cms) (negb al)) cache).

  Definition shuffle_allocs lxp bxps ms cms :=
    let^ (ms, cms) <- ForN i < (BmapNBlocks (fst bxps) * valulen)
    Hashmap hm
    Ghost [ F Fm crash m0 ]
    Loopvar [ ms cms ]
    Invariant
         exists m' frees,
         LOG.rep lxp F (LOG.ActiveTxn m0 m') ms hm *
         [[[ m' ::: (Fm * BALLOCC.rep (fst bxps) (fst frees) (BALLOCC.mk_memstate ms (fst cms))   *
                         BALLOCC.rep (snd bxps) (snd frees) (BALLOCC.mk_memstate ms (snd cms))) ]]] *
         [[ forall bn, bn < (BmapNBlocks (fst bxps)) * valulen /\ bn >= i
             -> In bn (fst frees) ]]
    OnCrash crash
    Begin
      If (bool_dec (Nat.odd i) true) {
        fcms <- BALLOCC.steal lxp (fst bxps) i (BALLOCC.mk_memstate ms (fst cms));
        scms <- BALLOCC.free lxp (snd bxps) i (BALLOCC.mk_memstate (BALLOCC.MSLog fcms) (snd cms));
        Ret ^((BALLOCC.MSLog scms), ((BALLOCC.MSCache fcms), (BALLOCC.MSCache scms)))
      } else {
        Ret ^(ms, cms)
      }
    Rof ^(ms, cms);
    Ret ^(ms, cms).

  Definition init lxp bxps bixp ixp ms :=
    fcms <- BALLOCC.init_nofree lxp (snd bxps) ms;
    scms <- BALLOCC.init lxp (fst bxps) (BALLOCC.MSLog fcms);
    ms <- IAlloc.init lxp bixp (BALLOCC.MSLog scms);
    ms <- INODE.init lxp ixp ms;
    let^ (ms, cms) <- shuffle_allocs lxp bxps ms (BALLOCC.MSCache scms, BALLOCC.MSCache fcms);
    Ret (mk_memstate true ms cms (BFcache.empty _)).

  Definition recover ms :=
    Ret (mk_memstate true ms (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0)  (BFcache.empty _)).

  Definition cache_get inum fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    Ret ^(mk_memstate al ms alc cache, BFcache.find inum cache).

  Definition cache_put inum dc fms :=
    let '(al, ms, alc, cache) := (MSAlloc fms, MSLL fms, MSAllocC fms, MSCache fms) in
    Ret (mk_memstate al ms alc (BFcache.add inum dc cache)).


  (* rep invariants *)

  Definition attr := INODE.iattr.
  Definition attr0 := INODE.iattr0.

  Definition datatype := valuset.

  Record bfile := mk_bfile {
    BFData : list datatype;
    BFAttr : attr;
    BFCache : option Dcache_type
  }.

  Definition bfile0 := mk_bfile nil attr0 None.
  Definition freepred f := f = bfile0.

  Definition file_match f i : @pred _ addr_eq_dec datatype :=
    (listmatch (fun v a => a |-> v ) (BFData f) (map (@wordToNat _) (INODE.IBlocks i)) *
     [[ BFAttr f = INODE.IAttr i ]])%pred.

  Definition cache_ptsto inum (oc : option Dcache_type) : @pred _ addr_eq_dec _ :=
    ( match oc with
      | None => emp
      | Some c => inum |-> c
      end )%pred.

  Definition cache_rep mscache (flist : list bfile) (ilist : list INODE.inode) :=
     arrayN cache_ptsto 0 (map BFCache flist) (BFM.mm _ mscache).

  Definition rep (bxps : balloc_xparams * balloc_xparams) ixp (flist : list bfile) ilist frees cms mscache :=
    (exists lms, 
     BALLOCC.rep (fst bxps) (fst frees) (BALLOCC.mk_memstate lms (fst cms)) *
     BALLOCC.rep (snd bxps) (snd frees) (BALLOCC.mk_memstate lms (snd cms)) *
     INODE.rep (fst bxps) ixp ilist *
     listmatch file_match flist ilist *
     [[ locked (cache_rep mscache flist ilist) ]] *
     [[ BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) ]]
    )%pred.

  Definition rep_length_pimpl : forall bxps ixp flist ilist frees allocc mscache,
    rep bxps ixp flist ilist frees allocc mscache =p=>
    (rep bxps ixp flist ilist frees allocc mscache *
     [[ length flist = ((INODE.IRecSig.RALen ixp) * INODE.IRecSig.items_per_val)%nat ]] *
     [[ length ilist = ((INODE.IRecSig.RALen ixp) * INODE.IRecSig.items_per_val)%nat ]])%pred.
  Proof.
    unfold rep; intros.
    norm'l; unfold stars; simpl.
    rewrite INODE.rep_length_pimpl at 1.
    rewrite listmatch_length_pimpl at 1.
    cancel.
  Qed.

  Definition rep_alt (bxps : BALLOCC.Alloc.Alloc.BmpSig.xparams * BALLOCC.Alloc.Alloc.BmpSig.xparams)
                     ixp (flist : list bfile) ilist frees cms mscache msalloc :=
    (exists lms,
      BALLOCC.rep (pick_balloc bxps msalloc) (pick_balloc frees msalloc) (BALLOCC.mk_memstate lms (pick_balloc cms msalloc)) *
     BALLOCC.rep (pick_balloc bxps (negb msalloc)) (pick_balloc frees (negb msalloc)) (BALLOCC.mk_memstate lms (pick_balloc cms (negb msalloc))) *
     INODE.rep (pick_balloc bxps msalloc) ixp ilist *
     listmatch file_match flist ilist *
     [[ locked (cache_rep mscache flist ilist) ]] *
     [[ BmapNBlocks (pick_balloc bxps msalloc) = BmapNBlocks (pick_balloc bxps (negb msalloc)) ]]
    )%pred.

  Theorem rep_alt_equiv : forall bxps ixp flist ilist frees mscache allocc msalloc,
    rep bxps ixp flist ilist frees allocc mscache <=p=> rep_alt bxps ixp flist ilist frees allocc mscache msalloc.
  Proof.
    unfold rep, rep_alt; split; destruct msalloc; simpl.
    - cancel.
    - norml; unfold stars; simpl.
      rewrite INODE.rep_bxp_switch at 1 by eauto.
      cancel.
    - cancel.
    - norml; unfold stars; simpl.
      rewrite INODE.rep_bxp_switch at 1 by eauto.
      cancel.
  Qed.

  Definition clear_cache bf := mk_bfile (BFData bf) (BFAttr bf) None.
  Definition clear_caches bflist := map clear_cache bflist.

  Theorem rep_clear_freelist : forall bxps ixp flist ilist frees allocc mscache,
    rep bxps ixp flist ilist frees allocc mscache =p=>
    rep bxps ixp flist ilist frees (BALLOCC.Alloc.freelist0, BALLOCC.Alloc.freelist0) mscache.
  Proof.
    unfold rep; intros; cancel.
    rewrite <- BALLOCC.rep_clear_mscache_ok. cancel.
    rewrite <- BALLOCC.rep_clear_mscache_ok. cancel.
  Qed.

  Theorem rep_clear_bfcache : forall bxps ixp flist ilist frees allocc mscache,
    rep bxps ixp flist ilist frees allocc mscache =p=>
    rep bxps ixp (clear_caches flist) ilist frees allocc (BFcache.empty Dcache_type).
  Proof.
    unfold rep; intros; cancel.
    unfold clear_caches.
    rewrite listmatch_map_l.
    unfold file_match, clear_cache; simpl.
    reflexivity.

    rewrite locked_eq.
    unfold cache_rep, clear_caches, clear_cache.
    rewrite map_map; simpl.
    clear H2.
    generalize 0.
    induction flist; simpl; intros.
    apply BFM.mm_init.
    specialize (IHflist (S n)).
    pred_apply; cancel.
  Qed.

  Definition block_belong_to_file ilist bn inum off :=
    off < length (INODE.IBlocks (selN ilist inum INODE.inode0)) /\
    bn = # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0).

  Definition block_is_unused freeblocks (bn : addr) := In bn freeblocks.

  Definition block_is_unused_dec freeblocks (bn : addr) :
    { block_is_unused freeblocks bn } + { ~ block_is_unused freeblocks bn }
    := In_dec addr_eq_dec bn freeblocks.

  Lemma block_is_unused_xor_belong_to_file : forall F Ftop fsxp files ilist free allocc mscache m flag bn inum off,
    (F * rep fsxp Ftop files ilist free allocc mscache)%pred m ->
    block_is_unused (pick_balloc free flag) bn ->
    block_belong_to_file ilist bn inum off ->
    False.
  Proof.
    unfold rep, block_is_unused, block_belong_to_file; intuition.
    rewrite <- locked_eq with (x := bn) in H3.
    destruct_lift H.
    rewrite listmatch_isolate with (i := inum) in H.
    unfold file_match at 2 in H.
    erewrite listmatch_isolate with (i := off) (a := (BFData files ⟦ inum ⟧)) in H by simplen.
    erewrite selN_map in H; eauto.
    unfold BALLOCC.rep in H; destruct_lift H.
    unfold BALLOCC.Alloc.rep in H; destruct_lift H.
    unfold BALLOCC.Alloc.Alloc.rep in H; destruct_lift H.
    destruct flag; simpl in *.
    - destruct H20 as [H20 _]. rewrite listpred_pick in H20 by eauto.
      rewrite H20 in H.
      destruct_lift H.
      rewrite locked_eq in H3.
      rewrite <- H3 in H; clear H3.
      eapply ptsto_conflict_F with (m := m) (a := bn).
      pred_apply.
      destruct ((BFData files ⟦ inum ⟧) ⟦ off ⟧).
      cancel.
    - destruct H23 as [H23 _]. rewrite listpred_pick in H23 by eauto.
      rewrite H23 in H.
      destruct_lift H.
      rewrite locked_eq in H3.
      rewrite <- H3 in H; clear H3.
      eapply ptsto_conflict_F with (m := m) (a := bn).
      pred_apply.
      destruct ((BFData files ⟦ inum ⟧) ⟦ off ⟧).
      cancel.
    - erewrite listmatch_length_r; eauto.
      destruct (lt_dec inum (length ilist)); eauto.
      rewrite selN_oob in H2 by omega.
      unfold INODE.inode0 in H2; simpl in *; omega.
    - destruct (lt_dec inum (length ilist)); eauto.
      rewrite selN_oob in H2 by omega.
      unfold INODE.inode0 in H2; simpl in *; omega.

    Grab Existential Variables.
    exact ($0, nil).
    exact bfile0.
    exact 0.
  Qed.

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

  Lemma rep_used_block_eq_Some_helper : forall T (x y: T),
    Some x = Some y -> x = y.
  Proof.
    intros.
    inversion H.
    auto.
  Qed.

  Theorem rep_used_block_eq : forall F bxps ixp flist ilist m bn inum off frees allocc mscache,
    (F * rep bxps ixp flist ilist frees allocc mscache)%pred (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    selN (BFData (selN flist inum bfile0)) off ($0, nil) = selN m bn ($0, nil).
  Proof.
    unfold rep; intros.
    destruct_lift H.
    rewrite listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    2: substl (length flist); eapply block_belong_to_file_inum_ok; eauto.

    assert (inum < length ilist) by ( eapply block_belong_to_file_inum_ok; eauto ).
    assert (inum < length flist) by ( substl (length flist); eauto ).

    denote block_belong_to_file as Hx; assert (Hy := Hx).
    unfold block_belong_to_file in Hy; intuition.
    unfold file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFData _) in H; destruct_lift H.
    denote! (length _ = _) as Heq.
    rewrite listmatch_extract with (i := off) (a := BFData _) in H.
    2: rewrite Heq; rewrite map_length; eauto.

    erewrite selN_map in H; eauto.
    eapply rep_used_block_eq_Some_helper.
    apply eq_sym.
    rewrite <- list2nmem_sel_inb.

    eapply ptsto_valid.
    pred_apply.
    eassign (natToWord addrlen O).
    cancel.

    eapply list2nmem_inbound.
    pred_apply.
    cancel.

  Grab Existential Variables.
    all: eauto.
  Qed.

  Theorem rep_safe_used: forall F bxps ixp flist ilist m bn inum off frees allocc mscache v,
    (F * rep bxps ixp flist ilist frees allocc mscache)%pred (list2nmem m) ->
    block_belong_to_file ilist bn inum off ->
    let f := selN flist inum bfile0 in
    let f' := mk_bfile (updN (BFData f) off v) (BFAttr f) (BFCache f) in
    let flist' := updN flist inum f' in
    (F * rep bxps ixp flist' ilist frees allocc mscache)%pred (list2nmem (updN m bn v)).
  Proof.
    unfold rep; intros.
    destruct_lift H.
    rewrite listmatch_length_pimpl in H; destruct_lift H.
    rewrite listmatch_extract with (i := inum) in H.
    2: substl (length flist); eapply block_belong_to_file_inum_ok; eauto.

    assert (inum < length ilist) by ( eapply block_belong_to_file_inum_ok; eauto ).
    assert (inum < length flist) by ( substl (length flist); eauto ).

    denote block_belong_to_file as Hx; assert (Hy := Hx).
    unfold block_belong_to_file in Hy; intuition.
    unfold file_match at 2 in H.
    rewrite listmatch_length_pimpl with (a := BFData _) in H; destruct_lift H.
    denote! (length _ = _) as Heq.
    rewrite listmatch_extract with (i := off) (a := BFData _) in H.
    2: rewrite Heq; rewrite map_length; eauto.

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
    2: rewrite selN_updN_eq by ( substl (length flist); eauto ).
    2: simpl; eauto.

    eapply pimpl_trans.
    2: eapply listmatch_isolate with (i := off).
    2: rewrite selN_updN_eq by ( substl (length flist); eauto ).
    2: simpl.
    2: rewrite length_updN.
    2: rewrite Heq; rewrite map_length; eauto.
    2: rewrite map_length; eauto.

    rewrite selN_updN_eq; eauto; simpl.
    erewrite selN_map by eauto.
    rewrite removeN_updN.
    rewrite selN_updN_eq by ( rewrite Heq; rewrite map_length; eauto ).
    cancel.

    rewrite locked_eq in *; unfold cache_rep in *.
    pred_apply.
    rewrite map_updN.
    erewrite selN_eq_updN_eq by ( erewrite selN_map; eauto; reflexivity ).
    cancel.

  Grab Existential Variables.
    all: eauto.
    all: try exact BFILE.bfile0.
    all: try exact None.
  Qed.

  Theorem rep_safe_unused: forall F bxps ixp flist ilist m frees allocc mscache bn v flag,
    (F * rep bxps ixp flist ilist frees allocc mscache)%pred (list2nmem m) ->
    block_is_unused (pick_balloc frees flag) bn ->
    (F * rep bxps ixp flist ilist frees allocc mscache)%pred (list2nmem (updN m bn v)).
  Proof.
    unfold rep, pick_balloc, block_is_unused; intros.
    destruct_lift H.
    destruct flag.
    - unfold BALLOCC.rep at 1 in H.
      unfold BALLOCC.Alloc.rep in H.
      unfold BALLOCC.Alloc.Alloc.rep in H.
      destruct_lift H.

      denote listpred as Hx.
      assert (Hy := Hx).
      rewrite listpred_nodup_piff in Hy; [ | apply addr_eq_dec | ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      assert (Hnodup := H). rewrite Hy in Hnodup; destruct_lift Hnodup.

      rewrite listpred_remove_piff in Hy; [ | | eauto | eauto ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      rewrite Hy in H.
      destruct_lift H.
      eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply; cancel ].
      unfold BALLOCC.rep at 2. unfold BALLOCC.Alloc.rep. unfold BALLOCC.Alloc.Alloc.rep.

      norm; unfold stars; simpl.
      2: intuition eauto.
      cancel. rewrite Hy. cancel.

    - unfold BALLOCC.rep at 2 in H.
      unfold BALLOCC.Alloc.rep in H.
      unfold BALLOCC.Alloc.Alloc.rep in H.
      destruct_lift H.

      denote listpred as Hx.
      assert (Hy := Hx).
      rewrite listpred_nodup_piff in Hy; [ | apply addr_eq_dec | ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      assert (Hnodup := H). rewrite Hy in Hnodup; destruct_lift Hnodup.

      rewrite listpred_remove_piff in Hy; [ | | eauto | eauto ].

      2: intros; assert (~ (y |->? * y |->?)%pred m') as Hc by apply ptsto_conflict.
      2: contradict Hc; pred_apply; cancel.

      rewrite Hy in H.
      destruct_lift H.
      eapply pimpl_trans; [ apply pimpl_refl | | eapply list2nmem_updN; pred_apply; cancel ].
      unfold BALLOCC.rep at 3. unfold BALLOCC.Alloc.rep. unfold BALLOCC.Alloc.Alloc.rep.

      norm; unfold stars; simpl.
      2: intuition eauto.
      cancel. rewrite Hy. cancel.

    Unshelve.
    all: apply addr_eq_dec.
  Qed.

  Theorem block_belong_to_file_bfdata_length : forall bxp ixp flist ilist frees allocc mscache m F inum off bn,
    (F * rep bxp ixp flist ilist frees allocc mscache)%pred m ->
    block_belong_to_file ilist bn inum off ->
    off < length (BFData (selN flist inum BFILE.bfile0)).
  Proof.
    intros.
    apply block_belong_to_file_inum_ok in H0 as H0'.
    unfold block_belong_to_file, rep in *.
    setoid_rewrite listmatch_extract with (i := inum) in H.
    unfold file_match at 2 in H.
    setoid_rewrite listmatch_length_pimpl with (a := BFData _) in H.
    destruct_lift H.
    rewrite map_length in *.
    intuition.
    rewrite H12; eauto.
    setoid_rewrite listmatch_length_pimpl in H.
    destruct_lift H.
    rewrite H9. eauto.
  Qed.

  Definition synced_file f := mk_bfile (synced_list (map fst (BFData f))) (BFAttr f) (BFCache f).

  Lemma add_nonzero_exfalso_helper2 : forall a b,
    a * valulen + b = 0 -> a <> 0 -> False.
  Proof.
    intros.
    destruct a; auto.
    rewrite Nat.mul_succ_l in H.
    assert (0 < a * valulen + valulen + b).
    apply Nat.add_pos_l.
    apply Nat.add_pos_r.
    rewrite valulen_is; simpl.
    apply Nat.lt_0_succ.
    omega.
  Qed.

  Lemma file_match_init_ok : forall n,
    emp =p=> listmatch file_match (repeat bfile0 n) (repeat INODE.inode0 n).
  Proof.
    induction n; simpl; intros.
    unfold listmatch; cancel.
    rewrite IHn.
    unfold listmatch; cancel.
    unfold file_match, listmatch; cancel.
  Qed.

  Lemma odd_nonzero : forall n,
    Nat.odd n = true -> n <> 0.
  Proof.
    destruct n; intros; auto.
    cbv in H; congruence.
  Qed.

  Local Hint Resolve odd_nonzero.

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

  Lemma bfcache_init' : forall len start,
    arrayN cache_ptsto start (map BFCache (repeat bfile0 len))
      (BFM.mm Dcache_type (BFcache.empty Dcache_type)).
  Proof.
    induction len; simpl; intros.
    eapply BFM.mm_init.
    eapply pimpl_apply; [ | apply IHlen ].
    cancel.
  Qed.

  Lemma bfcache_init : forall len ilist,
    locked (cache_rep (BFcache.empty Dcache_type) (repeat bfile0 len) ilist).
  Proof.
    intros.
    rewrite locked_eq.
    unfold cache_rep.
    eapply bfcache_init'.
  Qed.

  Lemma bfcache_upd : forall mscache inum flist ilist F f d a,
    locked (cache_rep mscache flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep mscache (updN flist inum {| BFData := d; BFAttr := a; BFCache := BFCache f |}) ilist).
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    rewrite map_updN; simpl.
    eapply list2nmem_sel in H0 as H0'; rewrite H0'.
    erewrite selN_eq_updN_eq; eauto.
    erewrite selN_map; eauto.
    simplen.
  Unshelve.
    exact None.
  Qed.

  Lemma cache_ptsto_none'' : forall l start m idx,
    arrayN cache_ptsto start l m ->
    idx < start ->
    m idx = None.
  Proof.
    induction l; intros; eauto.
    simpl in H.
    eapply sep_star_none; intros; [ | | exact H ].
    destruct a; simpl in *.
    eapply ptsto_none; [ | eauto ]; omega.
    eauto.
    eapply IHl; eauto.
  Qed.

  Lemma cache_ptsto_none' : forall l start m idx def,
    arrayN cache_ptsto start l m ->
    idx < length l ->
    selN l idx def = None ->
    m (start + idx) = None.
  Proof.
    induction l; intros; eauto.
    simpl in H.
    eapply sep_star_none; eauto; intros.
    destruct a; simpl in *.
    eapply ptsto_none; [ | eauto ].
    destruct idx; try omega; try congruence.
    eauto.
    destruct idx.
    eapply cache_ptsto_none''; eauto; omega.
    replace (start + S idx) with (S start + idx) by omega.
    eapply IHl; eauto.
    simpl in *; omega.
  Qed.

  Lemma cache_ptsto_none : forall l m idx def,
    arrayN cache_ptsto 0 l m ->
    idx < length l ->
    selN l idx def = None ->
    m idx = None.
  Proof.
    intros.
    replace (idx) with (0 + idx) by omega.
    eapply cache_ptsto_none'; eauto.
  Qed.

  Lemma cache_ptsto_none_find : forall l c idx def,
    arrayN cache_ptsto 0 l (BFM.mm Dcache_type c) ->
    idx < length l ->
    selN l idx def = None ->
    BFcache.find idx c = None.
  Proof.
    intros.
    assert (BFM.mm Dcache_type c idx = None).
    eapply cache_ptsto_none; eauto.
    eauto.
  Qed.

  Lemma bfcache_find : forall c flist ilist inum f F,
    locked (cache_rep c flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    BFcache.find inum c = BFCache f.
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply arrayN_isolate with (i := inum) in H; [ | simplen ].
      unfold cache_ptsto at 2 in H. simpl in H.
      erewrite selN_map in H by simplen. rewrite <- H0' in H. rewrite H1 in H.
      eapply BFM.mm_find; pred_apply; cancel.
    - eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'.
      eauto.
  Unshelve.
    all: exact None.
  Qed.

  Lemma bfcache_put : forall msc flist ilist inum c f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep (BFcache.add inum c msc)
                      (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := Some c |})
                      ilist).
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply pimpl_apply.
      2: eapply BFM.mm_replace.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2; simpl.
      erewrite selN_map by simplen. rewrite selN_updN_eq by simplen. cancel.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      rewrite skipn_updN by omega.
      pred_apply.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2.
      erewrite selN_map by simplen. rewrite <- H0'. rewrite H1. cancel.
    - eapply pimpl_apply.
      2: eapply BFM.mm_add; eauto.
      rewrite arrayN_isolate with (i := inum) by simplen.
      rewrite arrayN_isolate with (i := inum) (vs := map _ _) by simplen.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      simpl; rewrite skipn_updN by omega.
      cancel.
      unfold cache_ptsto.
      erewrite selN_map by simplen. rewrite H1.
      rewrite selN_updN_eq by simplen.
      cancel.
      eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'; eauto.
  Unshelve.
    all: try exact None.
    all: eauto.
  Qed.

  Lemma bfcache_remove' : forall msc flist ilist inum f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    locked (cache_rep (BFcache.remove inum msc)
                      (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := None |})
                      ilist).
  Proof.
    intros.
    rewrite locked_eq in *.
    unfold cache_rep in *.
    eapply list2nmem_sel in H0 as H0'.
    case_eq (BFCache f); intros.
    - eapply pimpl_apply.
      2: eapply BFM.mm_remove.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2; simpl.
      erewrite selN_map by simplen. rewrite selN_updN_eq by simplen. cancel.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      rewrite skipn_updN by omega.
      pred_apply.
      rewrite arrayN_isolate with (i := inum) by simplen.
      unfold cache_ptsto at 2.
      erewrite selN_map by simplen. rewrite <- H0'. rewrite H1. cancel.
      cancel.
    - eapply pimpl_apply.
      2: eapply BFM.mm_remove_none; eauto.
      rewrite arrayN_isolate with (i := inum) by simplen.
      rewrite arrayN_isolate with (i := inum) (vs := map _ _) by simplen.
      rewrite map_updN. rewrite firstn_updN_oob by omega.
      simpl; rewrite skipn_updN by omega.
      cancel.
      unfold cache_ptsto.
      erewrite selN_map by simplen. rewrite H1.
      rewrite selN_updN_eq by simplen.
      cancel.
      eapply cache_ptsto_none_find; eauto.
      simplen.
      erewrite selN_map by simplen.
      rewrite <- H0'; eauto.
  Unshelve.
    all: try exact None.
    all: eauto.
  Qed.

  Lemma bfcache_remove : forall msc flist ilist inum f F,
    locked (cache_rep msc flist ilist) ->
    (F * inum |-> f)%pred (list2nmem flist) ->
    BFData f = nil ->
    BFAttr f = attr0 ->
    locked (cache_rep (BFcache.remove inum msc) (updN flist inum bfile0) ilist).
  Proof.
    intros.
    eapply bfcache_remove' in H; eauto.
    replace bfile0 with ({| BFData := BFData f; BFAttr := BFAttr f; BFCache := None |}); eauto.
    rewrite H1.
    rewrite H2.
    reflexivity.
  Qed.

  Lemma rep_bfcache_remove : forall bxps ixp flist ilist frees allocc mscache inum f F,
    (F * inum |-> f)%pred (list2nmem flist) ->
    rep bxps ixp flist ilist frees allocc mscache =p=>
    rep bxps ixp (updN flist inum {| BFData := BFData f; BFAttr := BFAttr f; BFCache := None |}) ilist frees allocc
      (BFcache.remove inum mscache).
  Proof.
    unfold rep; intros.
    cancel.
    2: eapply bfcache_remove'; eauto.
    seprewrite.
    erewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 2.
    rewrite listmatch_length_pimpl; cancel.
    eapply listmatch_updN_selN; try simplen.
    unfold file_match; cancel.
  Unshelve.
    exact INODE.inode0.
  Qed.

  Hint Resolve bfcache_init bfcache_upd.

  Ltac assignms :=
    match goal with
    [ fms : memstate |- LOG.rep _ _ _ ?ms _ =p=> LOG.rep _ _ _ (MSLL ?e) _ ] =>
      is_evar e; eassign (mk_memstate (MSAlloc fms) ms (MSAllocC fms) (MSCache fms)); simpl; eauto
    end.

  Local Hint Extern 1 (LOG.rep _ _ _ ?ms _  =p=> LOG.rep _ _ _ (MSLL ?e) _ ) => assignms.

  (*** specification *)


  Theorem shuffle_allocs_ok : forall lxp bxps ms cms,
    {< F Fm m0 m frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * BALLOCC.rep (fst bxps) (fst frees) (BALLOCC.mk_memstate ms (fst cms)) *
                           BALLOCC.rep (snd bxps) (snd frees) (BALLOCC.mk_memstate ms (snd cms))) ]]] *
           [[ forall bn, bn < (BmapNBlocks (fst bxps)) * valulen -> In bn (fst frees) ]] *
           [[ BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) ]]
    POST:hm' RET:^(ms',cms')  exists m' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') ms' hm' *
           [[[ m' ::: (Fm * BALLOCC.rep (fst bxps) (fst frees') (BALLOCC.mk_memstate ms' (fst cms')) *
                            BALLOCC.rep (snd bxps) (snd frees') (BALLOCC.mk_memstate ms' (snd cms'))) ]]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} shuffle_allocs lxp bxps ms cms.
  Proof.
    unfold shuffle_allocs.
    step.
    step.
    step.
    unfold BALLOCC.bn_valid; split; auto.
    step.
    unfold BALLOCC.bn_valid; split; auto.
    substl (BmapNBlocks bxps_2); auto.
    step.
    apply remove_other_In.
    omega.
    intuition.
    step.
    step.
    eapply LOG.intact_hashmap_subset.
    eauto.
    Unshelve. exact tt.
  Qed.

  Hint Extern 1 ({{_}} Bind (shuffle_allocs _ _ _ _) _) => apply shuffle_allocs_ok : prog.

  Local Hint Resolve INODE.IRec.Defs.items_per_val_gt_0 INODE.IRec.Defs.items_per_val_not_0 valulen_gt_0.

  Theorem init_ok : forall lxp bxps ibxp ixp ms,
    {< F Fm m0 m l,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) ms hm *
           [[[ m ::: (Fm * arrayN (@ptsto _ _ _) 0 l) ]]] *
           [[ let data_bitmaps := (BmapNBlocks (fst bxps)) in
              let inode_bitmaps := (IAlloc.Sig.BMPLen ibxp) in
              let data_blocks := (data_bitmaps * valulen)%nat in
              let inode_blocks := (inode_bitmaps * valulen / INODE.IRecSig.items_per_val)%nat in
              let inode_base := data_blocks in
              let balloc_base1 := inode_base + inode_blocks + inode_bitmaps in
              let balloc_base2 := balloc_base1 + data_bitmaps in
              length l = balloc_base2 + data_bitmaps /\
              BmapNBlocks (fst bxps) = BmapNBlocks (snd bxps) /\
              BmapStart (fst bxps) = balloc_base1 /\
              BmapStart (snd bxps) = balloc_base2 /\
              IAlloc.Sig.BMPStart ibxp = inode_base + inode_blocks /\
              IXStart ixp = inode_base /\ IXLen ixp = inode_blocks /\
              data_bitmaps <> 0 /\ inode_bitmaps <> 0 /\
              data_bitmaps <= valulen * valulen /\
             inode_bitmaps <= valulen * valulen
           ]]
    POST:hm' RET:ms'  exists m' n frees allocc freeinodes freeinode_pred,
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxps ixp (repeat bfile0 n) (repeat INODE.inode0 n) allocc frees (MSCache ms') * 
                            @IAlloc.rep bfile freepred ibxp freeinodes freeinode_pred) ]]] *
           [[ n = ((IXLen ixp) * INODE.IRecSig.items_per_val)%nat /\ n > 1 ]] *
           [[ forall dl, length dl = n ->
                         Forall freepred dl ->
                         arrayN (@ptsto _ _ _) 0 dl =p=> freeinode_pred ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} init lxp bxps ibxp ixp ms.
  Proof.
    unfold init, rep.

    (* BALLOC.init_nofree *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.

    (* now we need to split the LHS several times to get the correct layout *)
    erewrite arrayN_split at 1; repeat rewrite Nat.add_0_l.
    (* data alloc2 is the last chunk *)
    apply sep_star_assoc.
    omega. omega.
    rewrite skipn_length; omega.

    (* BALLOC.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    erewrite arrayN_split at 1; repeat rewrite Nat.add_0_l.
    erewrite arrayN_split with (i := (BmapNBlocks bxps_1) * valulen) at 1; repeat rewrite Nat.add_0_l.
    (* data region is the first chunk, and data alloc1 is the last chunk *)
    eassign(BmapStart bxps_1); cancel.
    omega.
    rewrite skipn_length.
    rewrite firstn_length_l; omega.
    repeat rewrite firstn_firstn.
    repeat rewrite Nat.min_l; try omega.
    rewrite firstn_length_l; omega.

    (* IAlloc.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    erewrite arrayN_split at 1; repeat rewrite Nat.add_0_l.
    (* inode region is the first chunk, and inode alloc is the second chunk *)
    substl (IAlloc.Sig.BMPStart ibxp).
    eassign (IAlloc.Sig.BMPLen ibxp * valulen / INODE.IRecSig.items_per_val).
    cancel.

    denote (IAlloc.Sig.BMPStart) as Hx; contradict Hx.
    substl (IAlloc.Sig.BMPStart ibxp); intro.
    eapply add_nonzero_exfalso_helper2; eauto.
    rewrite skipn_skipn, firstn_firstn.
    rewrite Nat.min_l, skipn_length by omega.
    rewrite firstn_length_l by omega.
    omega.

    (* Inode.init *)
    prestep. norm. cancel.
    intuition simpl. pred_apply.
    substl (IXStart ixp); cancel.

    rewrite firstn_firstn, firstn_length, skipn_length, firstn_length.
    repeat rewrite Nat.min_l with (n := (BmapStart bxps_1)) by omega.
    rewrite Nat.min_l; omega.
    denote (IXStart ixp) as Hx; contradict Hx.
    substl (IXStart ixp); intro.
    eapply add_nonzero_exfalso_helper2 with (b := 0).
    rewrite Nat.add_0_r; eauto.
    auto.

    (* shuffle_allocs *)
    step.

    (* post condition *)
    prestep; unfold IAlloc.rep; cancel.
    apply file_match_init_ok.

    substl (IXLen ixp).
    apply Rounding.div_lt_mul_lt; auto.
    rewrite Nat.div_small.
    apply Nat.div_str_pos; split.
    apply INODE.IRec.Defs.items_per_val_gt_0.
    rewrite Nat.mul_comm.
    apply Rounding.div_le_mul; try omega.
    cbv; omega.
    unfold INODE.IRecSig.items_per_val.
    rewrite valulen_is.
    compute; omega.

    denote (_ =p=> freepred0) as Hx; apply Hx.
    substl (length dl); substl (IXLen ixp).
    apply Rounding.mul_div; auto.
    apply Nat.mod_divide; auto.
    apply Nat.divide_mul_r.
    unfold INODE.IRecSig.items_per_val.
    apply Nat.mod_divide; auto.
    rewrite valulen_is.
    compute; auto.

    all: auto; cancel.
    Unshelve. eauto.
  Qed.

  Theorem getlen_ok : forall lxp bxps ixp inum ms,
    {< F Fm Fi m0 m f flist ilist allocc frees,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxps ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = length (BFData f) /\ MSAlloc ms = MSAlloc ms' /\ 
              MSCache ms = MSCache ms' /\ MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} getlen lxp ixp inum ms.
  Proof.
    unfold getlen, rep.
    safestep.
    sepauto.

    safestep.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    destruct_lift Hx; eauto.
    simplen.

    cancel.
    eauto.
    Unshelve. all: eauto.
  Qed.

  Theorem getattrs_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist ilist allocc frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist  frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = BFAttr f /\ MSAlloc ms = MSAlloc ms' /\ MSCache ms = MSCache ms' ]]
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

  Definition treeseq_ilist_safe inum ilist1 ilist2 :=
    (forall off bn,
        block_belong_to_file ilist1 bn inum off ->
        block_belong_to_file ilist2 bn inum off) /\
    (forall i def,
        inum <> i -> selN ilist1 i def = selN ilist2 i def).

  Lemma treeseq_ilist_safe_refl : forall inum ilist,
    treeseq_ilist_safe inum ilist ilist.
  Proof.
    unfold treeseq_ilist_safe; intuition.
  Qed.

  Lemma treeseq_ilist_safe_trans : forall inum ilist0 ilist1 ilist2,
    treeseq_ilist_safe inum ilist0 ilist1 ->
    treeseq_ilist_safe inum ilist1 ilist2 ->
    treeseq_ilist_safe inum ilist0 ilist2.
  Proof.
    unfold treeseq_ilist_safe; intuition.
    erewrite H2 by eauto.
    erewrite H3 by eauto.
    eauto.
  Qed.

  Theorem setattrs_ok : forall lxp bxps ixp inum a ms,
    {< F Fm Ff m0 m flist ilist allocc frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxps ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Ff * inum |-> f) ]]] 
    POST:hm' RET:ms'  exists m' flist' f' ilist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxps ixp flist' ilist' frees allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Ff * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) a (BFCache f) ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' /\
              let free := pick_balloc frees (MSAlloc ms') in
              ilist_safe ilist free ilist' free ]] *
           [[ treeseq_ilist_safe inum ilist ilist' ]]
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
    eauto.
    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
    - unfold treeseq_ilist_safe.
      split.
      intros.
      unfold block_belong_to_file in *.
      intuition.
      denote arrayN_ex as Ha. eapply list2nmem_sel in Ha as Ha'.
      rewrite <- Ha'; eauto.
      denote arrayN_ex as Ha. eapply list2nmem_sel in Ha as Ha'.
      rewrite <- Ha'; eauto.

      intuition.
      assert (inum < length ilist) by simplen'.
      denote arrayN_ex as Ha.
      apply arrayN_except_upd in Ha; auto.
      apply list2nmem_array_eq in Ha; subst.
      rewrite selN_updN_ne; auto.
  Qed.

  Theorem updattr_ok : forall lxp bxps ixp inum kv ms,
    {< F Fm Fi m0 m flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxps ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' ilist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxps ixp flist' ilist' frees allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (INODE.iattr_upd (BFAttr f) kv) (BFCache f) ]] *
           [[ MSAlloc ms = MSAlloc ms' /\
              let free := pick_balloc frees (MSAlloc ms') in
              ilist_safe ilist free ilist' free ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} updattr lxp ixp inum kv ms.
  Proof.
    unfold updattr, rep.
    step.
    sepauto.

    safestep.
    repeat extract. seprewrite.
    3: sepauto.
    3: eauto.
    eapply listmatch_updN_selN; try omega.
    unfold file_match; cancel.
    eauto.

    denote (list2nmem m') as Hm'.
    rewrite listmatch_length_pimpl in Hm'; destruct_lift Hm'.
    denote (list2nmem ilist') as Hilist'.
    assert (inum < length ilist) by simplen'.
    apply arrayN_except_upd in Hilist'; eauto.
    apply list2nmem_array_eq in Hilist'; subst.
    unfold ilist_safe; intuition. left.
    destruct (addr_eq_dec inum inum0); subst.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_eq in * by eauto; simpl; eauto.
    - unfold block_belong_to_file in *; intuition.
      all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
  Qed.

  Theorem read_ok : forall lxp bxp ixp inum off ms,
    {< F Fm Fi Fd m0 m flist ilist frees allocc f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = fst vs /\ MSAlloc ms = MSAlloc ms' /\ MSCache ms = MSCache ms' /\
              MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} read lxp ixp inum off ms.
  Proof.
    unfold read, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx.
    safecancel.
    eauto.

    sepauto.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_extract with (i := off) in Hx at 2; try omega.
    destruct_lift Hx; filldef.
    safestep.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 1.
    cancel.
    step.
    cancel; eauto.
    cancel; eauto.
    Unshelve. all: eauto.
  Qed.


  Theorem write_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd m0 m flist ilist frees allocc f vs0,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[ off < length (BFData f) ]] *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs0) ]]]
    POST:hm' RET:ms'  exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist frees allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, nil)) (BFAttr f) (BFCache f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write lxp ixp inum off v ms.
  Proof.
    unfold write, rep.
    prestep; norml.
    extract; seprewrite; subst.
    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx; safecancel.
    eauto.
    sepauto.

    denote (_ (list2nmem m)) as Hx.
    setoid_rewrite listmatch_extract with (i := off) in Hx at 2; try omega.
    destruct_lift Hx; filldef.
    step.

    setoid_rewrite INODE.inode_rep_bn_nonzero_pimpl in H.
    destruct_lift H; denote (_ <> 0) as Hx; subst.
    eapply Hx; eauto; omega.
    erewrite selN_map by omega; filldef.
    setoid_rewrite surjective_pairing at 4.
    cancel.
    safestep.
    5: eauto.
    3: sepauto.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (ix := off) at 15.
    rewrite listmatch_updN_removeN by omega.
    erewrite selN_map by omega; filldef.
    cancel.

    eapply bfcache_upd; eauto.
    sepauto.

    pimpl_crash; cancel; auto.
    Grab Existential Variables.
    all: try exact unit; eauto using tt.
  Qed.

  Lemma grow_treeseq_ilist_safe: forall (ilist: list INODE.inode) ilist' inum a,
    inum < Datatypes.length ilist ->
    (arrayN_ex (ptsto (V:=INODE.inode)) ilist inum
     ✶ inum
       |-> {|
           INODE.IBlocks := INODE.IBlocks (selN ilist inum INODE.inode0) ++ [$ (a)];
           INODE.IAttr := INODE.IAttr (selN ilist inum INODE.inode0) |})%pred (list2nmem ilist') ->
    treeseq_ilist_safe inum ilist ilist'.
  Proof.
    intros.
    unfold treeseq_ilist_safe, block_belong_to_file.
    apply arrayN_except_upd in H0 as Hselupd; auto.
    apply list2nmem_array_eq in Hselupd; subst.
    split. 
    intros.
    split.
    erewrite selN_updN_eq; simpl.
    erewrite app_length.
    omega.
    simplen'.
    intuition.
    erewrite selN_updN_eq; simpl.
    erewrite selN_app; eauto.
    simplen'.
    intros.
    erewrite selN_updN_ne; eauto.
  Qed.


  Theorem grow_ok : forall lxp bxp ixp inum v ms,
    {< F Fm Fi Fd m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAllocC ms) (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms', r) [[ MSAlloc ms = MSAlloc ms' /\ MSCache ms = MSCache ms' ]] * exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
           [[ r = OK tt  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * (length (BFData f)) |-> (v, nil)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ [(v, nil)]) (BFAttr f) (BFCache f) ]] *
           [[ ilist_safe ilist  (pick_balloc frees  (MSAlloc ms'))
                         ilist' (pick_balloc frees' (MSAlloc ms')) ]] *
           [[ treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grow lxp bxp ixp inum v ms.
  Proof.
    unfold grow.
    prestep; norml; unfold stars; simpl.
    denote rep as Hr.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in Hr.
    unfold rep_alt in Hr; destruct_lift Hr.
    extract. seprewrite; subst.
    denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.
    destruct_lift Hx. safecancel.
    sepauto.

    step.

    (* file size ok, do allocation *)
    {
      step.

      safestep.
      sepauto.
      step.

      eapply BALLOCC.bn_valid_facts; eauto.
      step.

      or_r; safecancel.

      rewrite rep_alt_equiv with (msalloc := MSAlloc ms); unfold rep_alt.
      erewrite pick_upd_balloc_lift with (new := freelist') (flag := MSAlloc ms) (p := (frees_1, frees_2)) at 1.
      rewrite pick_negb_upd_balloc with (new := freelist') (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      replace (a3) with (BALLOCC.mk_memstate (BALLOCC.MSLog a3) (BALLOCC.MSCache a3)) at 1 by (destruct a3; reflexivity).
      setoid_rewrite pick_upd_balloc_lift with (new := (BALLOCC.MSCache a3) ) (flag := MSAlloc ms) at 1.
      rewrite pick_negb_upd_balloc with (new := (BALLOCC.MSCache a3)) (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      cancel.

      3: sepauto.
      4: eauto.
      seprewrite.
      rewrite listmatch_updN_removeN by simplen.
      unfold file_match; cancel.
      rewrite map_app; simpl.
      rewrite <- listmatch_app_tail.
      cancel.

      rewrite map_length; omega.
      rewrite wordToNat_natToWord_idempotent'; auto.
      eapply BALLOCC.bn_valid_goodSize; eauto.
      eapply bfcache_upd; eauto.
      eauto.
      apply list2nmem_app; eauto.

      2: eapply grow_treeseq_ilist_safe in H25; eauto.

      2: cancel.
      2: or_l; cancel.

      denote (list2nmem ilist') as Hilist'.
      assert (inum < length ilist) by simplen'.
      apply arrayN_except_upd in Hilist'; eauto.
      apply list2nmem_array_eq in Hilist'; subst.
      unfold ilist_safe; intuition.

      destruct (MSAlloc ms); simpl in *; eapply incl_tran; eauto; eapply incl_remove.

      destruct (addr_eq_dec inum inum0); subst.
      + unfold block_belong_to_file in *; intuition.
        all: erewrite selN_updN_eq in * by eauto; simpl in *; eauto.
        destruct (addr_eq_dec off (length (INODE.IBlocks (selN ilist inum0 INODE.inode0)))).
        * right.
          rewrite selN_last in * by auto.
          subst. rewrite wordToNat_natToWord_idempotent'. eauto.
          eapply BALLOCC.bn_valid_goodSize; eauto.
        * left.
          rewrite app_length in *; simpl in *.
          split. omega.
          subst. rewrite selN_app1 by omega. auto.
      + unfold block_belong_to_file in *; intuition.
        all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
    }

    step.
    cancel; eauto.

    Unshelve. all: easy.
  Qed.

  Local Hint Extern 0 (okToUnify (listmatch _ _ _) (listmatch _ _ _)) => constructor : okToUnify.

  Theorem shrink_ok : forall lxp bxp ixp inum nr ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAllocC ms) (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'  exists m' flist' f' ilist' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (firstn ((length (BFData f)) - nr) (BFData f)) (BFAttr f) (BFCache f) ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAlloc ms = MSAlloc ms' /\
              ilist_safe ilist  (pick_balloc frees  (MSAlloc ms'))
                         ilist' (pick_balloc frees' (MSAlloc ms')) ]] *
           [[ forall inum' def', inum' <> inum -> 
                selN ilist inum' def' = selN ilist' inum' def' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} shrink lxp bxp ixp inum nr ms.
  Proof.
    unfold shrink.
    prestep; norml; unfold stars; simpl.
    denote rep as Hr.
    rewrite rep_alt_equiv with (msalloc := MSAlloc ms) in Hr.
    unfold rep_alt in Hr; destruct_lift Hr.
    cancel.
    sepauto.
    extract; seprewrite; subst; denote removeN as Hx.
    setoid_rewrite listmatch_length_pimpl in Hx at 2.
    rewrite map_length in *.

    {
      step.
      erewrite INODE.rep_bxp_switch in Hx by eassumption.
      rewrite INODE.inode_rep_bn_valid_piff in Hx; destruct_lift Hx.
      denote Forall as Hv; specialize (Hv inum); subst.
      rewrite <- Forall_map.
      apply forall_skipn; apply Hv; eauto.
      erewrite <- listmatch_ptsto_listpred.
      setoid_rewrite listmatch_split at 2.
      rewrite skipn_map_comm; cancel.
      destruct_lift Hx; denote (length (BFData _)) as Heq.

      prestep.
      norm.
      cancel.
      intuition.

      pred_apply.
      erewrite INODE.rep_bxp_switch by eassumption. cancel.
      sepauto.

      denote listmatch as Hx.
      setoid_rewrite listmatch_length_pimpl in Hx at 2.
      prestep; norm. cancel. eassign (ilist'). intuition simpl.
      2: sepauto.

      rewrite rep_alt_equiv with (msalloc := MSAlloc ms); unfold rep_alt.
      pred_apply.
      erewrite pick_upd_balloc_lift with (new := freelist') (flag := negb (MSAlloc ms)) (p := (frees_1, frees_2)) at 1.
      rewrite pick_upd_balloc_negb with (new := freelist') (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      replace (r_0) with (BALLOCC.mk_memstate (BALLOCC.MSLog r_0) (BALLOCC.MSCache r_0)) at 1 by (destruct r_0; reflexivity).
      setoid_rewrite pick_upd_balloc_lift with (new := (BALLOCC.MSCache r_0) ) (flag := negb (MSAlloc ms)) at 1.
      rewrite pick_upd_balloc_negb with (new := (BALLOCC.MSCache r_0)) (flag := MSAlloc ms) at 1.
      unfold upd_balloc.

      erewrite INODE.rep_bxp_switch by ( apply eq_sym; eassumption ).
      cancel.

      seprewrite.
      rewrite listmatch_updN_removeN by omega.
      rewrite firstn_map_comm, Heq.
      unfold file_match, cuttail; cancel; eauto.
      eapply bfcache_upd; eauto.
      3: eauto.

      denote (list2nmem ilist') as Hilist'.
      assert (inum < length ilist) by simplen.
      apply arrayN_except_upd in Hilist'; eauto.
      apply list2nmem_array_eq in Hilist'; subst.
      unfold ilist_safe; intuition.
      destruct (MSAlloc ms); simpl in *; eapply incl_refl.
      left.
      destruct (addr_eq_dec inum inum0); subst.
      + unfold block_belong_to_file in *; intuition simpl.
        all: erewrite selN_updN_eq in * by eauto; simpl in *; eauto.
        rewrite cuttail_length in *. omega.
        rewrite selN_cuttail in *; auto.
      + unfold block_belong_to_file in *; intuition simpl.
        all: erewrite selN_updN_ne in * by eauto; simpl; eauto.
      + eapply list2nmem_array_updN in H20; eauto.
        rewrite H20.
        erewrite selN_updN_ne; eauto.
      + pimpl_crash.
        cancel.
    }

    pimpl_crash; cancel; eauto.

  Unshelve.
    easy. all: try exact bfile0.
  Qed.

  Theorem sync_ok : forall lxp ixp ms,
    {< F ds,
    PRE:hm
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms) hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      LOG.rep lxp F (LOG.NoTxn (ds!!, nil)) (MSLL ms') hm' *
      [[ MSAlloc ms' = negb (MSAlloc ms) ]] *
      [[ MSCache ms' = MSCache ms ]] *
      [[ MSAllocC ms' = MSAllocC ms]]
    XCRASH:hm'
      LOG.recover_any lxp F ds hm'
    >} sync lxp ixp ms.
  Proof.
    unfold sync, rep.
    step.
    step.
  Qed.

  Theorem sync_noop_ok : forall lxp ixp ms,
    {< F ds,
    PRE:hm
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms) hm *
      [[ sync_invariant F ]]
    POST:hm' RET:ms'
      LOG.rep lxp F (LOG.NoTxn ds) (MSLL ms') hm' *
      [[ MSAlloc ms' = negb (MSAlloc ms) ]] *
      [[ MSCache ms' = MSCache ms ]] *
      [[ MSAllocC ms' = MSAllocC ms]]
    XCRASH:hm'
      LOG.recover_any lxp F ds hm'
    >} sync_noop lxp ixp ms.
  Proof.
    unfold sync_noop, rep.
    step.
    step.
  Qed.

  Lemma block_belong_to_file_off_ok : forall Fm Fi bxp ixp flist ilist frees cms mscache inum off f m,
    (Fm * rep bxp ixp flist ilist frees cms mscache)%pred m ->
    (Fi * inum |-> f)%pred (list2nmem flist) ->
    off < Datatypes.length (BFData f) -> 
    block_belong_to_file ilist # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0) inum off.
  Proof.
    unfold block_belong_to_file; intros; split; auto.
    unfold rep, INODE.rep in H; destruct_lift H.
    extract. destruct_lift H.
    setoid_rewrite listmatch_extract with (i := inum) in H at 2.
    unfold file_match in H at 2; destruct_lift H.
    setoid_rewrite listmatch_extract with (i := off) in H at 3.
    destruct_lift H.
    rewrite map_length in *.
    rewrite <- H8. simplen. simplen. simplen.
    Unshelve. eauto.
  Qed.

  Lemma block_belong_to_file_ok : forall Fm Fi Fd bxp ixp flist ilist frees cms mscache inum off f vs m,
    (Fm * rep bxp ixp flist ilist frees cms mscache)%pred m ->
    (Fi * inum |-> f)%pred (list2nmem flist) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    block_belong_to_file ilist # (selN (INODE.IBlocks (selN ilist inum INODE.inode0)) off $0) inum off.
  Proof.
    intros.
    eapply list2nmem_inbound in H1.
    eapply block_belong_to_file_off_ok; eauto.
  Qed.

  Definition diskset_was (ds0 ds : diskset) := ds0 = ds \/ ds0 = (ds!!, nil).

  Theorem d_in_diskset_was : forall d ds ds',
    d_in d ds ->
    diskset_was ds ds' ->
    d_in d ds'.
  Proof.
    intros.
    inversion H0; subst; eauto.
    inversion H; simpl in *; intuition; subst.
    apply latest_in_ds.
  Qed.

  Theorem dwrite_ok : forall lxp bxp ixp inum off v ms,
    {< F Fm Fi Fd ds flist ilist frees allocc f vs,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (MSLL ms) hm *
           [[ off < length (BFData f) ]] *
           [[[ ds!! ::: (Fm  * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: (Fd * off |-> vs) ]]] *
           [[ sync_invariant F ]]
    POST:hm' RET:ms'  exists flist' f' bn ds',
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (MSLL ms') hm' *
           [[ ds' = dsupd ds bn (v, vsmerge vs) ]] *
           [[ block_belong_to_file ilist bn inum off ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           (* spec about files on the latest diskset *)
           [[[ ds'!! ::: (Fm  * rep bxp ixp flist' ilist frees allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * off |-> (v, vsmerge vs)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) off (v, vsmerge vs)) (BFAttr f) (BFCache f) ]]
    XCRASH:hm'
           LOG.recover_any lxp F ds hm' \/
           exists bn, [[ block_belong_to_file ilist bn inum off ]] *
           LOG.recover_any lxp F (dsupd ds bn (v, vsmerge vs)) hm'
    >} dwrite lxp ixp inum off v ms.
  Proof.
    unfold dwrite.
    prestep; norml.
    denote  (list2nmem ds !!) as Hz.
    eapply block_belong_to_file_ok in Hz as Hb; eauto.
    unfold rep in *; destruct_lift Hz.
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
    intuition simpl.
    2: sepauto. 2: sepauto.
    pred_apply; cancel.
    setoid_rewrite <- updN_selN_eq with (l := ilist) (ix := inum) at 4.
    rewrite listmatch_updN_removeN by omega.
    unfold file_match at 3; cancel; eauto.
    setoid_rewrite <- updN_selN_eq with (l := INODE.IBlocks _) (ix := off) at 3.
    erewrite map_updN by omega; filldef.
    rewrite listmatch_updN_removeN by omega.
    cancel.
    eauto.
    eauto.
    cancel.

    repeat xcrash_rewrite.
    xform_norm; xform_normr.
    cancel.

    or_r; cancel.
    xform_norm; cancel.

    cancel.
    xcrash.
    or_l; rewrite LOG.active_intact, LOG.intact_any; auto.

    Unshelve. all: easy.
  Qed.


  Lemma synced_list_map_fst_map : forall (vsl : list valuset),
    synced_list (map fst vsl) = map (fun x => (fst x, nil)) vsl.
  Proof.
    unfold synced_list; induction vsl; simpl; auto.
    f_equal; auto.
  Qed.

  Theorem datasync_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi ds flist ilist free allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn ds ds!!) (MSLL ms) hm *
           [[[ ds!!  ::: (Fm  * rep bxp ixp flist ilist free allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ sync_invariant F ]]
    POST:hm' RET:ms'  exists ds' flist' al,
           LOG.rep lxp F (LOG.ActiveTxn ds' ds'!!) (MSLL ms') hm' *
           [[ ds' = dssync_vecs ds al ]] *
           [[[ ds'!! ::: (Fm * rep bxp ixp flist' ilist free allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> synced_file f) ]]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ length al = length (BFILE.BFData f) /\ forall i, i < length al ->
              BFILE.block_belong_to_file ilist (selN al i 0) inum i ]]
    CRASH:hm' LOG.recover_any lxp F ds hm'
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

    seprewrite; apply eq_sym.
    eapply listmatch_length_r with (m := list2nmem ds!!).
    pred_apply; cancel.
    erewrite selN_map by simplen.
    eapply block_belong_to_file_ok with (m := list2nmem ds!!); eauto.
    eassign (bxp_1, bxp_2); pred_apply; unfold rep, file_match.
    setoid_rewrite listmatch_isolate with (i := inum) at 3.
    repeat erewrite fst_pair by eauto.
    cancel. eauto. simplen. simplen.
    apply list2nmem_ptsto_cancel.
    seprewrite.
    erewrite listmatch_length_r with (m := list2nmem ds!!); eauto.
    auto.

    rewrite LOG.active_intact, LOG.intact_any; auto.
    Unshelve. all: exact ($0, nil).
  Qed.


  Hint Extern 1 ({{_}} Bind (init _ _ _ _ _) _) => apply init_ok : prog.
  Hint Extern 1 ({{_}} Bind (getlen _ _ _ _) _) => apply getlen_ok : prog.
  Hint Extern 1 ({{_}} Bind (getattrs _ _ _ _) _) => apply getattrs_ok : prog.
  Hint Extern 1 ({{_}} Bind (setattrs _ _ _ _ _) _) => apply setattrs_ok : prog.
  Hint Extern 1 ({{_}} Bind (updattr _ _ _ _ _) _) => apply updattr_ok : prog.
  Hint Extern 1 ({{_}} Bind (read _ _ _ _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} Bind (write _ _ _ _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} Bind (dwrite _ _ _ _ _ _) _) => apply dwrite_ok : prog.
  Hint Extern 1 ({{_}} Bind (grow _ _ _ _ _ _) _) => apply grow_ok : prog.
  Hint Extern 1 ({{_}} Bind (shrink _ _ _ _ _ _) _) => apply shrink_ok : prog.
  Hint Extern 1 ({{_}} Bind (datasync _ _ _ _) _) => apply datasync_ok : prog.
  Hint Extern 1 ({{_}} Bind (sync _ _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_}} Bind (sync_noop _ _ _) _) => apply sync_noop_ok : prog.
  Hint Extern 0 (okToUnify (rep _ _ _ _ _ _ _) (rep _ _ _ _ _ _ _)) => constructor : okToUnify.


  Definition read_array lxp ixp inum a i ms :=
    let^ (ms, r) <- read lxp ixp inum (a + i) ms;
    Ret ^(ms, r).

  Definition write_array lxp ixp inum a i v ms :=
    ms <- write lxp ixp inum (a + i) v ms;
    Ret ms.

  Theorem read_array_ok : forall lxp bxp ixp inum a i ms,
    {< F Fm Fi Fd m0 m flist ilist free allocc f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist free allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = fst (selN vsl i ($0, nil)) /\ 
              MSAlloc ms = MSAlloc ms' /\ MSCache ms = MSCache ms' /\
              MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} read_array lxp ixp inum a i ms.
  Proof.
    unfold read_array.
    hoare.

    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    rewrite isolateN_fwd with (i:=i) by auto.
    cancel.
  Unshelve.
    eauto.
    intros; exact emp.
  Qed.


  Theorem write_array_ok : forall lxp bxp ixp inum a i v ms,
    {< F Fm Fi Fd m0 m flist ilist free allocc f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist free allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
           [[ i < length vsl]]
    POST:hm' RET:ms' exists m' flist' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist free allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a (updN vsl i (v, nil)) ]]] *
           [[ f' = mk_bfile (updN (BFData f) (a + i) (v, nil)) (BFAttr f) (BFCache f) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} write_array lxp ixp inum a i v ms.
  Proof.
    unfold write_array.
    prestep. cancel.
    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; try omega.
    rewrite isolateN_fwd with (i:=i) by auto; filldef; cancel.

    step.
    rewrite <- isolateN_bwd_upd by auto; cancel.
  Unshelve.
    eauto.
    intros; exact emp.
  Qed.


  Hint Extern 1 ({{_}} Bind (read_array _ _ _ _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} Bind (write_array _ _ _ _ _ _ _) _) => apply write_array_ok : prog.


  Definition read_range A lxp ixp inum a nr (vfold : A -> valu -> A) v0 ms0 :=
    let^ (ms, r) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi Fd crash m0 m flist ilist frees allocc f vsl ]
    Loopvar [ ms pf ]
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
      [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
      [[ pf = fold_left vfold (firstn i (map fst vsl)) v0 ]] *
      [[ MSAlloc ms = MSAlloc ms0 ]] *
      [[ MSCache ms = MSCache ms0 ]] *
      [[ MSAllocC ms = MSAllocC ms0 ]]
    OnCrash  crash
    Begin
      let^ (ms, v) <- read_array lxp ixp inum a i ms;
      Ret ^(ms, vfold pf v)
    Rof ^(ms0, v0);
    Ret ^(ms, r).


  Theorem read_range_ok : forall A lxp bxp ixp inum a nr (vfold : A -> valu -> A) v0 ms,
    {< F Fm Fi Fd m0 m flist ilist frees allocc f vsl,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd * arrayN (@ptsto _ addr_eq_dec _) a vsl ]]] *
           [[ nr <= length vsl]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = fold_left vfold (firstn nr (map fst vsl)) v0 ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} read_range lxp ixp inum a nr vfold v0 ms.
  Proof.
    unfold read_range.
    safestep. eauto. eauto.
    step.

    assert (m1 < length vsl).
    denote (arrayN _ a vsl) as Hx.
    destruct (list2nmem_arrayN_bound vsl _ Hx); subst; simpl in *; omega.
    safestep.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.

    safestep.
    cancel.
    erewrite <- LOG.rep_hashmap_subset; eauto.
  Unshelve.
    all: eauto; try exact tt; intros; try exact emp.
  Qed.


  (* like read_range, but stops when cond is true *)
  Definition read_cond A lxp ixp inum (vfold : A -> valu -> A)
                       v0 (cond : A -> bool) ms0 :=
    let^ (ms, nr) <- getlen lxp ixp inum ms0;
    let^ (ms, r, ret) <- ForN i < nr
    Hashmap hm
    Ghost [ bxp F Fm Fi m0 m flist f ilist frees allocc ]
    Loopvar [ ms pf ret ]
    Invariant
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
      [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
      [[[ flist ::: (Fi * inum |-> f) ]]] *
      [[ MSAlloc ms = MSAlloc ms0 ]] *
      [[ MSCache ms = MSCache ms0 ]] *
      [[ MSAllocC ms = MSAllocC ms0 ]] *
      [[ ret = None ->
        pf = fold_left vfold (firstn i (map fst (BFData f))) v0 ]] *
      [[ ret = None ->
        cond pf = false ]] *
      [[ forall v, ret = Some v ->
        cond v = true ]]
    OnCrash
      LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm
    Begin
      If (is_some ret) {
        Ret ^(ms, pf, ret)
      } else {
        let^ (ms, v) <- read lxp ixp inum i ms;
        let pf' := vfold pf v in
        If (bool_dec (cond pf') true) {
          Ret ^(ms, pf', Some pf')
        } else {
          Ret ^(ms, pf', None)
        }
      }
    Rof ^(ms, v0, None);
    Ret ^(ms, ret).


  Theorem read_cond_ok : forall A lxp bxp ixp inum (vfold : A -> valu -> A)
                                v0 (cond : A -> bool) ms,
    {< F Fm Fi m0 m flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[ cond v0 = false ]]
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]] *
           ( exists v, 
             [[ r = Some v /\ cond v = true ]] \/
             [[ r = None /\ cond (fold_left vfold (map fst (BFData f)) v0) = false ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} read_cond lxp ixp inum vfold v0 cond ms.
  Proof.
    unfold read_cond.
    prestep. cancel.
    safestep. eauto. msalloc_eq; cancel. eauto. eauto.

    step.
    step.
    step.

    eapply list2nmem_array_pick; eauto.
    step.
    step.
    step.

    rewrite firstn_S_selN_expand with (def := $0) by (rewrite map_length; auto).
    rewrite fold_left_app; simpl.
    erewrite selN_map; subst; auto.
    apply not_true_is_false; auto.

    destruct a2.
    step.
    step.
    or_r; cancel.
    denote cond as Hx; rewrite firstn_oob in Hx; auto.
    rewrite map_length; auto.
    cancel.
  Unshelve.
    all: try easy.
    try exact ($0, nil).
  Qed.


  Hint Extern 1 ({{_}} Bind (read_range _ _ _ _ _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_}} Bind (read_cond _ _ _ _ _ _ _) _) => apply read_cond_ok : prog.

  Definition grown lxp bxp ixp inum l ms0 :=
    let^ (ms, ret) <- ForN i < length l
      Hashmap hm
      Ghost [ F Fm Fi m0 f ilist frees ]
      Loopvar [ ms ret ]
      Invariant
        exists m',
        LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms) hm *
        [[ MSAlloc ms = MSAlloc ms0 ]] *
        [[ MSCache ms = MSCache ms0 ]] *
        ([[ isError ret ]] \/
         exists flist' ilist' frees' f',
         [[ ret = OK tt ]] *
         [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAllocC ms) (MSCache ms)) ]]] *
         [[[ flist' ::: (Fi * inum |-> f') ]]] *
         [[  f' = mk_bfile ((BFData f) ++ synced_list (firstn i l)) (BFAttr f) (BFCache f) ]] *
         [[ ilist_safe ilist  (pick_balloc frees  (MSAlloc ms)) 
                       ilist' (pick_balloc frees' (MSAlloc ms)) ]] *
         [[ treeseq_ilist_safe inum ilist ilist' ]])
      OnCrash
        LOG.intact lxp F m0 hm
      Begin
        match ret with
        | Err e => Ret ^(ms, ret)
        | OK _ =>
          let^ (ms, ok) <- grow lxp bxp ixp inum (selN l i $0) ms;
          Ret ^(ms, ok)
        end
      Rof ^(ms0, OK tt);
    Ret ^(ms, ret).


  Definition truncate lxp bxp xp inum newsz ms :=
    let^ (ms, sz) <- getlen lxp xp inum ms;
    If (lt_dec newsz sz) {
      ms <- shrink lxp bxp xp inum (sz - newsz) ms;
      Ret ^(ms, OK tt)
    } else {
      let^ (ms, ok) <- grown lxp bxp xp inum (repeat $0 (newsz - sz)) ms;
      Ret ^(ms, ok)
    }.


  Definition reset lxp bxp xp inum ms :=
    let^ (ms, sz) <- getlen lxp xp inum ms;
    ms <- shrink lxp bxp xp inum sz ms;
    ms <- setattrs lxp xp inum attr0 ms;
    Ret (mk_memstate (MSAlloc ms) (MSLL ms) (MSAllocC ms) (BFcache.remove inum (MSCache ms))).


  Theorem grown_ok : forall lxp bxp ixp inum l ms,
    {< F Fm Fi Fd m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAllocC ms) (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]] *
           [[[ (BFData f) ::: Fd ]]]
    POST:hm' RET:^(ms', r)
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSCache ms' = MSCache ms ]] *
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
           [[ r = OK tt  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[[ (BFData f') ::: (Fd * arrayN (@ptsto _ addr_eq_dec _) (length (BFData f)) (synced_list l)) ]]] *
           [[ f' = mk_bfile ((BFData f) ++ (synced_list l)) (BFAttr f) (BFCache f) ]] *
           [[ ilist_safe ilist (pick_balloc frees (MSAlloc ms')) 
                      ilist' (pick_balloc frees' (MSAlloc ms'))  ]] *
           [[ treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} grown lxp bxp ixp inum l ms.
  Proof.
    unfold grown; intros.
    safestep.
    unfold synced_list; simpl; rewrite app_nil_r.
    eassign f; destruct f.
    eassign F_; cancel. or_r; cancel. eapply treeseq_ilist_safe_refl.
    eauto. eauto.

    safestep.
    apply list2nmem_arrayN_app; eauto.
    safestep.
    cancel.
    or_r; cancel.
    erewrite firstn_S_selN_expand by omega.
    rewrite synced_list_app, <- app_assoc.
    unfold synced_list at 3; simpl; eauto.
    denote (MSAlloc a = MSAlloc a2) as Heq; rewrite Heq in *.
    eapply ilist_safe_trans; eauto.
    eapply treeseq_ilist_safe_trans; eauto.

    cancel.
    cancel.

    safestep.
    cancel.
    or_r; cancel.
    rewrite firstn_oob; auto.
    apply list2nmem_arrayN_app; auto.
    rewrite firstn_oob; auto.

    cancel.
    Unshelve. all: easy.
  Qed.


  Hint Extern 1 ({{_}} Bind (grown _ _ _ _ _ _) _) => apply grown_ok : prog.

  Theorem truncate_ok : forall lxp bxp ixp inum sz ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAllocC ms) (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms', r)
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSCache ms = MSCache ms' ]] *
           exists m',
           [[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' \/
           [[ r = OK tt  ]] * exists flist' ilist' frees' f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (setlen (BFData f) sz ($0, nil)) (BFAttr f) (BFCache f) ]] *
           [[ ilist_safe ilist (pick_balloc frees (MSAlloc ms')) 
                         ilist' (pick_balloc frees' (MSAlloc ms'))  ]] *
           [[ sz >= Datatypes.length (BFData f) -> treeseq_ilist_safe inum ilist ilist' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} truncate lxp bxp ixp inum sz ms.
  Proof.
    unfold truncate; intros.
    step.
    step.

    - safestep.
      msalloc_eq; cancel.
      eauto.
      step.
      or_r; safecancel.
      rewrite setlen_inbound, Rounding.sub_sub_assoc by omega; auto.
      exfalso; omega.
      cancel.

    - safestep.
      msalloc_eq; cancel.
      eauto.
      apply list2nmem_array.
      step.

      or_r; safecancel.
      rewrite setlen_oob by omega.
      unfold synced_list.
      rewrite repeat_length, combine_repeat; auto.
      cancel.
  Qed.

  Theorem reset_ok : forall lxp bxp ixp inum ms,
    {< F Fm Fi m0 m flist ilist frees f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees (MSAllocC ms) (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms' exists m' flist' ilist' frees',
           LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
           [[[ m' ::: (Fm * rep bxp ixp flist' ilist' frees' (MSAllocC ms') (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> bfile0) ]]] *
           [[ MSAlloc ms = MSAlloc ms' /\ 
              ilist_safe ilist (pick_balloc frees (MSAlloc ms')) 
                         ilist' (pick_balloc frees' (MSAlloc ms'))  ]] *
           [[ forall inum' def', inum' <> inum -> 
                selN ilist inum' def' = selN ilist' inum' def' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} reset lxp bxp ixp inum ms.
  Proof.
    unfold reset; intros.
    step.
    step.
    msalloc_eq; cancel.
    step.
    safestep. 

    destruct (r_).
    destruct (r_0).
    simpl in *.
    subst.
    destruct (MSAllocC1). simpl in *.

    eapply rep_bfcache_remove; eauto.
    simpl.
    rewrite Nat.sub_diag; simpl; auto.
    eapply list2nmem_updN; eauto.
    denote (MSAlloc r_ = MSAlloc r_0) as Heq; rewrite Heq in *.
    eapply ilist_safe_trans; eauto.
    denote treeseq_ilist_safe as Hts.
    unfold treeseq_ilist_safe in Hts.
    intuition.
    assert (inum = inum' -> False).
    intro; eapply H18; eauto.
    denote (forall _ _, _ -> selN ilist' _ _ = selN ilist'0 _ _) as Hx.
    rewrite <- Hx.
    denote (forall _ _, _ -> selN ilist _ _ = selN ilist' _ _) as Hy.
    rewrite Hy.
    all: eauto.
  Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (truncate _ _ _ _ _ _) _) => apply truncate_ok : prog.
  Hint Extern 1 ({{_}} Bind (reset _ _ _ _ _) _) => apply reset_ok : prog.


  Theorem cache_get_ok : forall inum ms,
    {< F Fm Fi m0 m lxp bxp ixp flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:^(ms', r)
           [[ ms' = ms ]] *
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[ r = BFCache f ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} cache_get inum ms.
  Proof.
    unfold cache_get, rep; intros.
    step.
    step.
    destruct ms; reflexivity.
    eapply bfcache_find; eauto.
  Qed.

  Theorem cache_put_ok : forall inum ms c,
    {< F Fm Fi m0 m lxp bxp ixp flist ilist frees allocc f,
    PRE:hm
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           [[[ m ::: (Fm * rep bxp ixp flist ilist frees allocc (MSCache ms)) ]]] *
           [[[ flist ::: (Fi * inum |-> f) ]]]
    POST:hm' RET:ms'
           exists f' flist',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           [[[ m ::: (Fm * rep bxp ixp flist' ilist frees allocc (MSCache ms')) ]]] *
           [[[ flist' ::: (Fi * inum |-> f') ]]] *
           [[ f' = mk_bfile (BFData f) (BFAttr f) (Some c) ]] *
           [[ MSAlloc ms = MSAlloc ms' ]] *
           [[ MSAllocC ms = MSAllocC ms' ]]
    CRASH:hm'  LOG.intact lxp F m0 hm'
    >} cache_put inum c ms.
  Proof.
    unfold cache_put, rep; intros.
    step.
    prestep.
    norm.
    cancel.
    intuition idtac.
    2: eapply list2nmem_updN; eauto.
    2: eauto.
    pred_apply; cancel.
    rewrite <- updN_selN_eq with (l := ilist) at 2.
    eapply listmatch_updN_selN.
    simplen.
    simplen.
    eapply list2nmem_sel in H5; rewrite H5.
    unfold file_match; simpl.
    eassign bfile0.
    eassign INODE.inode0.
    apply pimpl_refl.
    eapply bfcache_put; eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (cache_get _ _) _) => apply cache_get_ok : prog.
  Hint Extern 1 ({{_}} Bind (cache_put _ _ _) _) => apply cache_put_ok : prog.


  (** crash and recovery *)

  Definition FSynced f : Prop :=
     forall n, snd (selN (BFData f) n ($0, nil)) = nil.

  Definition file_crash f f' : Prop :=
    exists vs, possible_crash_list (BFData f) vs /\
    f' = mk_bfile (synced_list vs) (BFAttr f) None.

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
    arrayN (@ptsto _ addr_eq_dec _) 0 (synced_list l) (list2nmem (BFData f)) ->
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
    BFData f = BFData f' /\
    BFAttr f = BFAttr f'.
  Proof.
    unfold FSynced, file_crash; intros.
    destruct H; intuition subst; simpl; eauto.
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

  Lemma xform_rep : forall bxp ixp flist ilist frees allocc mscache,
    crash_xform (rep bxp ixp flist ilist frees allocc mscache) =p=> 
      exists flist', [[ flist_crash flist flist' ]] *
      rep bxp ixp flist' ilist frees allocc (BFcache.empty _).
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOCC.xform_rep, BALLOCC.xform_rep.
    rewrite xform_file_list.
    cancel.

    rewrite locked_eq; unfold cache_rep.
    denote cache_rep as Hc; clear Hc.
    generalize dependent flist. generalize 0.
    induction fs'; simpl in *; intros.
    eapply BFM.mm_init.
    denote flist_crash as Hx; inversion Hx; subst.
    denote! (file_crash _ _) as Hy; inversion Hy; intuition subst.
    simpl.
    eapply pimpl_trans. apply pimpl_refl. 2: eapply IHfs'. cancel.
    eauto.

  Unshelve.
    all: eauto.
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
    eassign (mk_bfile (synced_list l) (BFAttr f) (BFCache f)); cancel.
    eassign (dummy).
    intuition subst; eauto.
  Qed.

  Lemma xform_rep_file : forall F bxp ixp fs f i ilist frees allocc mscache,
    (F * i |-> f)%pred (list2nmem fs) ->
    crash_xform (rep bxp ixp fs ilist frees allocc mscache) =p=> 
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' ilist frees allocc (BFcache.empty _) *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' i * i |-> f')%pred (list2nmem fs') ]].
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite INODE.xform_rep, BALLOCC.xform_rep, BALLOCC.xform_rep.
    rewrite xform_file_list.
    cancel.
    erewrite list2nmem_sel with (x := f) by eauto.
    apply forall2_selN; eauto.
    eapply list2nmem_inbound; eauto.

    rewrite locked_eq; unfold cache_rep.
    denote cache_rep as Hc; clear Hc.
    denote list2nmem as Hc; clear Hc.
    generalize dependent fs. generalize 0.
    induction fs'; simpl in *; intros.
    eapply BFM.mm_init.
    denote! (flist_crash _ _) as Hx; inversion Hx; subst.
    denote! (file_crash _ _) as Hy; inversion Hy; intuition subst.
    simpl.
    eapply pimpl_trans. apply pimpl_refl. 2: eapply IHfs'. cancel.
    eauto.

    apply list2nmem_ptsto_cancel.
    erewrite <- flist_crash_length; eauto.
    eapply list2nmem_inbound; eauto.
    Unshelve. all: eauto.
  Qed.

 Lemma xform_rep_file_pred : forall (F Fd : pred) bxp ixp fs f i ilist frees allocc mscache,
    (F * i |-> f)%pred (list2nmem fs) ->
    (Fd (list2nmem (BFData f))) ->
    crash_xform (rep bxp ixp fs ilist frees allocc mscache) =p=>
      exists fs' f',  [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' ilist frees allocc (BFcache.empty _) *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' i * i |-> f')%pred (list2nmem fs') ]] *
      [[ (crash_xform Fd)%pred (list2nmem (BFData f')) ]].
  Proof.
    intros.
    rewrite xform_rep_file by eauto.
    cancel. eauto.
    unfold file_crash in *.
    repeat deex; simpl.
    eapply list2nmem_crash_xform; eauto.
  Qed.

  Lemma xform_rep_off : forall Fm Fd bxp ixp ino off f fs vs ilist frees allocc mscache,
    (Fm * ino |-> f)%pred (list2nmem fs) ->
    (Fd * off |-> vs)%pred (list2nmem (BFData f)) ->
    crash_xform (rep bxp ixp fs ilist frees allocc mscache) =p=> 
      exists fs' f' v, [[ flist_crash fs fs' ]] * [[ file_crash f f' ]] *
      rep bxp ixp fs' ilist frees allocc (BFcache.empty _) * [[ In v (vsmerge vs) ]] *
      [[ (arrayN_ex (@ptsto _ addr_eq_dec _) fs' ino * ino |-> f')%pred (list2nmem fs') ]] *
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

Ltac msalloc_eq := BFILE.msalloc_eq.
