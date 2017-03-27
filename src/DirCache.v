Require Import Mem.
Require Import Word.
Require Import Ascii.
Require Import String.
Require Import Dir.
Require Import Omega.
Require Import Prog.
Require Import BasicProg.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import Log.
Require Import BFile.
Require Import GenSepN.
Require Import ListPred.
Require Import MemMatch.
Require Import FunctionalExtensionality.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import Errno.
Require Import DirName.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import StringUtils.
Require Import MapUtils.
Require List.

Set Implicit Arguments.


Module CacheOneDir.

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.
  Notation MSCache := BFILE.MSCache.
  Notation MSAllocC := BFILE.MSAllocC.

  Definition empty_cache : Dcache_type := Dcache.empty _.

  Fixpoint fill_cache (files: (list (string * (addr * bool)))) ocache : Dcache_type  :=
    match files with
    | nil => ocache
    | f::files' => fill_cache files' (Dcache.add (fst f) (Some (snd f)) ocache)
    end.

  Definition init_cache lxp ixp dnum ms :=
    let^ (ms, files) <- SDIR.readdir lxp ixp dnum ms;
    let ocache := fill_cache files (Dcache.empty _) in
    ms <- BFILE.cache_put dnum (ocache, 0) ms;
    Ret ^(ms, (ocache, 0)).

  Definition get_dcache' (lxp:FSLayout.log_xparams) (ixp:Inode.INODE.IRecSig.xparams) dnum ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None =>
      ms <- BFILE.cache_put dnum (Dcache.empty _, 0) ms;
      Ret ^(ms, (Dcache.empty _, 0))
    | Some r =>
      Ret ^(ms, r)
    end.

  Definition get_dcache lxp ixp dnum ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None =>
      let^ (ms, r0) <- init_cache lxp ixp dnum ms;
      Ret ^(ms, r0)
    | Some r =>
      Ret ^(ms, r)
    end.

  Definition lookup lxp ixp dnum name ms :=
    let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
    match Dcache.find name (fst cache) with
    | None =>
      Ret ^(ms, None)
    | Some r =>
      Ret ^(ms, r)
    end.

   Definition lookup' lxp ixp dnum name ms :=
     let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
     match Dcache.find name (fst cache) with
     | None =>
       AlertModified;;
       let^ (ms, r) <- SDIR.lookup lxp ixp dnum name ms;
       ms <- BFILE.cache_put dnum (Dcache.add name r (fst cache), (snd cache)) ms;
       Ret ^(ms, r)
     | Some r =>
       Ret ^(ms, r)
     end.


  Definition unlink lxp ixp dnum name ms :=
    let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
    let^ (ms, ix, r) <- SDIR.unlink lxp ixp dnum name ms;
    ms <- BFILE.cache_put dnum (Dcache.add name None (fst cache), ix) ms;
    Ret ^(ms, r).

  Definition link lxp bxp ixp dnum name inum isdir ms :=
    let^ (ms, lookup_res) <- lookup lxp ixp dnum name ms;
    match lookup_res with
    | Some _ =>
      Ret ^(ms, Err EEXIST)
    | None =>
      let^ (ms, cache) <- get_dcache lxp ixp dnum ms;
      let^ (ms, ix, r) <- SDIR.link lxp bxp ixp dnum name inum isdir (snd cache) ms;
      match r with
      | Err _ =>
        Ret ^(ms, r)
      | OK _ =>
        ms <- BFILE.cache_put dnum (Dcache.add name (Some (inum, isdir)) (fst cache), ix) ms;
        Ret ^(ms, r)
      end
    end.

  Definition readdir lxp ixp dnum ms :=
    let^ (ms, r) <- SDIR.readdir lxp ixp dnum ms;
    Ret ^(ms, r).


  Definition rep f (dsmap : @mem string string_dec (addr * bool)) : Prop :=
    SDIR.rep f dsmap /\
    exists cache, (BFILE.BFCache f = Some cache \/ BFILE.BFCache f = None /\ cache = (Dcache.empty _, 0)) /\
    forall name v,
    Dcache.MapsTo name v (fst cache) -> dsmap name = v.

  Definition rep_macro Fi Fm m bxp ixp (inum : addr) dsmap ilist frees f ms : @pred _ addr_eq_dec valuset :=
    (exists flist,
     [[[ m ::: Fm * BFILE.rep bxp ixp flist ilist frees (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) ]]] *
     [[[ flist ::: Fi * inum |-> f ]]] *
     [[ rep f dsmap ]] )%pred.

  Local Hint Unfold rep rep_macro SDIR.rep_macro : hoare_unfold.

  Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 -> rep f m2 -> m1 = m2.
  Proof.
    unfold rep; intuition.
    eapply SDIR.rep_mem_eq; eauto.
  Qed.

  Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.
  Proof.
    unfold rep; intuition.
    apply SDIR.bfile0_empty.
    eexists. intuition.
    apply DcacheDefs.MapProperties.F.empty_mapsto_iff in H.
    exfalso; eauto.
  Qed.

  Theorem crash_rep : forall f f' m,
    BFILE.file_crash f f' ->
    rep f m ->
    rep f' m.
  Proof.
    unfold rep; intuition.
    eapply SDIR.crash_rep; eauto.
    inversion H; intuition subst; simpl.
    eexists; intuition.
    apply DcacheDefs.MapProperties.F.empty_mapsto_iff in H0.
    exfalso; eauto.
  Qed.

  Hint Resolve Dcache.find_2.

  Lemma readmatch_neq: forall F a b m,
    (F * SDIR.readmatch a * SDIR.readmatch b)%pred m ->
    fst a <> fst b.
  Proof.
    unfold_sep_star.
    unfold SDIR.readmatch, ptsto.
    destruct a, b; cbn.
    intros. repeat deex.
    apply mem_disjoint_union in H.
    contradiction H.
    eauto.
  Qed.

  Lemma fill_cache_add_comm : forall entries a cache F,
    F * listpred SDIR.readmatch (a :: entries) =p=>
    F * listpred SDIR.readmatch (a :: entries) *
    [[ Dcache.Equal (fill_cache (a :: entries) cache)
      (Dcache.add (fst a) (Some (snd a)) (fill_cache entries cache)) ]].
  Proof.
    unfold Dcache.Equal; simpl.
    induction entries; intros; simpl.
    cancel.
    do 2 intro; pred_apply; cancel.
    enough (fst a <> fst a0).
    all : repeat match goal with
    | _ => reflexivity
    | [ H: _ |- _ ] => rewrite H; clear H
    | [ |- context [Dcache.find ?k1 (Dcache.add ?k2 _ _)] ] =>
      progress (rewrite ?DcacheDefs.MapFacts.add_eq_o,
                       ?DcacheDefs.MapFacts.add_neq_o by auto)
      || destruct (string_dec k1 k2); subst
    | [ |- context [Dcache.find _ (fill_cache _ (Dcache.add (fst ?a) _ _))] ] =>
      eapply pimpl_trans in H as ?; [ | | apply (IHentries a)]; try cancel; destruct_lifts
    end.
    eapply readmatch_neq with (m := m).
    pred_apply; cancel.
  Qed.

  Lemma fill_cache_correct: forall entries name v dmap,
    Dcache.MapsTo name v (fill_cache entries (Dcache.empty _)) ->
    listpred SDIR.readmatch entries dmap ->
    dmap name = v.
  Proof.
    induction entries; cbn; intros.
    rewrite DcacheDefs.MapFacts.empty_mapsto_iff in *.
    intuition.
    eapply pimpl_trans in H0; [ | | apply fill_cache_add_comm with (F := emp)]; try cancel.
    destruct_lifts.
    rewrite H3 in H.
    revert H0.
    unfold_sep_star. unfold SDIR.readmatch at 1, ptsto.
    intros. repeat deex.
    destruct (string_dec name a_1); subst.
    apply DcacheDefs.mapsto_add in H; subst.
    apply mem_union_addr; auto.
    apply Dcache.add_3 in H; eauto.
    rewrite mem_union_sel_r; auto.
  Qed.

  Theorem init_cache_ok : forall bxp lxp ixp dnum ms,
    {< F Fm Fi m0 m dmap ilist frees f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms
    POST:hm' RET:^(ms', cache)
           exists f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f' ms' *
           [[ BFILE.BFCache f' = Some cache ]] *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]]
    CRASH:hm'
           LOG.intact lxp F m0 hm'
    >} init_cache lxp ixp dnum ms.
  Proof.
    unfold init_cache, rep_macro.
    step.
    step.
    step.
    msalloc_eq. cancel.
    eexists. split.
    left. reflexivity.
    eauto using fill_cache_correct.
    step.
    step.
    msalloc_eq. cancel.
    eexists. split.
    left. reflexivity.
    eauto using fill_cache_correct.
  Qed.

  Hint Extern 1 ({{_}} Bind (init_cache _ _ _ _) _) => apply init_cache_ok : prog.

  Theorem get_dcache_ok : forall lxp ixp dnum ms,
    {< F Fm Fi m0 m dmap ilist frees bxp f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms
    POST:hm' RET:^(ms', cache)
           exists f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f' ms' *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
           [[ BFILE.BFCache f' = Some cache ]]
    CRASH:hm'
           LOG.intact lxp F m0 hm'
    >} get_dcache lxp ixp dnum ms.
  Proof.
    unfold get_dcache, rep_macro.
    step.
    step.
    step.
    step.
    Unshelve. all: eauto.
  Qed.

  Hint Extern 1 ({{_}} Bind (get_dcache _ _) _) => apply get_dcache_ok : prog.

  Ltac subst_cache :=
    repeat match goal with
    | [ H : Some _ = Some _ |- _ ] => inversion H; clear H; subst
    | [ H1 : BFILE.BFCache ?f = _ , H2 : BFILE.BFCache ?F = _ |- _ ] => rewrite H1 in H2
    end.

  Theorem lookup_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 m dmap ilist frees f,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms
    POST:hm' RET:^(ms', r)
           exists f',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f' ms' *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]]) *
           [[ True ]]
    CRASH:hm'
           LOG.intact lxp F m0 hm'
    >} lookup lxp ixp dnum name ms.
  Proof.
    unfold lookup.

    step.
    step.

    repeat ( denote! (SDIR.rep _ _) as Hx; clear Hx ).
    destruct o; [ or_r | or_l ]; cancel.
    apply any_sep_star_ptsto. subst_cache; eauto.
    unfold notindomain. subst_cache; eauto.

    step.
    step.
    destruct (r_); subst; simpl in *. cancel.

    eexists; intuition eauto.

    (* Prove that the new cache is valid *)
    destruct (string_dec name0 name); subst.
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      unfold notindomain in *; congruence.
    }
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

    step.
    destruct (r_); subst; simpl in *. cancel.

    eexists; intuition eauto.
    destruct (string_dec name0 name); subst.
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      denote! (_ dmap) as Hd.
      eapply ptsto_valid' in Hd.
      congruence.
    }
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

    step.

    repeat ( denote! (SDIR.rep _ _) as Hx; clear Hx ).
    destruct o; [ or_r | or_l ]; cancel.
    apply any_sep_star_ptsto. subst_cache; eauto.
    unfold notindomain. subst_cache; eauto.

    step.
    step.
    destruct (r_); subst; simpl in *. cancel.
    eexists; intuition eauto.
    destruct (string_dec name0 name); subst.
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      subst_cache; eauto.
    }
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

    step.
    destruct (r_); subst; simpl in *. cancel.

    eexists; intuition eauto.
    destruct (string_dec name0 name); subst.
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      denote! (_ dmap) as Hd.
      eapply ptsto_valid' in Hd.
      congruence.
    }
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

  Unshelve.
    all: try exact unit.
    all: eauto.
    all: intros.
    all: try exact tt.
    all: try exact (Dcache.empty unit).
  Qed.

  Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fm Fi m0 m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms
    POST:hm' RET:^(ms', r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
             [[ listpred SDIR.readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSCache ms' = MSCache ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ True ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} readdir lxp ixp dnum ms.
  Proof.
    unfold readdir.
    hoare.
  Qed.

  Theorem unlink_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms
    POST:hm' RET:^(ms', r) exists m' dmap' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees f' ms' *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ True ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} unlink lxp ixp dnum name ms.
  Proof.
    unfold unlink.
    hoare.

    destruct (r_); simpl in *. subst. cancel.

    unfold mem_except.
    eexists; intuition eauto.


    destruct (string_dec name0 name); subst.
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      subst_cache; eauto.
    }
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

    destruct (r_); simpl in *. subst. cancel.

    unfold mem_except.
    eexists; intuition eauto.
    destruct (string_dec name0 name); subst.
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      subst_cache; eauto.
    }
    {
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

  Unshelve.
    all: try exact ""%string.
    all: try exact (Dcache.empty _).
    all: try exact empty_mem.
  Qed.

  Lemma sdir_rep_cache : forall f c m,
    SDIR.rep f m ->
    SDIR.rep {| BFILE.BFData := BFILE.BFData f; BFILE.BFAttr := BFILE.BFAttr f; BFILE.BFCache := c |} m.
  Proof.
    unfold SDIR.rep, DIR.rep, DIR.Dent.rep, DIR.Dent.items_valid, DIR.Dent.RA.RALen; eauto.
  Qed.

  Hint Resolve sdir_rep_cache.

  Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fm Fi m0 m dmap ilist frees f,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms *
             [[ goodSize addrlen inum ]]
    POST:hm' RET:^(ms', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
           (([[ isError r ]] *
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} link lxp bxp ixp dnum name inum isdir ms.
  Proof.
    unfold link.
    step.
    step.
    step.
    step.

    destruct (r_); simpl in *. subst. cancel.

    or_r; cancel.
    eauto.

    eexists; intuition eauto.
    destruct (string_dec name0 name); subst.
    {
      try rewrite upd_eq by eauto.
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      subst_cache; eauto.
    }
    {
      try rewrite upd_ne by eauto.
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

    step.
    step.
    step.

    destruct (r_); simpl in *. subst. cancel.

    or_r; cancel.
    eauto.

    eexists; intuition eauto.
    destruct (string_dec name0 name); subst.
    {
      try rewrite upd_eq by eauto.
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply DcacheDefs.mapsto_add in Hm.
      subst_cache; eauto.
    }
    {
      try rewrite upd_ne by eauto.
      denote! (Dcache.MapsTo _ _ _) as Hm.
      eapply Dcache.add_3 in Hm; subst_cache; eauto.
    }

  Unshelve.
    all: try exact unit.
    all: eauto.
    all: try exact (Dcache.empty _).
    all: try exact tt.
  Qed.


  Hint Extern 1 ({{_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
  Hint Extern 1 ({{_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
  Hint Extern 1 ({{_}} Bind (link _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
  Hint Extern 1 ({{_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.

End CacheOneDir.
