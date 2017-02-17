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

  Definition empty_cache : Dcache_type := Dcache.empty _.

  Definition lookup lxp ixp dnum name ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None => Ret ^(ms, None)
    | Some cache =>
      match Dcache.find name cache with
      | None =>
        let^ (ms, r) <- SDIR.lookup lxp ixp dnum name ms;
        ms <- BFILE.cache_put dnum (Dcache.add name r cache) ms;
        Ret ^(ms, r)
      | Some r =>
        Ret ^(ms, r)
      end
    end.

  Definition unlink lxp ixp dnum name ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None => Ret ^(ms, OK tt)
    | Some cache =>
      let^ (ms, r) <- SDIR.unlink lxp ixp dnum name ms;
      ms <- BFILE.cache_put dnum (Dcache.add name None cache) ms;
      Ret ^(ms, r)
    end.

  Definition link lxp bxp ixp dnum name inum isdir ms :=
    let^ (ms, ocache) <- BFILE.cache_get dnum ms;
    match ocache with
    | None => Ret ^(ms, OK tt)
    | Some cache =>
      let^ (ms, r) <- SDIR.link lxp bxp ixp dnum name inum isdir ms;
      match r with
      | Err _ =>
        Ret ^(ms, r)
      | OK _ =>
        ms <- BFILE.cache_put dnum (Dcache.add name (Some (inum, isdir)) cache) ms;
        Ret ^(ms, r)
      end
    end.

  Definition readdir lxp ixp dnum ms :=
    let^ (ms, r) <- SDIR.readdir lxp ixp dnum ms;
    Ret ^(ms, r).


  Definition rep f (dsmap : @mem string string_dec (addr * bool)) : Prop :=
    SDIR.rep f dsmap /\
    exists cache, BFILE.BFCache f = Some cache /\
    forall name v,
    Dcache.MapsTo name v cache -> dsmap name = v.

  Definition rep_macro Fi Fm m bxp ixp (inum : addr) dsmap ilist frees ms : @pred _ addr_eq_dec valuset :=
    (exists flist f,
     [[[ m ::: Fm * BFILE.rep bxp ixp flist ilist frees (BFILE.MSCache ms) ]]] *
     [[[ flist ::: Fi * inum |-> f ]]] *
     [[ rep f dsmap ]] )%pred.

  Local Hint Unfold rep rep_macro SDIR.rep_macro : hoare_unfold.

  Hint Resolve Dcache.find_2.


  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.
  Notation MSCache := BFILE.MSCache.

  Theorem lookup_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms
    POST:hm' RET:^(ms', r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms' *
           [[ MSAlloc ms' = MSAlloc ms ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]])
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} lookup lxp ixp dnum name ms.
  Proof.
    unfold lookup.

    (* Odd issue: [eauto] takes forever as part of [prestep].. *)
    intros.
    destruct_branch.

    step.
    step.

    denote! (SDIR.rep _ _) as Hx; clear Hx.
    destruct o; [ or_r | or_l ]; cancel.
    apply any_sep_star_ptsto. eauto.
    unfold notindomain. eauto.

    ProgMonad.monad_simpl_one.
    eapply pimpl_ok2; [ eauto with prog | ].
    intros. unfold rep_macro, rep, SDIR.rep_macro in *. norm.
    cancel.

    intuition.
    pred_apply; cancel.
    pred_apply; cancel.
    eauto.
    step.

    (* Prove that the new cache is valid *)
    destruct (string_dec name0 name); subst.
    {
      eapply DcacheDefs.mapsto_add in H0.
      unfold notindomain in *; congruence.
    }
    {
      eapply Dcache.add_3 in H0; eauto.
    }

    destruct (string_dec name0 name); subst.
    {
      eapply DcacheDefs.mapsto_add in H0.
      eapply ptsto_valid' in H8.
      congruence.
    }
    {
      eapply Dcache.add_3 in H0; eauto.
    }

  Unshelve.
    all: eauto.
  Qed.

  Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms
    POST:hm' RET:^(ms', r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm' *
             [[ listpred SDIR.readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSCache ms' = MSCache ms ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') hm'
    >} readdir lxp ixp dnum ms.
  Proof.
    unfold readdir.
    intros.

    ProgMonad.monad_simpl_one.
    eapply pimpl_ok2; [ eauto with prog | ].
    intros. unfold rep_macro, rep, SDIR.rep_macro. norm.
    cancel.

    intuition.
    pred_apply; cancel.
    pred_apply; cancel.
    eauto.
    step.
  Qed.

  Theorem unlink_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms
    POST:hm' RET:^(ms', r) exists m' dmap',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees ms' *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]]
    CRASH:hm' LOG.intact lxp F m0 hm'
    >} unlink lxp ixp dnum name ms.
  Proof.
    unfold unlink.
    intros.

    ProgMonad.monad_simpl_one.
    eapply pimpl_ok2; [ eauto with prog | ].
    intros. unfold rep_macro, rep, SDIR.rep_macro. norm.
    cancel.

    intuition.
    pred_apply; cancel.
    pred_apply; cancel.
    eauto.

    step.

    unfold mem_except. destruct (string_dec name name0); subst.
    denote! (Dcache.MapsTo _ _ _) as Hx; apply DcacheDefs.mapsto_add in Hx; subst.
    destruct (string_dec name0 name0); congruence.
    destruct (string_dec name0 name); try congruence.
    denote! (Dcache.MapsTo _ _ _) as Hx; apply Dcache.add_3 in Hx. eauto. congruence.

  Unshelve.
    all: try exact ""%string.
    all: try exact (Dcache.empty _).
  Qed.

  Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms *
             [[ goodSize addrlen inum ]]
    POST:hm' RET:^(ms', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
           (([[ isError r ]] *
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap ilist frees ms')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' ms' *
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
    unfold rep in *.
    or_r; norm. cancel.
    intuition eauto.

    denote! (Dcache.MapsTo _ _ _) as Hx.
    destruct (string_dec name name0); subst; [ rewrite upd_eq by auto | rewrite upd_ne by auto ].
    apply DcacheDefs.mapsto_add in Hx; congruence.
    apply Dcache.add_3 in Hx; auto; congruence.

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

  Hint Extern 0 (okToUnify (rep ?f _ _ _) (rep ?f _ _ _)) => constructor : okToUnify.

End CacheOneDir.
