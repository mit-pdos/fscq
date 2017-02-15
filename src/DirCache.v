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


Module CDIR.

  Module dcache_key_as_OT <: UsualOrderedType.
    Definition t := (addr * string)%type.
    Definition eq := @eq t.
    Definition eq_refl := @eq_refl t.
    Definition eq_sym := @eq_sym t.
    Definition eq_trans := @eq_trans t.
    Definition lt (x y : t) :=
      match x with
      | (xa, xs) =>
        match y with
        | (ya, ys) => lt xa ya \/ (xa = ya /\ (String_as_OT.string_compare xs ys = Lt))
        end
      end.

    Lemma lt_trans: forall x y z : t, lt x y -> lt y z -> lt x z.
    Proof.
      unfold lt; destruct x, y, z; intuition.
      subst.
      right; intuition.
      eapply String_as_OT.lt_trans; eauto.
    Qed.

    Lemma lt_not_eq : forall x y : t, lt x y -> ~ eq x y.
    Proof.
      unfold lt, eq; destruct x, y; intuition.
      inversion H0; subst; omega.
      inversion H0; subst.
      eapply String_as_OT.lt_not_eq; eauto.
      reflexivity.
    Qed.

    Definition compare x y : Compare lt eq x y.
      destruct (Nat_as_OT.compare (fst x) (fst y)); [ apply LT | | apply GT ].
      2: destruct (String_as_OT.compare (snd x) (snd y)); [ apply LT | apply EQ | apply GT ].

      all: unfold lt, eq, Nat_as_OT.lt, Nat_as_OT.eq, String_as_OT.lt, String_as_OT.eq in *.
      all: destruct x, y; simpl in *.
      all: intuition.
      congruence.
    Defined.

    Definition eq_dec (a b : t) : {a = b} + {a <> b}.
      destruct (addr_eq_dec (fst a) (fst b)).
      destruct (string_dec (snd a) (snd b)).

      all: destruct a, b; simpl in *.
      left. congruence.
      right. congruence.
      right. congruence.
    Defined.

  End dcache_key_as_OT.

  Module Dcache := FMapAVL.Make(dcache_key_as_OT).
  Module DcacheDefs := MapDefs dcache_key_as_OT Dcache.
  Definition Dcache_type := Dcache.t (option (addr * bool)).


  Definition memstate := (BFILE.memstate * Dcache_type)%type.

  Definition init_cache ms : prog memstate :=
    Ret (ms, Dcache.empty _).

  Definition lookup lxp ixp dnum name (ms : memstate) :=
    match Dcache.find (dnum, name) (snd ms) with
    | None =>
      let^ (fms, r) <- SDIR.lookup lxp ixp dnum name (fst ms);
      Ret ^((fms, Dcache.add (dnum, name) r (snd ms)), r)
    | Some r =>
      Ret ^(ms, r)
    end.

  Definition unlink lxp ixp dnum name (ms : memstate) :=
    let^ (fms, r) <- SDIR.unlink lxp ixp dnum name (fst ms);
    Ret ^((fms, Dcache.add (dnum, name) None (snd ms)), r).

  Definition link lxp bxp ixp dnum name inum isdir ms :=
    let^ (fms, r) <- SDIR.link lxp bxp ixp dnum name inum isdir (fst ms);
    match r with
    | Err _ => Ret ^((fms, snd ms), r)
    | OK _ => Ret ^((fms, Dcache.add (dnum, name) (Some (inum, isdir)) (snd ms)), r)
    end.

  Definition readdir lxp ixp dnum (ms : memstate) :=
    let^ (fms, r) <- SDIR.readdir lxp ixp dnum (fst ms);
    Ret ^((fms, snd ms), r).


  Definition rep f (dsmap : @mem string string_dec (addr * bool)) (dnum : addr) (ms : memstate) : Prop :=
    SDIR.rep f dsmap /\
    forall name v,
    Dcache.MapsTo (dnum, name) v (snd ms) -> dsmap name = v.

  Definition rep_macro Fi Fm m bxp ixp (inum : addr) dsmap ilist frees ms : @pred _ addr_eq_dec valuset :=
    (exists flist f,
     [[[ m ::: Fm * BFILE.rep bxp ixp flist ilist frees ]]] *
     [[[ flist ::: Fi * inum |-> f ]]] *
     [[ rep f dsmap inum ms ]] )%pred.

  Local Hint Unfold rep rep_macro SDIR.rep_macro : hoare_unfold.

  Hint Resolve Dcache.find_2.


  Theorem lookup_ok : forall lxp bxp ixp dnum name ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL (fst ms)) hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms
    POST:hm' RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL (fst ms')) hm' *
           [[ BFILE.MSAlloc (fst ms') = BFILE.MSAlloc (fst ms) ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]])
    CRASH:hm'  exists ms,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms) hm'
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

  Unshelve.
    all: eauto.
  Qed.

  Theorem readdir_ok : forall lxp bxp ixp dnum ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL (fst ms)) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms
    POST:hm' RET:^(ms', r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL (fst ms')) hm' *
             [[ listpred SDIR.readmatch r dmap ]] *
             [[ BFILE.MSAlloc (fst ms') = BFILE.MSAlloc (fst ms) ]]
    CRASH:hm'  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL ms') hm'
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
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL (fst ms)) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms
    POST:hm' RET:^(ms', r) exists m' dmap',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL (fst ms')) hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees ms' *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ BFILE.MSAlloc (fst ms') = BFILE.MSAlloc (fst ms) ]]
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
    all: try exact (0, ""%string).
    all: try exact (Dcache.empty _).
  Qed.

  Theorem link_ok : forall lxp bxp ixp dnum name inum isdir ms,
    {< F Fm Fi m0 m dmap ilist frees,
    PRE:hm   LOG.rep lxp F (LOG.ActiveTxn m0 m) (BFILE.MSLL (fst ms)) hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees ms *
             [[ goodSize addrlen inum ]]
    POST:hm' RET:^(ms', r) exists m',
             [[ BFILE.MSAlloc (fst ms') = BFILE.MSAlloc (fst ms) ]] *
           (([[ isError r ]] *
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL (fst ms')) hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (BFILE.MSLL (fst ms')) hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' ms' *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (BFILE.MSAlloc (fst ms')))
                                 ilist' (BFILE.pick_balloc frees' (BFILE.MSAlloc (fst ms'))) ]] *
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
    all: try exact (0, ""%string).
  Qed.


  Hint Extern 1 ({{_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
  Hint Extern 1 ({{_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
  Hint Extern 1 ({{_}} Bind (link _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
  Hint Extern 1 ({{_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.

  Hint Extern 0 (okToUnify (rep ?f _ _ _) (rep ?f _ _ _)) => constructor : okToUnify.


End CDIR.
