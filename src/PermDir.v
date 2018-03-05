Require Import Mem.
Require Import List.
Require Import Word.
Require Import Rec.
Require Import Pred.
Require Import Omega.
Require Import Rec.
Require Import ListPred.
Require Import Bool.
Require Import ListUtils.
Require Import Errno.
Require Import DestructVarname.

Require Export PermFileRecArray.

Import ListNotations.

Set Implicit Arguments.



Module DIR.

  Definition filename_len := (1024 - addrlen - addrlen).
  Definition filename := word filename_len.


  Module DentSig <: FileRASig.

    Definition itemtype : Rec.type := Rec.RecF
        ([("name",  Rec.WordF filename_len);
          ("inum",  Rec.WordF addrlen);
          ("valid", Rec.WordF 1);
          ("isdir", Rec.WordF 1);
          ("unused", Rec.WordF (addrlen - 2))
         ]).

    Definition items_per_val := valulen / (Rec.len itemtype).

    Theorem blocksz_ok : valulen = Rec.len (Rec.ArrayF itemtype items_per_val).
    Proof.
      unfold items_per_val; simpl.
      rewrite valulen_is.
      compute; auto.
    Qed.

  End DentSig.

  Module Dent := FileRecArray DentSig.


  (*************  dirent accessors  *)

  Definition dent := Dent.Defs.item.
  Definition dent0 := Dent.Defs.item0.

  Fact resolve_selN_dent0 : forall l i d,
    d = dent0 -> selN l i d = selN l i dent0.
  Proof.
    intros; subst; auto.
  Qed.

  Hint Rewrite resolve_selN_dent0 using reflexivity : defaults.


  Definition bit2bool bit := if (bit_dec bit) then false else true.
  Definition bool2bit bool : word 1 := if (bool_dec bool true) then $1 else $0.

  Definition DEIsDir (de : dent) := Eval compute_rec in de :-> "isdir".
  Definition DEValid (de : dent) := Eval compute_rec in de :-> "valid".
  Definition DEName  (de : dent) := Eval compute_rec in de :-> "name".
  Definition DEInum  (de : dent) := Eval compute_rec in # (de :-> "inum").
  Definition mk_dent (name : filename) inum isdir : dent := Eval cbn in
      dent0 :=> "valid" := $1 :=>
                "name" := name :=>
                "inum" := $ inum :=>
                "isdir" := bool2bit isdir.

  Definition is_dir   (de : dent) := bit2bool (DEIsDir de).
  Definition is_valid (de : dent) := bit2bool (DEValid de).
  Definition name_is  (n : filename) (de : dent) :=
      if (weq n (DEName de)) then true else false.


  (*************  rep invariant  *)

  Definition dmatch (de: dent) : @pred filename (@weq filename_len) (addr * bool) :=
    if bool_dec (is_valid de) false then emp
    else (DEName de) |-> (DEInum de, is_dir de) * [[ DEInum de <> 0 ]].

  Definition rep f dmap :=
    exists delist,
    (Dent.rep f (repeat Public (length (Dent.Defs.ipack delist))) delist)%pred (list2nmem (BFILE.BFData f)) /\
    listpred dmatch delist dmap.

  Definition rep_macro Fm Fi m bxp ixp inum dmap ilist frees f ms sm : (@pred _ addr_eq_dec valuset) :=
    (exists flist,
    [[ INODE.IOwner (selN ilist inum INODE.inode0) = Public ]] *
    [[[ m ::: Fm * BFILE.rep bxp sm ixp flist ilist frees (BFILE.MSAllocC ms) (BFILE.MSCache ms) (BFILE.MSICache ms) (BFILE.MSDBlocks ms) ]]] *
    [[[ flist ::: Fi * inum |-> f ]]] *
    [[ rep f dmap ]])%pred.

  (*************  program  *)


  Definition lookup_f name de (_ : addr) := (is_valid de) && (name_is name de).

  Definition ifind_lookup_f lxp ixp dnum name ms :=
    Dent.ifind lxp ixp dnum (lookup_f name) ms.

  Definition ifind_invalid lxp ixp dnum ms :=
    Dent.ifind lxp ixp dnum (fun de _ => negb (is_valid de)) ms.

  Definition lookup lxp ixp dnum name ms :=
    let^ (ms, r) <- ifind_lookup_f lxp ixp dnum name ms;;
    match r with
    | None => Ret ^(ms, None)
    | Some (_, de) => Ret ^(ms, Some (DEInum de, is_dir de))
    end.

  Definition readent := (filename * (addr * bool))%type.

  Definition readdir lxp ixp dnum ms :=
    let^ (ms, dents) <- Dent.readall lxp ixp dnum ms;;
    let r := map (fun de => (DEName de, (DEInum de, is_dir de))) (filter is_valid dents) in
    Ret ^(ms, r).

  Definition unlink lxp ixp dnum name ms :=
    let^ (ms, r) <- ifind_lookup_f lxp ixp dnum name ms;;
    match r with
    | None => Ret ^(ms, 0, Err ENOENT)
    | Some (ix, _) =>
        ms <- Dent.put lxp ixp dnum ix Public dent0 ms;;
        Ret ^(ms, ix, OK tt)
    end.

  Definition link' lxp bxp ixp dnum name inum isdir ms :=
    let de := mk_dent name inum isdir in
    let^ (ms, r) <- ifind_invalid lxp ixp dnum ms;;
    match r with
    | Some (ix, _) =>
        ms <- Dent.put lxp ixp dnum ix Public de ms;;
        Ret ^(ms, ix+1, OK tt)
    | None =>
        let^ (ms, ok) <- Dent.extend lxp bxp ixp dnum Public de ms;;
        Ret ^(ms, 0, ok)
    end.

  (* link without hint *)
  Definition link'' lxp bxp ixp dnum name inum isdir (ix0:addr) ms :=
    let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;;
    Ret ^(ms, ix, r0).

  (* link with hint *)
  Definition link lxp bxp ixp dnum name inum isdir ix0 ms :=
    let de := mk_dent name inum isdir in
    let^ (ms, len) <- BFILE.getlen lxp ixp dnum ms;;
    If (lt_dec ix0 (len * Dent.RA.items_per_val)) {
      let^ (ms, res) <- Dent.get lxp ixp dnum ix0 ms;;
      match (is_valid res) with
      | true =>
        let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;;
        Ret ^(ms, ix, r0)
      | false => 
        ms <- Dent.put lxp ixp dnum ix0 Public de ms;;
        Ret ^(ms, ix0+1, OK tt)
      end
    } else {
(* calling extend here slows down performance drastically.
        let^ (ms, ok) <- Dent.extend lxp bxp ixp dnum de ms;
        Ret ^(ms, ix0+1, ok)  *)
      let^ (ms, ix, r0) <- link' lxp bxp ixp dnum name inum isdir ms;;
      Ret ^(ms, ix, r0) 
    }.

  (*************  basic lemmas  *)


  Fact bit2bool_0 : bit2bool $0 = false.
  Proof.
    unfold bit2bool; destruct (bit_dec $0); auto.
    contradict e; apply natToWord_discriminate; auto.
  Qed.

  Fact bit2bool_1 : bit2bool $1 = true.
  Proof.
    unfold bit2bool; destruct (bit_dec $1); auto.
    apply eq_sym in e; contradict e.
    apply natToWord_discriminate; auto.
  Qed.

  Fact bit2bool_1_ne : bit2bool $1 <> false.
  Proof. rewrite bit2bool_1; congruence. Qed.

  Fact bit2bool_0_ne : bit2bool $0 <> true.
  Proof. rewrite bit2bool_0; congruence. Qed.

  Local Hint Resolve bit2bool_0 bit2bool_1 bit2bool_0_ne bit2bool_1_ne.

  Lemma bit2bool2bit : forall b, bit2bool (bool2bit b) = b.
  Proof.
    destruct b; cbn; auto.
  Qed.

  Lemma bool2bit2bool : forall b,  bool2bit (bit2bool b) = b.
  Proof.
    unfold bit2bool; intros.
    destruct (bit_dec b); subst; auto.
  Qed.

  Lemma lookup_f_ok: forall name de a,
    lookup_f name de a = true ->
    is_valid de = true /\ DEName de = name.
  Proof.
    unfold lookup_f, name_is; intuition.
    apply andb_true_iff in H; tauto.
    destruct (weq name (DEName de)); auto.
    contradict H.
    rewrite andb_true_iff; easy.
  Qed.

  Lemma lookup_f_nf: forall name de a,
    lookup_f name de a = false ->
    is_valid de = false \/ DEName de <> name.
  Proof.
    unfold lookup_f, name_is; intuition.
    apply andb_false_iff in H; intuition.
    destruct (weq name (DEName de)); intuition.
  Qed.

  Lemma lookup_notindomain': forall l ix name,
    Forall (fun e => (lookup_f name e ix) = false) l
    -> listpred dmatch l =p=> notindomain name.
  Proof.
    induction l; unfold pimpl; simpl; intros.
    apply emp_notindomain; auto.
    inversion H; subst.

    destruct (Sumbool.sumbool_of_bool (is_valid a)).
    destruct (lookup_f_nf name a ix); try congruence.
    eapply notindomain_mem_except; eauto.
    eapply ptsto_mem_except.
    pred_apply; unfold dmatch at 1.
    rewrite e, IHl by eauto; simpl; cancel.

    pred_apply; rewrite IHl by eauto; cancel.
    unfold dmatch; rewrite e; simpl; auto.
  Qed.

  Lemma lookup_notindomain: forall l name,
    (forall i, i < length l -> lookup_f name (selN l i dent0) i = false) ->
    listpred dmatch l =p=> notindomain name.
  Proof.
    intros.
    eapply lookup_notindomain' with (ix := 0).
    eapply selN_Forall; eauto.
  Qed.



  Definition dmatch_ex name (de: dent) : @pred filename (@weq filename_len) (addr * bool) :=
    if (name_is name de) then emp
    else dmatch de.

  Definition dmatch_ex_same : forall de,
    dmatch_ex (DEName de) de = emp.
  Proof.
    unfold dmatch_ex, name_is; intros.
    destruct (weq (DEName de) (DEName de)); congruence.
  Qed.

  Definition dmatch_ex_diff : forall name de,
    name <> (DEName de) ->
    dmatch_ex name de = dmatch de.
  Proof.
    unfold dmatch_ex, name_is; intros.
    destruct (weq name (DEName de)); congruence.
  Qed.

  Lemma dmatch_ex_ptsto : forall l name v,
    (name |-> v * listpred dmatch l) 
    =p=> (name |-> v * listpred (dmatch_ex name) l).
  Proof.
    induction l; simpl; intros; auto.
    unfold dmatch_ex at 1, dmatch at 1, dmatch at 2, name_is.
    destruct (bool_dec (is_valid a) false).
    destruct (weq name (DEName a));
    rewrite sep_star_comm, sep_star_assoc;
    setoid_rewrite sep_star_comm at 2; rewrite IHl; cancel.

    destruct (weq name (DEName a)); subst.
    unfold pimpl; intros; exfalso.
    eapply ptsto_conflict_F with (m := m) (a := DEName a).
    pred_apply; cancel.
    eapply pimpl_trans with (b := (name |-> v * listpred dmatch l * [[DEInum a <> 0 ]] * _)%pred).
    cancel. rewrite IHl. cancel.
  Qed.

  Lemma lookup_ptsto: forall l name ix,
    ix < length l ->
    lookup_f name (selN l ix dent0) ix = true ->
    listpred dmatch l =p=> listpred (dmatch_ex name) l *
       (name |-> (DEInum (selN l ix dent0), is_dir (selN l ix dent0))).
  Proof.
    induction l; intros.
    simpl; inversion H.
    pose proof (lookup_f_ok _ _ _ H0) as [Hx Hy].
    destruct ix; subst; simpl in *.
    unfold dmatch at 1; rewrite Hx, dmatch_ex_same; simpl.
    eapply pimpl_trans with (b := (DEName a |-> _ * listpred dmatch l * _)%pred).
    cancel. rewrite dmatch_ex_ptsto; cancel.

    assert (ix < length l) by omega.
    rewrite IHl; eauto; try solve [ cancel ].
    unfold dmatch_ex at 2, dmatch, name_is.
    destruct (bool_dec (is_valid _) false);
    destruct (weq (DEName _) _); try solve [ cancel ].
    rewrite e; repeat destruct_prod.
    unfold pimpl; intros; exfalso.
    eapply ptsto_conflict_F with (m := m) (a := DEName (w, (w0, (w1, (w2, (w3, u)))))).
    pred_apply; cancel.
  Qed.


  Definition readmatch (de: readent) : @pred _ (@weq filename_len) _ :=
    fst de |-> snd de.

  Lemma readmatch_ok : forall l,
    listpred dmatch l =p=> listpred readmatch
      (map (fun de => (DEName de, (DEInum de, is_dir de))) (filter is_valid l)).
  Proof.
    induction l; simpl; auto.
    unfold dmatch at 1; destruct (is_valid a); simpl.
    rewrite IHl; cancel.
    cancel.
  Qed.


  Lemma dmatch_dent0_emp :  dmatch dent0 = emp.
  Proof.
    unfold dmatch, dent0.
    destruct (bool_dec (is_valid _) false); auto.
    contradict n.
    compute; auto.
  Qed.

  Lemma listpred_dmatch_dent0_emp : forall l i dmap,
    listpred dmatch l dmap ->
    is_valid (selN l i dent0) = true ->
    i < length l ->
    listpred dmatch (updN l i dent0) (mem_except dmap (DEName (selN l i dent0))).
  Proof.
    intros.
    apply listpred_updN; auto.
    rewrite dmatch_dent0_emp.
    eapply ptsto_mem_except; pred_apply.
    rewrite listpred_isolate by eauto.
    unfold dmatch at 2; rewrite H0; simpl.
    repeat cancel.
  Qed.


  Lemma dmatch_mk_dent : forall name inum isdir,
    goodSize addrlen inum ->
    dmatch (mk_dent name inum isdir) = (name |-> (inum, isdir) * [[ inum <> 0 ]])%pred.
  Proof.
    unfold dmatch, mk_dent, is_valid, is_dir; intros; cbn.
    rewrite bit2bool_1, wordToNat_natToWord_idempotent', bit2bool2bit; auto.
  Qed.

  Lemma listpred_dmatch_mem_upd : forall l i dmap name inum isdir,
    notindomain name dmap ->
    negb (is_valid (selN l i dent0)) = true ->
    listpred dmatch l dmap ->
    i < length l -> inum <> 0 ->
    goodSize addrlen inum ->
    listpred dmatch (updN l i (mk_dent name inum isdir)) (Mem.upd dmap name (inum, isdir)).
  Proof.
    intros.
    apply listpred_updN; auto.
    rewrite dmatch_mk_dent by auto.
    eapply pimpl_apply. cancel.
    apply ptsto_upd_disjoint.
    apply negb_true_iff in H0.
    pred_apply.
    setoid_rewrite listpred_isolate with (def := dent0) at 1; eauto.
    unfold dmatch at 2; rewrite H0; cancel.
    eauto.
  Qed.

  Lemma listpred_dmatch_repeat_dent0 : forall n,
    listpred dmatch (repeat dent0 n) <=p=> emp.
  Proof.
    induction n; intros; simpl; eauto.
    split; rewrite dmatch_dent0_emp, IHn; cancel.
  Qed.

  Lemma listpred_dmatch_ext_mem_upd : forall l dmap name inum isdir,
    notindomain name dmap ->
    (forall i, i < length l -> negb (is_valid (selN l i dent0)) = false) ->
    listpred dmatch l dmap ->
    goodSize addrlen inum -> inum <> 0 ->
    listpred dmatch (l ++ @updN (Rec.data Dent.RA.itemtype) (Dent.Defs.block0) 0 (mk_dent name inum isdir))
                    (Mem.upd dmap name (inum, isdir)).
  Proof.
    intros.
    pose proof (Dent.Defs.items_per_val_gt_0).
    erewrite <- Nat.sub_diag, <- updN_app2, Dent.Defs.block0_repeat by auto.
    apply listpred_updN; auto.
    rewrite app_length, repeat_length; omega.

    replace (length l) with (length l + 0) by omega.
    rewrite removeN_app_r, removeN_repeat, listpred_app by auto.
    rewrite listpred_dmatch_repeat_dent0.
    rewrite dmatch_mk_dent by auto.
    eapply pimpl_apply. cancel.
    apply ptsto_upd_disjoint; auto.
  Qed.

  Lemma listpred_dmatch_eq_mem : forall l m m',
    listpred dmatch l m -> listpred dmatch l m' ->
    m = m'.
  Proof.
    induction l; cbn; intros m m' H H'.
    - apply emp_empty_mem_only in H.
      apply emp_empty_mem_only in H'.
      congruence.
    - unfold dmatch at 1 in H.
      unfold dmatch at 1 in H'.
      destruct bool_dec.
      apply IHl; pred_apply; cancel.
      eapply pimpl_trans in H; [| cancel..].
      eapply pimpl_trans in H'; [| cancel..].
      revert H. revert H'.
      unfold_sep_star.
      intros. repeat deex.
      match goal with H1 : (ptsto _ _ ?m), H2 : (ptsto _ _ ?m') |- _ =>
        assert (m = m') by (eapply ptsto_complete; eauto); subst
      end.
      f_equal.
      eauto.
  Qed.

  Lemma listpred_dmatch_notindomain: forall delist dmap name x,
    notindomain name dmap ->
    listpred dmatch delist (upd dmap name x) ->
    listpred dmatch delist =p=> notindomain name * name |-> x.
  Proof.
    intros. intros m ?.
    replace m with (upd dmap name x) in * by (eauto using listpred_dmatch_eq_mem).
    apply ptsto_upd_disjoint; auto.
  Qed.

  Lemma dmatch_no_0_inum: forall f m, dmatch f m ->
    forall name isdir, m name = Some (0, isdir) -> False.
  Proof.
    unfold dmatch.
    intros; destruct bool_dec; destruct_lifts.
    congruence.
    unfold ptsto in *. intuition.
    destruct (weq name (DEName f)); subst.
    congruence.
    denote (m name = Some _) as Hm.
    denote (m _ = None) as Ha.
    rewrite Ha in Hm by auto.
    congruence.
  Unshelve.
    all: auto; repeat constructor.
  Qed.

  Lemma listpred_dmatch_no_0_inum: forall dmap m,
    listpred dmatch dmap m ->
    forall name isdir, m name = Some (0, isdir) -> False.
  Proof.
    induction dmap; cbn; intros.
    congruence.
    revert H.
    unfold_sep_star.
    intros. repeat deex.
    unfold mem_union in *.
    destruct (m1 name) eqn:?.
    denote (Some _ = Some _) as Hs; inversion Hs; subst; clear Hs.
    eauto using dmatch_no_0_inum.
    eauto.
  Unshelve.
    all: eauto.
  Qed.

  (*************  correctness theorems  *)

  Notation MSLL := BFILE.MSLL.
  Notation MSAlloc := BFILE.MSAlloc.
  Notation MSCache := BFILE.MSCache.
  Notation MSAllocC := BFILE.MSAllocC.
  Notation MSIAllocC := BFILE.MSIAllocC.

  Theorem lookup_ok :
    forall lxp bxp ixp dnum name ms pr,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PERM:pr   
    PRE:bm, hm,
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:bm', hm', RET:^(ms',r)
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm bm' hm' *
           rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
           [[ MSAlloc ms' = MSAlloc ms ]] *
           [[ MSAllocC ms' = MSAllocC ms ]] *
         ( [[ r = None /\ notindomain name dmap ]] \/
           exists inum isdir Fd,
           [[ r = Some (inum, isdir) /\ inum <> 0 /\
                   (Fd * name |-> (inum, isdir))%pred dmap ]])
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm bm' hm'
    >} lookup lxp ixp dnum name ms.
  Proof. 
    unfold lookup, ifind_lookup_f, rep_macro, rep.
    safestep.
    unfold Dent.RA.RAData; eauto.
    
    safestep.
    safestep.
    erewrite LOG.rep_hashmap_subset; eauto; cancel.
    or_r; cancel.
    eapply listpred_dmatch_no_0_inum; eauto.
    eapply ptsto_valid'.
    denote DEInum as Hd.
    erewrite selN_inb in Hd by auto.
    rewrite <- Hd.
    eapply lookup_ptsto; eauto.
    eapply lookup_ptsto; eauto.
    eexists; intuition eauto.
    cancel.

    step.
    erewrite LOG.rep_hashmap_subset; eauto; cancel.
    or_l; cancel.
    apply lookup_notindomain; auto.
    cancel.
  Qed.


  Theorem readdir_ok :
    forall lxp bxp ixp dnum ms pr,
    {< F Fm Fi m0 sm m dmap ilist frees f,
    PERM:pr   
    PRE:bm, hm,
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:bm', hm', RET:^(ms',r)
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm bm' hm' *
             rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms' sm *
             [[ listpred readmatch r dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSCache ms' = MSCache ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]]
    CRASH:bm', hm',  exists ms',
           LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms') sm bm' hm'
    >} readdir lxp ixp dnum ms.
  Proof. 
    unfold readdir, rep_macro, rep.
    safestep.
    unfold Dent.RA.RAData; eauto.
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    apply readmatch_ok.
  Qed.

  Local Hint Resolve mem_except_notindomain.

  Theorem unlink_ok :
    forall lxp bxp ixp dnum name ms pr,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PERM:pr   
    PRE:bm, hm,
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm
    POST:bm', hm', RET:^(ms', hint, r) exists m' dmap',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm bm' hm' *
             exists f', rep_macro Fm Fi m' bxp ixp dnum dmap' ilist frees f' ms' sm *
             [[ dmap' = mem_except dmap name ]] *
             [[ notindomain name dmap' ]] *
             [[ r = OK tt -> indomain name dmap ]] *
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSAllocC ms' = MSAllocC ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]]
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} unlink lxp ixp dnum name ms.
  Proof. 
    unfold unlink, ifind_lookup_f, rep_macro, rep.
    prestep.
    intros m Hm.
    destruct_lift Hm.
    cleanup.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    eauto.
    eauto.
    unfold Dent.RA.RAData; eauto.
    
    prestep.
    intros mx Hmx.
    destruct_lift Hmx.
    cleanup.
    repeat eexists.
    pred_apply; norm.
    congruence.
    congruence.
    cancel.
    denote (Some _ = Some _) as Hx;
    inversion Hx; subst; clear Hx.
    intuition.
    eauto.
    apply Dent.Defs.item0_wellformed.
    msalloc_eq.
    eauto.
    eauto.
    unfold Dent.RA.RAData; eauto.

    denote (lookup_f) as HH.
    pose proof (lookup_f_ok _ _ _ HH) as [Hx Hy].
    auto.

    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto.
    unfold Dent.RA.RAData in *; eauto.
    eexists; split; eauto.
    subst.
    pred_apply.
    rewrite repeat_updN_noop.
    replace (length (Dent.Defs.ipack x))
      with (length (Dent.Defs.ipack (updN x a0_1 dent0))); eauto.
    repeat rewrite Dent.Defs.ipack_length.
    rewrite length_updN; auto.
    denote lookup_f as Hx;
    apply lookup_f_ok in Hx; cleanup.
    apply listpred_dmatch_dent0_emp; auto.

    rewrite lookup_ptsto by eauto.
    unfold pimpl; intros.
    eapply sep_star_ptsto_indomain.
    pred_apply; cancel.
    rewrite <- H2; cancel; eauto.

    norm.
    cancel.
    intuition.

    step.
    simpl.
    erewrite LOG.rep_hashmap_subset; eauto.
    rewrite <- notindomain_mem_eq; auto.
    eapply lookup_notindomain; eauto.
    eapply lookup_notindomain; eauto.
    cancel.
    congruence.
    congruence.
    rewrite <- H2; cancel; eauto.
    
    Unshelve.
    exact nat.
    all: try eauto.
  Qed.

  Theorem link'_ok :
    forall lxp bxp ixp dnum name inum isdir ms pr,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PERM:pr   
    PRE:bm, hm,
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:bm', hm', RET:^(ms', ixhint', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm bm' hm')
        \/  ([[ r = OK tt ]] *
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm bm' hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} link' lxp bxp ixp dnum name inum isdir ms.
  Proof.
    unfold link', ifind_lookup_f, ifind_invalid, rep_macro, rep.
    prestep.
    intros m Hm.
    destruct_lift Hm.
    cleanup.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    eauto.
    eauto.
    unfold Dent.RA.RAData; eauto.

    prestep.
    intros mx Hmx.
    destruct_lift Hmx.
    cleanup.
    repeat eexists.
    pred_apply; norm.
    congruence.
    congruence.
    cancel.
    cleanup.
    msalloc_eq.
    intuition.    
    eauto.
    cbv; tauto.
    eauto.
    eauto.
    unfold Dent.RA.RAData; eauto.
    auto.
    
    step.
    step; msalloc_eq.
    erewrite LOG.rep_hashmap_subset; eauto; or_r; cancel.
    auto.
    eexists; split; eauto.
    unfold Dent.RA.RAData in *; eauto.
    subst.
    pred_apply.
    rewrite repeat_updN_noop.
    replace (length (Dent.Defs.ipack x))
      with (length (Dent.Defs.ipack (updN x a0_1 dent0))); eauto.
    repeat rewrite Dent.Defs.ipack_length.
    rewrite length_updN; auto.
    erewrite <- length_updN; eauto.
    repeat rewrite Dent.Defs.ipack_length.
    setoid_rewrite length_updN; eauto.

    apply listpred_dmatch_mem_upd; auto.
    eapply ptsto_upd_disjoint; eauto.
    apply BFILE.ilist_safe_refl.
    apply BFILE.treeseq_ilist_safe_refl.

    rewrite <- H2; cancel; eauto.

    intros mx Hmx.
    destruct_lift Hmx.
    cleanup.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    cbv; tauto.
    msalloc_eq.
    pred_apply; cancel.
    eauto.
    unfold Dent.RA.RAData; eauto.
    auto.
    
    step.
    step.
    erewrite LOG.rep_hashmap_subset; eauto; or_l; cancel.

    step.
    intros mz Hmz; pose proof Hmz as Htemp; pred_apply.
    erewrite LOG.rep_hashmap_subset; eauto; or_r; cancel.

    apply listmatch_emp; intros; cancel.
    rewrite BFILE.rep_length_pimpl in *.
    destruct_lift H5.
    destruct_lift H28.
    apply list2nmem_ptsto_bound in H36.

    rewrite listmatch_isolate with (i:=dnum) in Htemp; try omega.
    destruct_lift Htemp; eauto.
    rewrite <- H41; eauto.
    
    eexists; split; eauto.
    unfold Dent.RA.RAData in *; eauto.
    subst.
    pred_apply.
    rewrite <- repeat_app_tail.
    
    replace ((S (length (Dent.Defs.ipack x))))
      with (length (Dent.Defs.ipack (x ++ (updN Dent.Defs.block0 0 (mk_dent name inum isdir))))); eauto.
    repeat rewrite Dent.Defs.ipack_length.
    rewrite app_length, length_updN; auto.
    setoid_rewrite Dent.Defs.block0_repeat.
    rewrite repeat_length.
    replace Dent.RA.items_per_val with (Dent.RA.items_per_val * 1) at 1 by omega.
    rewrite Rounding.divup_add; auto.
    apply Nat.add_1_r.
    apply Dent.Defs.items_per_val_not_0.
    eapply listpred_dmatch_ext_mem_upd; eauto.
    eapply ptsto_upd_disjoint; eauto.

    all: try solve[rewrite <- H2; cancel; eauto].
    congruence.
    congruence.

  Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (link' _ _ _ _ _ _ _ _) _) => apply link'_ok : prog.

  Theorem link_ok :
    forall lxp bxp ixp dnum name inum isdir ixhint ms pr,
    {< F Fm Fi m0 sm m dmap ilist frees,
    PERM:pr   
    PRE:bm, hm,
             LOG.rep lxp F (LOG.ActiveTxn m0 m) (MSLL ms) sm bm hm *
             exists f, rep_macro Fm Fi m bxp ixp dnum dmap ilist frees f ms sm *
             [[ notindomain name dmap ]] *
             [[ goodSize addrlen inum ]] *
             [[ inum <> 0 ]]
    POST:bm', hm', RET:^(ms', ixhint', r) exists m',
             [[ MSAlloc ms' = MSAlloc ms ]] *
             [[ MSIAllocC ms' = MSIAllocC ms ]] *
           (([[ isError r ]] * LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm bm' hm')
        \/  ([[ r = OK tt ]] * 
             exists dmap' Fd ilist' frees' f',
             LOG.rep lxp F (LOG.ActiveTxn m0 m') (MSLL ms') sm bm' hm' *
             rep_macro Fm Fi m' bxp ixp dnum dmap' ilist' frees' f' ms' sm *
             [[ dmap' = Mem.upd dmap name (inum, isdir) ]] *
             [[ (Fd * name |-> (inum, isdir))%pred dmap' ]] *
             [[ (Fd dmap /\ notindomain name dmap) ]] *
             [[ BFILE.ilist_safe ilist  (BFILE.pick_balloc frees  (MSAlloc ms'))
                                 ilist' (BFILE.pick_balloc frees' (MSAlloc ms')) ]] *
             [[ BFILE.treeseq_ilist_safe dnum ilist ilist' ]] ))
    CRASH:bm', hm', LOG.intact lxp F m0 sm bm' hm'
    >} link lxp bxp ixp dnum name inum isdir ixhint ms.
  Proof.
    unfold link, rep_macro, rep.
    prestep.
    intros m Hm.
    destruct_lift Hm.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    eauto.
    eauto.
    
    step; msalloc_eq.

    (* case 1: try entry hint *)
    prestep.
    intros mx Hmx.
    destruct_lift Hmx.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    erewrite Dent.items_length_ok with (xp := dummy9) (m := (list2nmem (BFILE.BFData dummy9))).
    unfold Dent.RA.RALen. auto.
    pred_apply; cancel.
    eauto.
    eauto.
    eauto.
    destruct is_valid eqn:?.
    (* working around a 'not found' Coq bug, probably #4202 in simpl *)
    prestep. unfold rep_macro, rep.
    intros my Hmy.
    destruct_lift Hmy.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    eauto.
    msalloc_eq.
    eauto.
    eauto.
    eexists; split; eauto.
    erewrite <- notindomain_mem_eq; eauto.


    step.
    step; msalloc_eq.
    erewrite LOG.rep_hashmap_subset; eauto; or_l; cancel.

    step.
    erewrite LOG.rep_hashmap_subset; eauto; or_r; cancel.
    auto.
    eexists; split; eauto.
    rewrite <- upd_mem_except; auto.
    eapply ptsto_upd_disjoint; auto.
    rewrite <- H2; cancel; eauto.

    prestep.
    intros my Hmy.
    destruct_lift Hmy.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    erewrite Dent.items_length_ok with (xp := dummy9) (m := (list2nmem (BFILE.BFData dummy9))).
    unfold Dent.RA.RALen. auto.
    pred_apply; cancel.
    cbv; intuition.
    msalloc_eq; eauto.
    eauto.
    eauto.
    eauto.

    step.
    step; msalloc_eq.
    erewrite LOG.rep_hashmap_subset; eauto; or_r; cancel.
    eauto.
    eexists; split; eauto.

    unfold Dent.RA.RAData in *; eauto.
    subst.
    pred_apply.
    rewrite repeat_updN_noop.
    replace (length (Dent.Defs.ipack delist))
      with (length (Dent.Defs.ipack (updN delist ixhint (mk_dent name inum isdir)))); eauto.
    repeat rewrite Dent.Defs.ipack_length.
    rewrite length_updN; auto.

    apply listpred_dmatch_mem_upd; auto.
    rewrite Bool.negb_true_iff; auto.
    erewrite Dent.items_length_ok with (xp := dummy9) (m := (list2nmem (BFILE.BFData dummy9))).
    unfold Dent.RA.RALen. auto.
    pred_apply; cancel.
    eapply ptsto_upd_disjoint; auto.
    apply BFILE.ilist_safe_refl.
    apply BFILE.treeseq_ilist_safe_refl.

    all: try solve [rewrite <- H2; cancel; eauto].

    prestep. unfold rep_macro, rep.
    intros my Hmy.
    destruct_lift Hmy.
    repeat eexists.
    pred_apply; norm.
    cancel.
    intuition.
    eauto.
    eauto.
    eauto.
    eexists; split; eauto.
    erewrite <- notindomain_mem_eq; eauto.

    step.
    step; msalloc_eq.
    simpl.
    erewrite LOG.rep_hashmap_subset; eauto; or_l; cancel.

    step.
    erewrite LOG.rep_hashmap_subset; eauto; or_r; cancel.
    eauto.
    eexists; split; eauto.
    rewrite <- upd_mem_except; auto.
    eapply ptsto_upd_disjoint; auto.

    rewrite <- H2; cancel; eauto.
 
  Unshelve.
    all: eauto.
  Qed.


  Hint Extern 1 ({{_|_}} Bind (lookup _ _ _ _ _) _) => apply lookup_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (unlink _ _ _ _ _) _) => apply unlink_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (link _ _ _ _ _ _ _ _ _) _) => apply link_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (readdir _ _ _ _) _) => apply readdir_ok : prog.

  Hint Extern 0 (okToUnify (rep ?f _) (rep ?f _)) => constructor : okToUnify.


  (*************  Lemma for callers *)

  Theorem dmatch_complete : forall de m1 m2, dmatch de m1 -> dmatch de m2 -> m1 = m2.
  Proof.
    unfold dmatch, is_dir; intros.
    destruct (bool_dec (is_valid de) false).
    apply emp_complete; eauto.
    eapply ptsto_complete; pred_apply; cancel.
  Qed.

  Lemma listpred_dmatch_eq : forall l m1 m2,
    listpred dmatch l m1
    -> listpred dmatch l m2
    -> m1 = m2.
  Proof.
    induction l; simpl; auto.
    apply emp_complete; auto.
    intros m1 m2.
    unfold_sep_star; intuition.
    repeat deex; f_equal.
    eapply dmatch_complete; eauto.
    eapply IHl; eauto.
  Qed.

  Lemma rep_mem_eq : forall f m1 m2,
    rep f m1 ->
    rep f m2 ->
    m1 = m2.
  Proof.
    unfold rep; intros.
    repeat deex.
    pose proof (Dent.rep_items_eq H0 H1); subst.
    cleanup;
    eapply listpred_dmatch_eq; eauto.
  Qed.

  Theorem bfile0_empty : rep BFILE.bfile0 empty_mem.
  Proof.
    unfold rep, Dent.rep, Dent.items_valid.
    exists nil; firstorder.
    exists nil; simpl.
    setoid_rewrite Dent.Defs.ipack_nil.
    assert (emp (list2nmem (@nil valuset))) by firstorder.
    pred_apply' H; cancel.
    apply Forall_nil.
  Qed.

  Theorem rep_no_0_inum: forall f m, rep f m ->
    forall name isdir, m name = Some (0, isdir) -> False.
  Proof.
    unfold rep. intros. repeat deex.
    eauto using listpred_dmatch_no_0_inum.
  Qed.

  Theorem crash_eq : forall f f' m1 m2,
    BFILE.file_crash f f' ->
    rep f m1 ->
    rep f' m2 ->
    m1 = m2.
  Proof.
    intros.
    apply eq_sym.
    eapply rep_mem_eq; eauto.

    unfold rep in *.
    repeat deex.
    eexists; intuition eauto.
    assert (delist0 = delist).
    eapply Dent.file_crash_rep_eq; eauto.
    subst; eauto.
  Qed.

  Theorem crash_rep : forall f f' m,
    BFILE.file_crash f f' ->
    rep f m ->
    rep f' m.
  Proof.
    unfold rep; intros.
    repeat deex.
    eexists; intuition eauto.
    eapply Dent.file_crash_rep; eauto.
  Qed.

End DIR.
