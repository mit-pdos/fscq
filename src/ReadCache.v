Require Import Mem.
Require Import List.
Require Import Prog.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Array.
Require Import Pred PredCrash.
Require Import Hoare.
Require Import SepAuto.
Require Import BasicProg.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import AsyncDisk.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.

Definition eviction_state : Type := unit.
Definition eviction_init : eviction_state := tt.
Definition eviction_update (s : eviction_state) (a : addr) := s.
Definition eviction_choose (s : eviction_state) : (addr * eviction_state) := (0, s).



Record cachestate := {
  CSMap : Map.t valu;
  CSCount : nat;
  CSMaxCount : nat;
  CSEvict : eviction_state
}.

Module RCache.

  Definition rep (cs : cachestate) (m : @rawdisk) : rawpred :=
    (diskIs m *
     [[ Map.cardinal (CSMap cs) = CSCount cs ]] *
     [[ CSCount cs <= CSMaxCount cs ]] *
     [[ CSMaxCount cs <> 0 ]] *
     [[ forall a v, Map.MapsTo a v (CSMap cs) -> exists old, m a = Some (v, old) ]])%pred.

  Definition maybe_evict T (cs : cachestate) rx : prog T :=
    If (lt_dec (CSCount cs) (CSMaxCount cs)) {
      rx cs
    } else {
      let (victim, evictor) := eviction_choose (CSEvict cs) in
      match (Map.find victim (CSMap cs)) with
      | Some v => rx (Build_cachestate (Map.remove victim (CSMap cs))
                                       (CSCount cs - 1)
                                       (CSMaxCount cs) evictor)
      | None => (* evictor failed, evict first block *)
        match (Map.elements (CSMap cs)) with
        | nil => rx cs
        | (a,v) :: tl => rx (Build_cachestate (Map.remove a (CSMap cs))
                                              (CSCount cs - 1)
                                              (CSMaxCount cs) (CSEvict cs))
        end
      end
    }.

  Definition read T a (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    match Map.find a (CSMap cs) with
    | Some v => rx ^(cs, v)
    | None =>
      v <- Read a;
      rx ^(Build_cachestate (Map.add a v (CSMap cs)) (CSCount cs + 1)
                            (CSMaxCount cs) (eviction_update (CSEvict cs) a), v)
    end.

  Definition write T a v (cs : cachestate) rx : prog T :=
    cs <- maybe_evict cs;
    Write a v;;
    match Map.find a (CSMap cs) with
    | Some _ =>
      rx (Build_cachestate (Map.add a v (CSMap cs)) (CSCount cs)
                           (CSMaxCount cs) (eviction_update (CSEvict cs) a))
    | None =>
      rx (Build_cachestate (Map.add a v (CSMap cs)) (CSCount cs + 1)
                           (CSMaxCount cs) (eviction_update (CSEvict cs) a))
    end.

  Definition sync T a (cs : cachestate) rx : prog T :=
    SyncAddr a;;
    rx cs.

  Definition trim T a (cs : cachestate) rx : prog T :=
    Trim a;;
    match Map.find a (CSMap cs) with
    | Some _ =>
      rx (Build_cachestate (Map.remove a (CSMap cs))
                           (CSCount cs - 1) (CSMaxCount cs) (CSEvict cs))
    | None =>
      rx cs
    end.

  Definition cache0 sz := Build_cachestate (Map.empty valu) 0 sz eviction_init.

  Definition init T (cachesize : nat) (rx : cachestate -> prog T) : prog T :=
    rx (cache0 cachesize).

  Definition read_array T a i cs rx : prog T :=
    r <- read (a + i) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a + i) v cs;
    rx cs.

  Definition sync_array T a i cs rx : prog T :=
    cs <- sync (a + i) cs;
    rx cs.

  Definition trim_array T a i cs rx : prog T :=
    cs <- trim (a + i) cs;
    rx cs.



  Local Hint Resolve Map.remove_3.
  Local Hint Resolve Map.add_3.
  Local Hint Resolve Map.find_2.
  Local Hint Resolve mapsto_add.

  Local Hint Unfold rep : hoare_unfold.

  Theorem maybe_evict_ok : forall cs,
    {< d,
    PRE
      rep cs d
    POST RET:cs
      rep cs d * [[ CSCount cs < CSMaxCount cs ]]
    CRASH
      exists cs', rep cs' d
    >} maybe_evict cs.
  Proof.
    unfold maybe_evict, rep.
    step.
    step.
    safestep.
    rewrite map_remove_cardinal; eauto.
    eauto.
    replace (CSCount cs) with (CSMaxCount cs) in * by omega.
    rewrite Map.cardinal_1 in *. rewrite Heql in *; simpl in *; omega.
    rewrite map_remove_cardinal by (eapply map_elements_hd_in; eauto); eauto.
    eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (maybe_evict _) _) => apply maybe_evict_ok : prog.


  Theorem read_ok : forall cs a,
    {< d (F : rawpred) v,
    PRE
      rep cs d * [[ (F * a |~> v)%pred d ]]
    POST RET:^(cs, r)
      rep cs d * [[ r = v ]]
    CRASH
      exists cs', rep cs' d
    >} read a cs.
  Proof.
    unfold read.

    safestep.
    cancel; eauto.
    eauto.

    safestep.
    denote ptsto as Hx; apply ptsto_valid' in Hx as Hy.
    apply Map.find_2 in Heqo.
    denote (Map.MapsTo) as Hz; apply Hz in Heqo.
    rewrite Hy in Heqo; deex; congruence.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel; cancel.

    safestep.
    rewrite <- diskIs_combine_same with (m:=d) (a:=a); try pred_apply; cancel.
    rewrite map_add_cardinal; auto.
    intro Hm; destruct Hm as [? Hm].
    apply Map.find_1 in Hm. congruence.

    denote ptsto as Hx; apply ptsto_valid' in Hx as Hy.
    destruct (addr_eq_dec a a0); subst.
    denote Map.add as Hz; apply mapsto_add in Hz; subst; eauto.
    denote (_ = Some _) as Hz; edestruct Hz.
    eapply Map.add_3; eauto.
    eexists; eauto.

    cancel; eauto.
    rewrite <- diskIs_combine_same with (m:=d) (a:=a); try pred_apply; cancel.
    cancel; eauto.

    Unshelve.
    all: eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.

  Remove Hints okToUnify: okToUnify.

  Theorem write_ok : forall cs a v,
    {< d (F : rawpred) v0,
    PRE
      rep cs d * [[ (F * a |-> v0)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} write a v cs.
  Proof.
    unfold write.
    safestep.
    cancel; eauto.
    eauto.

    safestep.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.

    safestep.
    rewrite <- diskIs_combine_upd with (m:=d) (a:=a); try pred_apply; cancel.
    rewrite map_add_dup_cardinal; eauto.
    destruct (addr_eq_dec a a0); subst.

    erewrite <- mapsto_add with (v := v0) by eauto.
    rewrite upd_eq; eauto.
    rewrite upd_ne by auto.
    denote Map.MapsTo as Hx; apply Map.add_3 in Hx; eauto.

    denote ptsto as Hx.
    apply sep_star_comm; apply sep_star_comm in Hx.
    eapply ptsto_upd; pred_apply; cancel.

    rewrite <- diskIs_combine_upd with (m:=d) (a:=a); cancel.
    rewrite map_add_cardinal; eauto.
    intro Hm; destruct Hm as [? Hm].
    apply Map.find_1 in Hm. congruence.

    destruct (addr_eq_dec a a0); subst.
    denote Map.MapsTo as Hx.
    apply mapsto_add in Hx; subst.
    rewrite upd_eq by auto. eauto.
    denote Map.MapsTo as Hx.
    apply Map.add_3 in Hx; auto.
    rewrite upd_ne by auto. auto.

    denote ptsto as Hx.
    apply sep_star_comm; apply sep_star_comm in Hx.
    eapply ptsto_upd; pred_apply; cancel.

    cancel; eauto.
    rewrite <- diskIs_combine_same with (m:=d) (a:=a); try pred_apply; cancel.
    cancel; eauto. 
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.

  Theorem sync_ok : forall a cs,
    {< d (F : rawpred) v,
    PRE
      rep cs d * [[ (F * a |-> v)%pred d ]]
    POST RET:cs
      exists d', rep cs d' * [[ (F * a |-> (fst v, nil))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} sync a cs.
  Proof.
    unfold sync, rep.
    safestep.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.

    safestep.
    eassign (@Mem.upd _ _ addr_eq_dec d a (v_cur, [])); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.
    denote! (forall _ _, Map.MapsTo _ _ _ -> _) as Hx.
    denote Map.MapsTo as Hy; denote ptsto as Hz.
    apply Hx in Hy; deex; denote (_ = Some _) as Hy.
    destruct (addr_eq_dec a a0); subst.
    apply sep_star_comm in Hz; apply ptsto_valid in Hz.
    rewrite Hz in Hy. inversion Hy. subst.
    rewrite upd_eq by auto. eexists. eauto.
    rewrite upd_ne by auto. eexists. eauto.
    apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

    cancel.
    rewrite <- diskIs_combine_same with (m:=d) (a:=a); try pred_apply; cancel.
    all: eauto.
    Unshelve.
    5: exact v_cur.  all: eauto.
    destruct cs; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

(*
  Theorem trim_ok : forall a cs,
    {< d (F : rawpred) vs,
    PRE
      rep cs d * [[ (F * a |-> vs)%pred d ]]
    POST RET:cs
      exists d', rep cs d' * [[ (F * a |->?)%pred d' ]]
    CRASH
      exists cs' d', rep cs' d' * [[ (F * a |->?)%pred d' ]]
    >} trim a cs.
  Proof.
    unfold trim, rep.
    intros; eapply pimpl_ok2; eauto with prog.
    intros; norm.
    unfold stars; simpl.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    intuition.

    case_eq (Map.find a (CSMap cs)); intros.
    eapply pimpl_ok2; eauto with prog.
    intros; norm.
    eassign (@Mem.upd _ _ addr_eq_dec d a (v0_cur, v0_old)); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.
    intuition.
    rewrite map_remove_cardinal. eauto. eauto.
    destruct (addr_eq_dec a a0).
    apply MapFacts.remove_mapsto_iff in H0. intuition.
    rewrite upd_ne by eauto. eauto.

    assert ((a |-> (v0_cur, v0_old) * F)%pred (Mem.upd d a (v0_cur, v0_old))).
    eapply ptsto_upd. pred_apply; cancel.
    pred_apply; cancel.

    eapply pimpl_ok2; eauto with prog.
    intros; norm.
    eassign (@Mem.upd _ _ addr_eq_dec d a (v0_cur, v0_old)); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.
    intuition.

    destruct (addr_eq_dec a a0).
    apply MapProperties.F.find_mapsto_iff in H0. congruence.
    rewrite upd_ne by eauto. eauto.

    assert ((a |-> (v0_cur, v0_old) * F)%pred (Mem.upd d a (v0_cur, v0_old))).
    eapply ptsto_upd. pred_apply; cancel.
    pred_apply; cancel.

    pimpl_crash. norm.
    eassign (@Mem.upd _ _ addr_eq_dec d a (v0_cur, v0_old)); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.

    intuition.
    eassign (Build_cachestate (Map.empty valu) 0 (CSMaxCount cs) eviction_init).
    all: simpl in *; eauto; try omega.
    apply MapProperties.F.empty_mapsto_iff in H; exfalso; eauto.

    assert ((a |-> (v0_cur, v0_old) * F)%pred (Mem.upd d a (v0_cur, v0_old))).
    eapply ptsto_upd. pred_apply; cancel.
    pred_apply; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (trim _ _) _) => apply trim_ok : prog.
*)

  (**
   * We have two versions of [init].  [init_load] will have a theorem that
   * proves that any frame we had on the base disk can be applied to the
   * new virtual state inside [BUFCACHE.rep].  [init_recover] will have a
   * theorem about restoring the state of the buffer cache after a crash,
   * where the state was already under [BUFCACHE.rep].
   *)
  Definition init_load := init.
  Definition init_recover := init.

  (**
   * [init_load_ok] uses the {!< .. >!} variant of the Hoare statement, as
   * we need it to be "frameless"; otherwise the {< .. >} notation adds an
   * extra frame around the whole thing, which looks exactly like our own
   * frame [F], and makes it difficult to use automation.
   *)
  Theorem init_load_ok : forall cachesize,
    {!< F,
    PRE
      F * [[cachesize <> 0]]
    POST RET:cs
      exists d, rep cs d * [[ F d ]]
    CRASH
      F
    >!} init_load cachesize.
  Proof.
    unfold init_load, init, rep.
    step.

    eapply pimpl_ok2; eauto.
    simpl; intros.

    (**
     * Special-case for initialization, because we are moving a predicate [F]
     * from the base memory to a virtual memory.
     *)
    match goal with
    | [ |- _ =p=> _ * ?E * [[ _ = _ ]] * [[ _ = _ ]] ] =>
      remember (E)
    end.

    unfold pimpl; intros.
    destruct_lift H; subst.

    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    exists m.
    repeat (apply sep_star_lift_apply'; eauto).
    congruence.
    cbn; omega.
    intros.
    contradict H0; apply Map.empty_1.
  Qed.

  Hint Extern 1 ({{_}} progseq (init_load _) _) => apply init_load_ok : prog.


  Theorem init_recover_ok : forall cachesize,
    {< d F,
    PRE
      exists cs, rep cs d *
      [[ F d ]] * [[ cachesize <> 0 ]]
    POST RET:cs
      exists d', rep cs d' * [[ F d' ]]
    CRASH
      exists cs, rep cs d
    >} init_recover cachesize.
  Proof.
    unfold init_recover, init, rep.
    step.

    eapply pimpl_ok2; eauto.
    simpl; intros.

    (**
     * Special-case for initialization, because we are moving a predicate [F]
     * from the base memory to a virtual memory.
     *)
    match goal with
    | [ |- _ =p=> _ * ?E * [[ _ = _ ]] * [[ _ = _ ]] ] =>
      remember (E)
    end.

    cancel; subst.
    cbn; auto.
    contradict H; apply Map.empty_1.
  Qed.

  Hint Extern 1 ({{_}} progseq (init_recover _) _) => apply init_recover_ok : prog.


  Theorem read_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:^(cs, v)
      rep cs d * [[ v = fst (selN vs i ($0, nil)) ]]
    CRASH
      exists cs', rep cs' d
    >} read_array a i cs.
  Proof.
    unfold read_array.
    hoare.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_array _ _ _) _) => apply read_array_ok : prog.

  Lemma ptsto_tuple : forall AT VA VB AEQ a v,
    @pimpl AT AEQ (VA * VB) (a |-> v) (a |-> (fst v, snd v)).
  Proof. cancel. Qed.

  Theorem write_array_ok : forall a i v cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} write_array a i v cs.
  Proof.
    unfold write_array, vsupd.
    hoare.

    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _) _) => apply write_array_ok : prog.

  Theorem sync_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync vs i))%pred d' ]]
    CRASH
      exists cs', rep cs' d
    >} sync_array a i cs.
  Proof.
    unfold sync_array, vssync.
    hoare.

    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync_array _ _ _) _) => apply sync_array_ok : prog.

(*
  Theorem trim_array_ok : forall a i cs,
    {< d (F : rawpred) vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d' v', rep cs d' *
      [[ (F * arrayN a (updN vs i v'))%pred d' ]]
    CRASH
      exists cs' d' v', rep cs' d' *
      [[ (F * arrayN a (updN vs i v'))%pred d' ]]
    >} trim_array a i cs.
  Proof.
    unfold trim_array.
    hoare.

    rewrite <- surjective_pairing.
    rewrite isolateN_fwd with (i:=i) by auto. cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    cancel; eauto.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    Grab Existential Variables.
    exact ($0, nil).
  Qed.

  Hint Extern 1 ({{_}} progseq (trim_array _ _ _) _) => apply trim_array_ok : prog.
*)

  Definition read_range T A a nr (vfold : A -> valu -> A) a0 cs rx : prog T :=
    let^ (cs, r) <- ForN i < nr
    Ghost [ F crash d vs ]
    Loopvar [ cs pf ]
    Continuation lrx
    Invariant
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ pf = fold_left vfold (firstn i (map fst vs)) a0 ]]
    OnCrash  crash
    Begin
      let^ (cs, v) <- read_array a i cs;
      lrx ^(cs, vfold pf v)
    Rof ^(cs, a0);
    rx ^(cs, r).


  Theorem read_range_ok : forall A a nr vfold (a0 : A) cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ nr <= length vs ]]
    POST RET:^(cs, r)
      rep cs d * [[ r = fold_left vfold (firstn nr (map fst vs)) a0 ]]
    CRASH
      exists cs', rep cs' d
    >} read_range a nr vfold a0 cs.
  Proof.
    unfold read_range; intros.
    safestep.
    eauto. cancel; eauto. eauto. eauto. eauto.
    safestep.
    cancel; eauto. eauto. eauto. omega.

    safestep.
    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; auto.
    rewrite map_length; omega.

    cancel; eauto.
    safestep.
    cancel; eauto.
    Unshelve. exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (read_range _ _ _ _ _) _) => apply read_range_ok : prog.

  Definition write_range T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_range vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- write_array a i (selN l i $0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.

  Theorem write_range_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ length l <= length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_range vs l))%pred d' ]]
    CRASH
      exists cs' d' n, rep cs' d' * [[ n <= length l ]] *
      [[ (F * arrayN a (vsupd_range vs (firstn n l)))%pred d' ]]
    >} write_range a l cs.
  Proof.
    unfold write_range; intros.
    safestep.
    cancel; eauto. eauto.
    pred_apply; rewrite vsupd_range_nil; eauto.
    eauto.

    safestep.
    cancel; eauto. eauto.
    pred_apply; eauto.
    rewrite vsupd_range_length; try omega.
    rewrite firstn_length_l; omega.

    step.
    apply arrayN_unify.
    erewrite firstn_S_selN_expand.
    apply vsupd_range_progress; auto.
    omega.

    safecancel; eauto; omega.

    step.
    rewrite firstn_oob by omega; auto.

    safecancel.
    eauto. eauto. eauto. eauto.
    eassign 0; omega.
    pred_apply; rewrite vsupd_range_nil; eauto.
    Unshelve. exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (write_range _ _ _) _) => apply write_range_ok : prog.

  Definition sync_range T a nr cs rx : prog T :=
    let^ (cs) <- ForN i < nr
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_range vs i))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a i cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.

  Theorem sync_range_ok : forall a n cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ n <= length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_range vs n))%pred d' ]]
    CRASH
      exists cs' d' m, rep cs' d' * [[ m <= n ]] *
      [[ (F * arrayN a (vssync_range vs m))%pred d' ]]
    >} sync_range a n cs.
  Proof.
    unfold sync_range; intros.
    safestep.
    cancel; eauto. eauto.
    pred_apply; cbn; eauto.
    eauto.

    safestep.
    cancel; eauto. eauto.
    pred_apply; eauto.
    rewrite vssync_range_length; try omega.

    step.
    apply arrayN_unify.
    apply vssync_range_progress; auto.
    omega.

    safecancel; eauto; omega.

    step.
    safecancel.
    eauto. eauto. eauto. eauto.
    eassign 0; omega.
    pred_apply; cbn; eauto.
    Unshelve. exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync_range _ _ _) _) => apply sync_range_ok : prog.
  Hint Extern 0 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (arrayN ?a _) (arrayN ?a _)) => constructor : okToUnify.

  Local Hint Resolve vsupd_vecs_length_ok.

  Definition write_vecs T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      let v := selN l i (0, $0) in
      cs <- write_array a (fst v) (snd v) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.


  Theorem write_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => fst e < length vs) l ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_vecs vs l))%pred d' ]]
    CRASH
      exists cs' d' n, rep cs' d' * [[ n <= length l ]] *
      [[ (F * arrayN a (vsupd_vecs vs (firstn n l)))%pred d' ]]
    >} write_vecs a l cs.
  Proof.
    unfold write_vecs.
    safestep.
    eauto.

    safestep.
    safestep.
    apply arrayN_unify.
    apply vsupd_vecs_progress; auto.

    safecancel; eauto; omega.
    step.
    apply arrayN_unify.
    rewrite firstn_oob; auto.

    safecancel.
    eauto. eauto. eauto. eauto.
    eassign 0; omega.
    pred_apply; cbn; eauto.
    Unshelve. exact tt.
  Qed.

  Local Hint Resolve vssync_vecs_length_ok.

  Definition sync_vecs T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ F crash vs ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_vecs vs (firstn i l)))%pred d' ]]
    OnCrash crash
    Begin
      cs <- sync_array a (selN l i 0) cs;
      lrx ^(cs)
    Rof ^(cs);
    rx cs.

  Theorem sync_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_vecs vs l))%pred d' ]]
    CRASH
      exists cs' d' n, rep cs' d' * [[ n <= length l ]] *
      [[ (F * arrayN a (vssync_vecs vs (firstn n l)))%pred d' ]]
    >} sync_vecs a l cs.
  Proof.
    unfold sync_vecs.
    safestep.
    eauto.

    safestep.
    safestep.
    apply arrayN_unify.
    apply vssync_vecs_progress; auto.

    safecancel; eauto; omega.
    step.
    apply arrayN_unify.
    rewrite firstn_oob; auto.

    safecancel.
    eauto. eauto. eauto. eauto.
    eassign 0; omega.
    pred_apply; cbn; eauto.
    Unshelve. exact tt.
  Qed.

  Hint Extern 1 ({{_}} progseq (write_vecs _ _ _) _) => apply write_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_vecs _ _ _) _) => apply sync_vecs_ok : prog.

  Lemma crash_xform_rep: forall cs m,
    crash_xform (rep cs m) =p=> exists m' cs', [[ possible_crash m m' ]] * rep cs' m'.
  Proof.
    unfold rep.
    intros.
    repeat rewrite crash_xform_sep_star_dist.
    rewrite crash_xform_diskIs.
    repeat rewrite crash_xform_lift_empty.
    cancel.
    eassign (Build_cachestate (Map.empty valu) 0 (CSMaxCount cs) (CSEvict cs)).
    auto.
    simpl; omega.
    simpl in *; omega.
    inversion H.
  Qed.

  Lemma crash_xform_rep_r: forall m m' cs',
    possible_crash m m' ->
    rep cs' m' =p=> crash_xform (rep (cache0 (CSMaxCount cs')) m).
  Proof.
    unfold rep; intros.
    cancel.
    repeat rewrite crash_xform_sep_star_dist.
    repeat rewrite crash_xform_lift_empty.
    cancel.
    apply crash_xform_diskIs_r; auto.
    exfalso.
    eapply MapFacts.empty_mapsto_iff; eauto.
  Qed.

  Lemma crash_xform_rep_r_ex: forall m m' cs,
    possible_crash m m' ->
    rep cs m' =p=> exists cs', crash_xform (rep cs' m).
  Proof.
    unfold rep; intros.
    cancel.
    repeat rewrite crash_xform_sep_star_dist.
    repeat rewrite crash_xform_lift_empty.
    cancel.
    apply crash_xform_diskIs_r; auto.
    eassign (cache0 (CSMaxCount cs)).
    all: simpl; auto.
    omega.
    simpl in *; exfalso.
    eapply MapFacts.empty_mapsto_iff; eauto.
  Qed.

  Lemma crash_xform_rep_pred : forall cs m (F : pred),
    F%pred m ->
    crash_xform (rep cs m) =p=>
    exists m' cs', rep cs' m' * [[ (crash_xform F)%pred m' ]].
  Proof.
    intros.
    rewrite crash_xform_rep.
    norm. cancel. split; auto.
    exists m; eauto.
  Qed.

  Lemma crash_xform_rep_pred_r: forall m' cs' (F : pred),
    (crash_xform F)%pred m' ->
    rep cs' m' =p=> exists m, crash_xform (rep (cache0 (CSMaxCount cs')) m) * [[ F%pred m ]].
  Proof.
    intros.
    unfold crash_xform in H; deex.
    rewrite crash_xform_rep_r; eauto.
    cancel.
  Qed.

  Hint Rewrite crash_xform_rep : crash_xform.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.


End RCache.

Global Opaque RCache.init.
Global Opaque RCache.init_load.
Global Opaque RCache.init_recover.
