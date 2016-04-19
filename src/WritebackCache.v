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
Require Import Cache.
Require Import MemPred.
Require Import ListPred.
Require Import FunctionalExtensionality.

Import AddrMap.
Import ListNotations.

Set Implicit Arguments.


Record wbcachestate := {
  WbCs : cachestate;
  WbBuf : Map.t valu
}.

Module WBCACHE.

  Definition cachepred (cache : Map.t valu) (a : addr) (vs : valuset) : @pred _ addr_eq_dec valuset :=
    match Map.find a cache with
    | None => a |-> vs
    | Some v => (exists vsdisk old_cache_writes, a |-> vsdisk * [[ vs = (v, old_cache_writes ++ vsmerge vsdisk) ]])%pred
    end.

  Lemma cachepred_remove_invariant : forall a a' v cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.remove a' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma cachepred_add_invariant : forall a a' v v' cache,
    a <> a' -> cachepred cache a v =p=> cachepred (Map.add a' v' cache) a v.
  Proof.
    unfold cachepred; intros.
    rewrite MapFacts.add_neq_o; auto.
  Qed.

  Definition rep (wcs : wbcachestate) (m : rawdisk) : rawpred :=
    (exists cm, BUFCACHE.rep (WbCs wcs) cm *
     [[ @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred (WbBuf wcs)) m cm ]])%pred.

  Definition read T a (wcs : wbcachestate) rx : prog T :=
    match Map.find a (WbBuf wcs) with
    | Some v => rx ^(wcs, v)
    | None =>
      let^ (new_cs, v) <- BUFCACHE.read a (WbCs wcs);
      rx ^(Build_wbcachestate new_cs (WbBuf wcs), v)
    end.

  Definition write T a v (wcs : wbcachestate) rx : prog T :=
    rx (Build_wbcachestate (WbCs wcs) (Map.add a v (WbBuf wcs))).

  Definition sync T a (wcs : wbcachestate) rx : prog T :=
    match (Map.find a (WbBuf wcs)) with
    | Some v =>
      new_cs <- BUFCACHE.write a v (WbCs wcs);
      new_cs <- BUFCACHE.sync a new_cs;
      rx (Build_wbcachestate new_cs (Map.remove a (WbBuf wcs)))
    | None =>
      new_cs <- BUFCACHE.sync a (WbCs wcs);
      rx (Build_wbcachestate new_cs (WbBuf wcs))
    end.

  Definition cache0 sz := Build_wbcachestate (BUFCACHE.cache0 sz) (Map.empty _).

  Definition init T (cachesize : nat) (rx : wbcachestate -> prog T) : prog T :=
    rx (cache0 cachesize).

  Theorem read_ok : forall wcs a,
    {< d (F : rawpred) v,
    PRE
      rep wcs d * [[ (F * a |~> v)%pred d ]]
    POST RET:^(wcs, r)
      rep wcs d * [[ r = v ]]
    CRASH
      exists wcs', rep wcs' d
    >} read a wcs.
  Proof.
    unfold read. unfold rep at 1 2.
    (* Don't unfold the [rep] in the crash condition, since that
     * causes incorrect evar instantiation..
     *)
    intros.
    case_eq (Map.find a (WbBuf wcs)); intros.
    - step.
      step.
      subst.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6.
      destruct_lift H6; congruence.
      unfold rep; cancel.
    - step.
      rewrite mem_pred_extract; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2; rewrite H.
      cancel.
      step.
      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      unfold rep; cancel.
  Qed.


  Theorem sync_ok_strict : forall wcs a,
    {< d (F : rawpred) v vold,
    PRE
      rep wcs d * [[ (F * a |-> (v, vold))%pred d ]]
    POST RET:wcs
      exists d',
      rep wcs d' * [[ (F * a |=> v)%pred d' ]]
    CRASH
      exists wcs' d', rep wcs' d' *
      ([[ exists n, (F * a |-> (v, skipn n vold))%pred d' ]])%pred
    >} sync a wcs.
  Proof.
    unfold sync, rep.
    intros.
    prestep; norml.
    - denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heqo in Hx; destruct_lift Hx.
      cancel.

      step.
      step.
      rewrite <- mem_pred_absorb with (a := a).
      unfold cachepred at 3.
      rewrite MapFacts.remove_eq_o by auto.
      cancel.
      apply mem_pred_pimpl_except.
      intros; apply cachepred_remove_invariant; auto.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      (* crash conditions *)
      norm; unfold stars; simpl.
      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb.
      unfold cachepred at 2; simpl.
      rewrite MapFacts.remove_eq_o by reflexivity.
      pred_apply; cancel.
      rewrite mem_pred_pimpl_except; cancel.
      apply cachepred_remove_invariant; auto.
      exists (length dummy); rewrite skipn_app.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb; unfold cachepred at 2.
      rewrite MapFacts.remove_eq_o by reflexivity.
      pred_apply; cancel.
      rewrite mem_pred_pimpl_except; cancel.
      apply cachepred_remove_invariant; auto.
      eexists; rewrite skipn_oob by eauto.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      pimpl_crash; norm; unfold stars; simpl.
      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition subst.
      apply mem_pred_absorb; unfold cachepred at 2.
      rewrite Heqo; pred_apply; cancel.
      exists (length dummy); rewrite skipn_app.
      eassign (@nil valu); simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb; unfold cachepred at 2.
      rewrite MapFacts.remove_eq_o by reflexivity.
      pred_apply; cancel.
      rewrite mem_pred_pimpl_except; cancel.
      apply cachepred_remove_invariant; auto.
      exists (length dummy); subst; rewrite skipn_app.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

    - denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx.
      rewrite Heqo in Hx; destruct_lift Hx.
      cancel.

      step.
      rewrite <- mem_pred_absorb with (a := a).
      unfold cachepred at 3; rewrite Heqo.
      cancel.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      pimpl_crash; norm; unfold stars; simpl.
      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb.
      unfold cachepred at 2; rewrite Heqo.
      pred_apply; cancel.
      subst; exists 0; simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eassign (Build_wbcachestate cs' (WbBuf wcs)).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb.
      unfold cachepred at 2; rewrite Heqo.
      pred_apply; cancel.
      eexists; rewrite skipn_oob; eauto.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      Unshelve.
      all: try exact addr; try exact addr_eq_dec; try exact empty_mem.
      all: exact (fun a b => emp).
  Qed.


  Theorem write_ok : forall wcs a v,
    {< d (F : rawpred) v0,
    PRE
      rep wcs d * [[ (F * a |-> v0)%pred d ]]
    POST RET:wcs
      exists d', rep wcs d' * [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    CRASH
      exists wcs', rep wcs' d \/
      exists d', rep wcs' d' *
      [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    >} write a v wcs.
  Proof.
    unfold write, rep.
    intros.
    case_eq (Map.find a (WbBuf wcs)); intros.
    - step.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6. destruct_lift H6.
      step.
      pred_apply. rewrite <- mem_pred_absorb. subst; simpl.
      unfold cachepred at 3. rewrite MapFacts.add_eq_o by reflexivity. cancel.
      apply mem_pred_pimpl_except. intros; apply cachepred_add_invariant; auto.
      eassign (w :: dummy); unfold vsmerge; simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
      or_l; cancel.

    - step.
      eapply mem_pred_extract in H6; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in H6. rewrite H in H6.
      step.
      subst; simpl.
      pred_apply.
      rewrite <- mem_pred_absorb with (a:=a). unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by auto. cancel.
      apply mem_pred_pimpl_except. intros; apply cachepred_add_invariant; auto.

      eassign (@nil valu); simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
      or_l; cancel.
  Qed.



  (** crashes and recovery *)

  Lemma xform_cachepred_ptsto : forall m a vs,
    crash_xform (cachepred m a vs) =p=> 
      exists v, [[ In v (vsmerge vs) ]] * a |=> v.
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros.
    xform_norm; subst.
    rewrite crash_xform_ptsto.
    cancel; subst.
    right; apply in_app_iff; right; simpl; intuition.
    right; apply in_app_iff; right; simpl; intuition.
    rewrite crash_xform_ptsto.
    cancel.
  Qed.

  Lemma xform_cachepred : forall m a vs,
    crash_xform (cachepred m a vs) =p=> 
      exists v cached, [[ In v (vsmerge vs) ]] * cachepred m a (v, cached).
  Proof.
    unfold cachepred; intros.
    case_eq (Map.find a m); intros.
    xform_norm; subst.
    rewrite crash_xform_ptsto.
    cancel.
    rewrite crash_xform_ptsto.
    cancel.
    Unshelve. eauto.
  Qed.


  Lemma xform_mem_pred_cachepred : forall wcs hm,
    crash_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred wcs) hm) =p=> 
      exists m', [[ possible_crash hm m' ]] *
      @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred (Map.empty _)) m'.
  Proof.
    intros.
    rewrite xform_mem_pred.
    unfold mem_pred at 1.
    xform_norm; subst.

    rename hm_avs into l.
    revert H; revert l.
    induction l; simpl; intros.
    cancel.
    apply mem_pred_empty_mem.
    unfold possible_crash; intuition.

    Opaque vsmerge.
    inversion H; destruct a; subst; simpl in *.
    unfold mem_pred_one; simpl.

    rewrite IHl by auto.
    xform_norm.
    rewrite xform_cachepred_ptsto.
    cancel.
    instantiate (1 := upd m' n (v0, nil)).
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3.
    rewrite MapFacts.empty_o; cancel.
    erewrite <- notindomain_mem_eq; auto.
    eapply possible_crash_notindomain; eauto.
    apply avs2mem_notindomain; auto.
    apply possible_crash_upd; eauto.
    Transparent vsmerge.
  Qed.


  Lemma crash_xform_rep: forall cs m,
    crash_xform (rep cs m) =p=>
       exists m' cs', [[ possible_crash m m' ]] * rep cs' m'.
  Proof.
    unfold rep; intros.
    xform_norm.
    rewrite BUFCACHE.crash_xform_rep_pred by eauto.
    xform_norm.
    apply xform_mem_pred_cachepred in H2.
    destruct_lift H2.
    cancel; eauto.
    eassign (Build_wbcachestate cs' (Map.empty _)); cancel.
    eauto.
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



  Lemma listpred_cachepred_notin : forall cs l m a,
    ~ In a (map fst l) ->
    listpred (mem_pred_one (cachepred cs)) l m ->
    m a = None.
  Proof.
    induction l; intros; eauto.
    destruct a; subst; simpl in *; intuition.
    unfold mem_pred_one at 1, cachepred at 1 in H0; simpl in *.
    destruct (Map.find n cs) eqn: Heq.

    destruct_lift H0; subst.
    eapply notindomain_mem_except with (a' := n); eauto.
    apply IHl; eauto.
    eapply ptsto_mem_except; eauto.

    eapply notindomain_mem_except with (a' := n); eauto.
    apply IHl; eauto.
    eapply ptsto_mem_except; eauto.
  Qed.


  Lemma mem_pred_cachepred_none : forall (m1 m2 : mem) cs a,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred cs) m1 m2 ->
    m1 a = None ->
    m2 a = None.
  Proof.
    unfold mem_pred; intros.
    destruct_lift H; subst.
    rename dummy into l.
    apply avs2mem_none_notin in H0 as Hx.
    erewrite listpred_cachepred_notin with (m := m2); eauto.
  Qed.


  Lemma mem_pred_cachepred_some_notin : forall (m1 m2 : mem) cs a v,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred cs) m1 m2 ->
    Map.find a cs = None ->
    m1 a = Some v ->
    m2 a = Some v.
  Proof.
    unfold mem_pred; intros.
    destruct_lift H; subst.
    pose proof (listpred_avs_except addr_eq_dec _ _ _ H3 H1 _ H) as Hx.
    unfold mem_pred_one at 2, cachepred at 2 in Hx; simpl in Hx.
    rewrite H0 in Hx.
    erewrite ptsto_valid'; eauto.
  Qed.

  Lemma mem_pred_cachepred_some_in : forall (m1 m2 : mem) cs a v w,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred cs) m1 m2 ->
    Map.find a cs = Some w ->
    m1 a = Some v ->
    exists v', m2 a = Some v' /\ postfix (vsmerge v') (snd v).
  Proof.
    unfold mem_pred; intros.
    destruct_lift H; subst.

    pose proof (listpred_avs_except addr_eq_dec _ _ _ H3 H1 _ H) as Hx.
    unfold mem_pred_one at 2, cachepred at 2 in Hx; simpl in Hx.
    rewrite H0 in Hx.
    destruct_lift Hx.
    destruct_pair_eq; subst.
    eexists; split.
    erewrite ptsto_valid'; eauto.
    apply postfix_app.
    apply postfix_refl.
  Qed.

  Lemma mem_pred_cachepred_some : forall (m1 m2 : mem) cs a v,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred cs) m1 m2 ->
    m1 a = Some v ->
    exists v', m2 a = Some v' /\ postfix (vsmerge v') (vsmerge v).
  Proof.
    intros.
    destruct (Map.find a cs) eqn: Heq.
    eapply mem_pred_cachepred_some_in in H; eauto.
    repeat deex; eexists; split; eauto.
    apply postfix_tl; auto.
    eapply mem_pred_cachepred_some_notin in H; eauto.
    eexists; split; eauto.
    apply postfix_refl.
  Qed.

  Lemma synced_mem_sel_eq : forall m1 m2 v1 v2 a,
    synced_mem m1 ->
    m1 a = Some v1 ->
    m2 a = Some v2 ->
    postfix (vsmerge v2) (vsmerge v1) ->
    v1 = v2.
  Proof.
    intros.
    assert (snd v1 = nil).
    eapply synced_mem_snd_nil; eauto.
    destruct v1, v2; unfold vsmerge in *; simpl in *; subst.
    apply postfix_singular in H2; try congruence.
  Qed.


  Lemma mem_pred_cachepred_eq : forall (m1 m2 : mem) cs,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred cs) m1 m2 ->
    synced_mem m1 ->
    m1 = m2.
  Proof.
    intros.
    apply functional_extensionality; intros.
    destruct (m1 x) eqn: Heq.
    eapply mem_pred_cachepred_some in H; eauto.
    repeat deex; substl (m2 x).
    f_equal; eapply synced_mem_sel_eq; eauto.
    eapply mem_pred_cachepred_none in H; eauto.
  Qed.


  Lemma mem_pred_possible_crash_trans : forall m m1 m2 cs,
    possible_crash m m1 ->
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred cs) m1 m2 ->
    possible_crash m1 m2.
  Proof.
    intros.
    replace m2 with m1.
    apply possible_crash_refl.
    eapply possible_crash_synced; eauto.
    eapply mem_pred_cachepred_eq; eauto.
    eapply possible_crash_synced; eauto.
  Qed.

  Lemma listpred_cachepred_mem_except : forall a v l m buf,
    listpred (mem_pred_one (cachepred buf)) ((a, v) :: l) m ->
    listpred (mem_pred_one (cachepred buf)) l (mem_except m a).
  Proof.
    unfold mem_pred_one; simpl; intros.
    unfold cachepred at 1 in H.
    destruct (Map.find a buf) eqn: Heq.
    destruct_lift H.
    eapply ptsto_mem_except; pred_apply; eauto.
    eapply ptsto_mem_except; pred_apply; eauto.
  Qed.

  Lemma mem_pred_cachepred_refl : forall m m' m'' buf,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred buf) m' m'' ->
    possible_crash m m' ->
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred (Map.empty valu)) m m.
  Proof.
    unfold mem_pred; intros.
    destruct H; destruct_lift H.
    generalize dependent m''.
    generalize dependent m'.
    generalize dependent m.
    induction x; intros.
    - exists nil.
      rewrite listpred_nil in *.
      apply sep_star_assoc.
      apply lift_impl; intros.
      simpl; auto.
      apply lift_impl; intros.
      apply emp_empty_mem_only.
      eapply possible_crash_emp_l; eauto; subst.
      apply emp_empty_mem.
      eapply possible_crash_emp_l; eauto; subst.
      apply emp_empty_mem.

    - destruct a.
      edestruct IHx.
      + inversion H2; eauto.
      + eapply possible_crash_mem_except; eauto.
      + subst.
        rewrite mem_except_avs_except.
        rewrite avs_except_cons; auto.
      + eapply listpred_cachepred_mem_except; eauto.
      + unfold possible_crash in H0.
        specialize (H0 n). inversion H0.
        * exists x0.
          destruct H3.
          rewrite mem_except_none in H1; eauto.
        * destruct H3.
          destruct H3.
          destruct H3.
          exists ((n, x1) :: x0).

          destruct_lift H1.
          apply sep_star_assoc.
          apply lift_impl; intros.
          apply NoDup_cons; eauto.
          eapply avs2mem_none_notin; eauto.
          denote mem_except as Hx; rewrite <- Hx.
          apply mem_except_eq.

          apply lift_impl; intros.
          cbn; denote mem_except as Hx; setoid_rewrite <- Hx.
          rewrite upd_mem_except.
          rewrite upd_nop; auto.
          apply mem_except_ptsto; eauto.
  Qed.


  Definition cache0cs cs := cache0 (CSMaxCount (WbCs cs)).

  Lemma crash_xform_rep_r: forall m m' cs',
    possible_crash m m' ->
    rep cs' m' =p=> crash_xform (rep (cache0cs cs') m).
  Proof.
    unfold rep; intros.
    cancel.
    xform_normr.
    rewrite <- BUFCACHE.crash_xform_rep_r.
    cancel.
    eapply mem_pred_cachepred_refl; eauto.
    eapply possible_crash_trans.
    eauto.
    eapply mem_pred_possible_crash_trans; eauto.
  Qed.



  Lemma sync_ok_xcrash : forall (F : @pred _ addr_eq_dec _) a vold vraw mm cs d raw,
    (F * a |-> vold)%pred d ->
    (mem_pred (cachepred mm) (mem_except d a) * a |-> vraw)%pred raw ->
    incl (vsmerge vraw) (vsmerge vold) ->
    crash_xform (BUFCACHE.rep cs raw) =p=>
    crash_xform (exists wcs' d', rep wcs' d' * [[ (F * a |-> vold)%pred d' ]]).
  Proof.
    unfold rep; intros.
    rewrite BUFCACHE.crash_xform_rep; cancel.
    xform_normr; cancel. xform_normr; cancel.
    instantiate (1 := upd raw a (vold_cur, vold_old)).
    eassign (Build_wbcachestate (BUFCACHE.cache0 (CSMaxCount cs'))
                                (Map.remove a mm)); simpl.
    rewrite <- BUFCACHE.crash_xform_rep_r; eauto.
    eapply possible_crash_ptsto_upd_incl; eauto.
    eapply pimpl_trans; [ apply pimpl_refl | simpl | eapply ptsto_upd; pred_apply; cancel ].
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3.
    rewrite MapFacts.remove_eq_o by reflexivity.
    rewrite mem_pred_pimpl_except; cancel.
    apply cachepred_remove_invariant; auto.
    apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
  Qed.

  Theorem sync_ok : forall wcs a,
    {< d (F : rawpred) v vold,
    PRE
      rep wcs d * [[ (F * a |-> (v, vold))%pred d ]]
    POST RET:wcs
      exists d',
      rep wcs d' * [[ (F * a |=> v)%pred d' ]]
    XCRASH
      exists wcs' d', rep wcs' d' *
      [[ (F * a |-> (v, vold))%pred d' ]]
    >} sync a wcs.
  Proof.
    unfold sync, rep.
    intros.
    prestep.
    - norml.
      denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heqo in Hx.
      destruct_lift Hx; cancel.

      step.
      step.
      rewrite <- mem_pred_absorb with (a := a).
      unfold cachepred at 3.
      rewrite MapFacts.remove_eq_o by auto.
      cancel.

      apply mem_pred_pimpl_except.
      intros; apply cachepred_remove_invariant; auto.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      (* crashes *)
      eapply pimpl_trans; [ | eapply H1 ]; cancel.
      eapply sync_ok_xcrash; eauto.
      apply incl_cons2; apply incl_appr; apply incl_refl.

      eapply pimpl_trans; [ | eapply H1 ]; cancel.
      eapply sync_ok_xcrash; eauto.
      apply incl_cons2; firstorder.

      eapply pimpl_trans; [ | eapply H1 ]; eauto.
      xform_norml; rewrite <- crash_xform_exists_comm.
      eapply sync_ok_xcrash; eauto; subst.
      apply incl_tl; apply incl_appr; apply incl_refl.
      eapply sync_ok_xcrash; eauto; subst.
      apply incl_cons2; apply incl_appr; apply incl_refl.

    - norml.
      denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heqo in Hx.
      destruct_lift Hx; cancel.

      step.
      rewrite <- mem_pred_absorb with (a := a).
      unfold cachepred at 3.
      rewrite Heqo; cancel.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      (* crashes *)
      eapply pimpl_trans; [ | eapply H1 ]; eauto.
      xform_norml; rewrite <- crash_xform_exists_comm.
      eapply sync_ok_xcrash; eauto; subst.
      apply incl_refl.
      eapply sync_ok_xcrash; eauto; subst.
      apply incl_cons2; firstorder.

      Unshelve.
      all: try exact addr; try exact addr_eq_dec; try exact empty_mem.
      all: exact (fun a b => emp).
  Qed.


  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.


  Definition read_array T a i cs rx : prog T :=
    r <- read (a + i) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a + i) v cs;
    rx cs.

  Definition sync_array T a i cs rx : prog T :=
    cs <- sync (a + i) cs;
    rx cs.

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


  Theorem write_array_ok : forall a i v cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
    >} write_array a i v cs.
  Proof.
    unfold write_array, vsupd.
    hoare.

    pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite surjective_pairing with (p := selN vs i ($0, nil)).
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    cancel.
    or_l; cancel.

    cancel.
    or_r; cancel.
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
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * arrayN a (vssync vs i))%pred d' ]]
    >} sync_array a i cs.
  Proof.
    unfold sync_array, vssync.
    hoare.

    pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite BUFCACHE.ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    cancel.
    unfold hidden_pred; cancel.

    or_r; cancel.

    apply pimpl_or_r; left; cancel; eauto.
    apply pimpl_or_r; right; cancel; eauto.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.



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

End WBCACHE.
