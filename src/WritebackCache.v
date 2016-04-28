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
Require Import ReadCache.
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

Module WBCache.

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
    (exists cm, RCache.rep (WbCs wcs) cm *
     [[ @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred (WbBuf wcs)) m cm ]])%pred.

  Definition read T a (wcs : wbcachestate) rx : prog T :=
    match Map.find a (WbBuf wcs) with
    | Some v => rx ^(wcs, v)
    | None =>
      let^ (new_cs, v) <- RCache.read a (WbCs wcs);
      rx ^(Build_wbcachestate new_cs (WbBuf wcs), v)
    end.

  Definition write T a v (wcs : wbcachestate) rx : prog T :=
    rx (Build_wbcachestate (WbCs wcs) (Map.add a v (WbBuf wcs))).

  Definition evict T a (wcs : wbcachestate) rx : prog T :=
    match (Map.find a (WbBuf wcs)) with
    | Some v =>
      new_cs <- RCache.write a v (WbCs wcs);
      rx (Build_wbcachestate new_cs (Map.remove a (WbBuf wcs)))
    | None =>
      rx wcs
    end.

  Definition sync T a (wcs : wbcachestate) rx : prog T :=
    match (Map.find a (WbBuf wcs)) with
    | Some v =>
      new_cs <- RCache.write a v (WbCs wcs);
      new_cs <- RCache.sync a new_cs;
      rx (Build_wbcachestate new_cs (Map.remove a (WbBuf wcs)))
    | None =>
      new_cs <- RCache.sync a (WbCs wcs);
      rx (Build_wbcachestate new_cs (WbBuf wcs))
    end.

  Definition cache0 sz := Build_wbcachestate (RCache.cache0 sz) (Map.empty _).

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
      rewrite mem_pred_pimpl_except. cancel.
      intros.
      apply cachepred_remove_invariant; auto.
      exists (length dummy); rewrite skipn_app.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eassign (Build_wbcachestate cs' (Map.remove a (WbBuf wcs))).
      cancel.
      simpl; intuition.
      apply mem_pred_absorb; unfold cachepred at 2.
      rewrite MapFacts.remove_eq_o by reflexivity.
      pred_apply; cancel.
      rewrite mem_pred_pimpl_except. cancel.
      intros.
      apply cachepred_remove_invariant; auto.
      eexists; rewrite skipn_oob by eauto.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      pimpl_crash. cancel.
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
      rewrite mem_pred_pimpl_except. cancel.
      intros.
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

      pimpl_crash. cancel.
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


  Theorem write_ok_strict : forall wcs a v,
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
    rewrite RCache.crash_xform_rep_pred by eauto.
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


  Section MEM_MATCH.

    Variable AT V : Type.
    Variable AEQ : EqDec AT.

    Implicit Types m ma mb : @Mem.mem AT AEQ V.

    Definition mem_match ma mb :=
      forall a, ma a = None <-> mb a = None.

    Lemma mem_match_refl : forall m,
      mem_match m m.
    Proof.
      firstorder.
    Qed.

    Lemma mem_match_trans : forall m ma mb,
      mem_match m ma ->
      mem_match ma mb ->
      mem_match m mb.
    Proof.
      firstorder.
    Qed.

    Lemma mem_match_sym : forall ma mb,
      mem_match ma mb ->
      mem_match mb ma.
    Proof.
      firstorder.
    Qed.

    Lemma mem_match_except : forall ma mb a,
      mem_match ma mb ->
      mem_match (mem_except ma a) (mem_except mb a).
    Proof.
      unfold mem_match; intros.
      unfold mem_except.
      destruct (AEQ a0 a); firstorder.
    Qed.

    Lemma mem_match_upd : forall ma mb a va vb,
      mem_match ma mb ->
      mem_match (upd ma a va) (upd mb a vb).
    Proof.
      unfold mem_match; intros.
      destruct (AEQ a0 a); subst.
      repeat rewrite upd_eq by auto.
      split; congruence.
      repeat rewrite upd_ne by auto.
      firstorder.
    Qed.

    Lemma mem_match_upd_l : forall ma mb a va vb,
      mem_match ma mb ->
      mb a = Some vb ->
      mem_match (upd ma a va) mb.
    Proof.
      unfold mem_match; intros.
      destruct (AEQ a0 a); subst.
      repeat rewrite upd_eq by auto.
      split; congruence.
      repeat rewrite upd_ne by auto.
      firstorder.
    Qed.

    Lemma mem_match_upd_r : forall ma mb a va vb,
      mem_match ma mb ->
      ma a = Some va ->
      mem_match ma (upd mb a vb).
    Proof.
      unfold mem_match; intros.
      destruct (AEQ a0 a); subst.
      repeat rewrite upd_eq by auto.
      split; congruence.
      repeat rewrite upd_ne by auto.
      firstorder.
    Qed.

    Lemma mem_match_cases : forall ma mb a,
      mem_match ma mb ->
      (ma a = None /\ mb a = None) \/
      exists va vb, (ma a = Some va /\ mb a = Some vb).
    Proof.
      intros.
      specialize (H a); destruct H.
      destruct (ma a); destruct (mb a).
      right. eexists; eauto.
      contradict H0; intuition; congruence.
      contradict H; intuition; congruence.
      intuition.
    Qed.

  End MEM_MATCH.


  Lemma mem_pred_cachepred_refl : forall m m' m'' buf,
    @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred buf) m' m'' ->
    mem_match m m' ->
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
      cbn in *; subst.
      assert (@emp _ addr_eq_dec _ m) by firstorder.
      apply lift_impl; intros; auto.
      apply emp_empty_mem_only; auto.

    - destruct a.
      edestruct IHx.
      + inversion H2; eauto.
      + eapply mem_match_except; eauto.
      + subst.
        rewrite mem_except_avs_except.
        rewrite avs_except_cons; auto.
      + eapply listpred_cachepred_mem_except; eauto.
      + destruct (mem_match_cases n H0).
        * exists x0.
          destruct H3.
          rewrite mem_except_none in H1; eauto.
        * do 3 destruct H3.
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

  Lemma possible_crash_mem_match : forall (m1 m2 : rawdisk),
    possible_crash m1 m2 ->
    @mem_match _ _ addr_eq_dec m1 m2.
  Proof.
    unfold possible_crash, mem_match; intuition.
    specialize (H a); intuition.
    repeat deex; congruence.
    specialize (H a); intuition.
    repeat deex; congruence.
  Qed.

  Definition cache0cs cs := cache0 (CSMaxCount (WbCs cs)).

  Lemma crash_xform_rep_r: forall m m' cs',
    possible_crash m m' ->
    rep cs' m' =p=> crash_xform (rep (cache0cs cs') m).
  Proof.
    unfold rep; intros.
    cancel.
    xform_normr.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.
    eapply mem_pred_cachepred_refl; eauto.
    apply possible_crash_mem_match; auto.
    eapply possible_crash_trans.
    eauto.
    eapply mem_pred_possible_crash_trans; eauto.
  Qed.


  Lemma write_ok_xcrash : forall (F : @pred _ addr_eq_dec _) a vold vraw mm cs d raw v,
    (F * a |-> vold)%pred d ->
    (mem_pred (cachepred mm) (mem_except d a) * a |-> vraw)%pred raw ->
    incl (vsmerge vraw) (vsmerge vold) ->
    crash_xform (RCache.rep cs raw) =p=>
    crash_xform (exists wcs' d', rep wcs' d' * [[ (F * a |-> (v, vsmerge vold))%pred d' ]]).
  Proof.
    unfold rep; intros.
    rewrite RCache.crash_xform_rep; cancel.
    xform_normr; cancel. xform_normr; cancel.
    instantiate (1 := upd raw a (v, vsmerge (vold_cur, vold_old))).
    eassign (Build_wbcachestate (RCache.cache0 (CSMaxCount cs'))
                                (Map.remove a mm)); simpl.
    rewrite <- RCache.crash_xform_rep_r; eauto.
    eapply possible_crash_ptsto_upd_incl; eauto.
    apply incl_tl; eauto.
    eapply pimpl_trans; [ apply pimpl_refl | simpl | eapply ptsto_upd; pred_apply; cancel ].
    rewrite <- mem_pred_absorb.
    unfold cachepred at 3.
    rewrite MapFacts.remove_eq_o by reflexivity.
    rewrite mem_pred_pimpl_except; cancel.
    apply cachepred_remove_invariant; auto.
    apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
  Qed.


  Theorem write_ok : forall wcs a v,
    {< d (F : rawpred) v0,
    PRE
      rep wcs d * [[ (F * a |-> v0)%pred d ]]
    POST RET:wcs
      exists d', rep wcs d' * [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    XCRASH
      exists wcs' d', rep wcs' d' *
      [[ (F * a |-> (v, vsmerge v0))%pred d' ]]
    >} write a v wcs.
  Proof.
    unfold write, rep; intros.
    destruct (Map.find a (WbBuf wcs)) eqn: Heq.
    - prestep; norml.
      denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heq in Hx; destruct_lift Hx.
      cancel; subst.

      step.
      pred_apply. rewrite <- mem_pred_absorb. subst; simpl.
      unfold cachepred at 3. rewrite MapFacts.add_eq_o by reflexivity. cancel.
      apply mem_pred_pimpl_except. intros; apply cachepred_add_invariant; auto.
      eassign (w :: dummy); unfold vsmerge; simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      (* crash *)
      eapply pimpl_trans; [ | eapply H1 ]; cancel; subst.
      eapply write_ok_xcrash; eauto.
      apply incl_tl; apply incl_appr; apply incl_refl.

    - prestep; norml.
      denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heq in Hx; destruct_lift Hx.
      cancel; subst.

      step.
      subst; simpl.
      pred_apply.
      rewrite <- mem_pred_absorb with (a:=a). unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by auto. cancel.
      apply mem_pred_pimpl_except. intros; apply cachepred_add_invariant; auto.
      eassign (@nil valu); simpl.
      apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.

      eapply pimpl_trans; [ | eapply H1 ]; cancel; subst.
      eapply write_ok_xcrash; eauto.
      apply incl_refl. 

      Unshelve.
      all: try exact addr; try exact addr_eq_dec; try exact empty_mem.
      all: exact (fun a b => emp).
  Qed.


  Lemma sync_ok_xcrash : forall (F : @pred _ addr_eq_dec _) a vold vraw mm cs d raw,
    (F * a |-> vold)%pred d ->
    (mem_pred (cachepred mm) (mem_except d a) * a |-> vraw)%pred raw ->
    incl (vsmerge vraw) (vsmerge vold) ->
    crash_xform (RCache.rep cs raw) =p=>
    crash_xform (exists wcs' d', rep wcs' d' * [[ (F * a |-> vold)%pred d' ]]).
  Proof.
    unfold rep; intros.
    rewrite RCache.crash_xform_rep; cancel.
    xform_normr; cancel. xform_normr; cancel.
    instantiate (1 := upd raw a (vold_cur, vold_old)).
    eassign (Build_wbcachestate (RCache.cache0 (CSMaxCount cs'))
                                (Map.remove a mm)); simpl.
    rewrite <- RCache.crash_xform_rep_r; eauto.
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


  Lemma mem_pred_cachepred_remove_mem_except : forall i mm (d : @Mem.mem _ addr_eq_dec _),
    mem_pred (cachepred mm) (mem_except d i) =p=>
    mem_pred (cachepred (Map.remove i mm)) (mem_except d i).
  Proof.
    unfold mem_pred; intros.
    cancel; eauto.

    revert mm i d H H2.
    generalize dependent hm_avs.
    induction hm_avs; intros; auto.

    inversion H; destruct a; subst; simpl in *.
    destruct (addr_eq_dec n i); subst.
    cbn in H2.
    apply equal_f with (x := i) in H2.
    rewrite mem_except_eq in H2.
    rewrite upd_eq in H2; congruence.

    unfold mem_pred_one at 1 3; simpl.
    rewrite <- cachepred_remove_invariant; eauto; cancel.
    eapply IHhm_avs; eauto.
    eassign (mem_except d n).
    rewrite mem_except_comm.
    rewrite H2; cbn.
    rewrite <- mem_except_upd.
    rewrite <- notindomain_mem_eq; auto.
    apply avs2mem_notindomain; auto.
  Qed.

  Theorem evict_ok : forall wcs a,
    {< d (F : rawpred) v vs,
    PRE
      rep wcs d * [[ (F * a |-> (v, vs))%pred d ]]
    POST RET:wcs exists d' vs',
      rep wcs d' * [[ incl vs' vs ]] *
      [[ (F * a |-> (v, vs'))%pred d' ]]
    XCRASH
      exists wcs' d', rep wcs' d' *
      [[ (F * a |-> (v, vs))%pred d' ]]
    >} evict a wcs.
  Proof.
    unfold evict, rep.
    intros.
    prestep.
    - norml.
      denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heqo in Hx.
      destruct_lift Hx; cancel.

      safestep.
      rewrite <- mem_pred_absorb with (a := a).
      3: apply sep_star_comm; eapply ptsto_upd; apply sep_star_comm; eauto.
      unfold cachepred at 3.
      rewrite MapFacts.remove_eq_o by auto; cancel.
      apply mem_pred_cachepred_remove_mem_except.
      apply incl_appr; apply incl_refl.

      cancel.
      xcrash_rewrite.
      eapply sync_ok_xcrash; eauto.
      apply incl_tl; apply incl_appr; apply incl_refl.

      xcrash_rewrite.
      eapply sync_ok_xcrash; eauto.
      apply incl_cons2; apply incl_appr; apply incl_refl.

    - norml.
      denote! (mem_pred _ _ _) as Hx.
      eapply mem_pred_extract in Hx; [ | eapply ptsto_valid'; eauto ].
      unfold cachepred at 2 in Hx; rewrite Heqo in Hx.
      destruct_lift Hx; cancel.

      step.
      pred_apply; subst.
      eapply pimpl_trans2.
      apply mem_pred_absorb_nop with (a := a).
      eapply ptsto_valid'; eauto.
      unfold cachepred at 3.
      rewrite Heqo; cancel.

      xcrash_rewrite.
      eapply sync_ok_xcrash; eauto.
      apply incl_refl.

    Unshelve.
    all: try exact addr; try exact addr_eq_dec; try exact empty_mem.
    all: exact (fun a b => emp).
  Qed.


  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_}} progseq (evict _ _) _) => apply evict_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.


  Definition read_array T a i cs rx : prog T :=
    r <- read (a + i) cs;
    rx r.

  Definition write_array T a i v cs rx : prog T :=
    cs <- write (a + i) v cs;
    rx cs.

  Definition evict_array T a i cs rx : prog T :=
    cs <- evict (a + i) cs;
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
    pred_apply; cancel.
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
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a (vsupd vs i v))%pred d' ]]
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

    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    rewrite H0.
    do 3 (xform_norm; cancel).
    rewrite <- surjective_pairing.
    setoid_rewrite arrayN_isolate with (i := i) (default := ($0, nil)) at 3.
    rewrite selN_updN_eq by auto.
    rewrite firstn_updN_oob by auto.
    simpl; rewrite skipn_updN by auto.
    cancel.
    rewrite length_updN; auto.
  Qed.


  Theorem evict_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      rep cs d
    XCRASH
      exists cs', rep cs' d
    >} evict_array a i cs.
  Proof.
    unfold evict_array.
    hoare.
    pred_apply; cancel.
    rewrite isolateN_fwd with (i:=i) by auto.
    rewrite <- surjective_pairing.
    cancel.

  Grab Existential Variables.
    exact ($0, nil).
  Qed.


  Theorem sync_array_ok : forall a i cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ i < length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync vs i))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' * [[ (F * arrayN a vs)%pred d' ]]
    >} sync_array a i cs.
  Proof.
    unfold sync_array, vssync.
    hoare.

    pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite RCache.ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    rewrite H0.
    do 3 (xform_norm; cancel).
    setoid_rewrite arrayN_isolate at 3; eauto.
    rewrite <- surjective_pairing; cancel.
  Qed.


  Hint Extern 1 ({{_}} progseq (read_array _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_array _ _ _ _) _) => apply write_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (evict_array _ _ _) _) => apply evict_array_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_array _ _ _) _) => apply sync_array_ok : prog.




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

  Definition evict_range T a nr cs rx : prog T :=
    let^ (cs) <- ForN i < nr
    Ghost [ crash d ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant rep cs d
    OnCrash crash
    Begin
      cs <- evict_array a i cs;
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


  Definition evict_vecs T a l cs rx : prog T :=
    let^ (cs) <- ForN i < length l
    Ghost [ crash d ]
    Loopvar [ cs ]
    Continuation lrx
    Invariant rep cs d
    OnCrash crash
    Begin
      cs <- evict_array a (selN l i 0) cs;
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



  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.

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
    safestep. auto.
    safestep.
    step; subst.

    rewrite firstn_S_selN_expand with (def := $0).
    rewrite fold_left_app; simpl.
    erewrite selN_map by omega; auto.
    rewrite map_length; omega.
    all: step.

    Unshelve. exact tt. eauto.
  Qed.


  Lemma mem_pred_cachepred_add_mem_except : forall i v mm (d : @Mem.mem _ addr_eq_dec _),
    mem_pred (cachepred mm) (mem_except d i) =p=>
    mem_pred (cachepred (Map.add i v mm)) (mem_except d i).
  Proof.
    unfold mem_pred; intros.
    cancel; eauto.

    revert mm i v d H H2.
    generalize dependent hm_avs.
    induction hm_avs; intros; auto.

    inversion H; destruct a; subst; simpl in *.
    destruct (addr_eq_dec n i); subst.
    cbn in H2.
    apply equal_f with (x := i) in H2.
    rewrite mem_except_eq in H2.
    rewrite upd_eq in H2; congruence.

    unfold mem_pred_one at 1 3; simpl.
    rewrite <- cachepred_add_invariant; eauto; cancel.
    eapply IHhm_avs; eauto.
    eassign (mem_except d n).
    rewrite mem_except_comm.
    rewrite H2; cbn.
    rewrite <- mem_except_upd.
    rewrite <- notindomain_mem_eq; auto.
    apply avs2mem_notindomain; auto.
  Qed.


  Lemma mem_pred_cachepred_add : forall mm (d : @Mem.mem _ addr_eq_dec _) i v v0,
    d i = Some v0 ->
    mem_pred (cachepred mm) d =p=>
    mem_pred (cachepred (Map.add i v mm)) (Mem.upd d i (v, vsmerge v0)).
  Proof.
    intros.
    rewrite mem_pred_extract by eauto.
    rewrite <- mem_pred_absorb.
    unfold cachepred at 4.
    rewrite MapFacts.add_eq_o by auto.

    unfold cachepred at 2.
    destruct (Map.find i mm) eqn: Heq.
    cancel.
    apply mem_pred_cachepred_add_mem_except.
    unfold vsmerge at 1; simpl.
    rewrite app_comm_cons; eauto.

    cancel.
    apply mem_pred_cachepred_add_mem_except.
    rewrite app_nil_l; auto.
  Qed.


  Theorem write_range_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ length l <= length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_range vs l))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a (vsupd_range vs l))%pred d' ]]
    >} write_range a l cs.
  Proof.
    unfold write_range; intros.
    safestep. auto.
    prestep; unfold rep; cancel.

    apply mem_pred_cachepred_add.
    eapply arrayN_selN; eauto; try omega.
    rewrite vsupd_range_length; try omega.
    rewrite firstn_length_l; omega.

    erewrite firstn_S_selN_expand by omega.
    setoid_rewrite <- vsupd_range_progress; auto.
    replace (a + m - a) with m by omega.
    apply arrayN_updN_memupd; eauto.
    rewrite vsupd_range_length; try omega.
    rewrite firstn_length_l; omega.

    step.
    rewrite firstn_oob; auto.

    (* crashes *)
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    Unshelve. exact tt.
  Qed.

  Theorem evict_range_ok : forall a nr cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ nr <= length vs ]]
    POST RET:cs
      rep cs d
    XCRASH
      exists cs', rep cs' d
    >} evict_range a nr cs.
  Proof.
    unfold evict_range; intros.
    safestep. auto.
    safestep.
    step; subst.

    (* XXX need an XCRASH version of the loop crash invariant? *)
    admit.

    step.

    (* XXX need an XCRASH version of the loop crash invariant? *)
    admit.
  Admitted.



  Section MEM_REGION.

    Variable V : Type.
    Implicit Types m ma mb : @Mem.mem _ addr_eq_dec V.

    Definition region_filled m st n :=
      forall a, a >= st -> a < st + n -> m a <> None.

    Lemma region_filled_sel : forall m st n a,
      region_filled m st n ->
      a >= st -> a < st + n ->
      exists v, m a = Some v.
    Proof.
      intros.
      specialize (H a H0 H1).
      destruct (m a); try congruence.
      eexists; eauto.
    Qed.

    Lemma listupd_region_filled : forall l m a,
      region_filled (listupd m a l) a (length l).
    Proof.
      unfold region_filled; destruct l; simpl; intros.
      omega.
      destruct (addr_eq_dec a a0); subst.
      rewrite listupd_sel_oob by omega.
      rewrite upd_eq; congruence.
      erewrite listupd_sel_inb with (def := v) by omega.
      congruence.
    Qed.

    Lemma arrayN_region_filled : forall l m a F,
      (F * arrayN a l)%pred m ->
      region_filled m a (length l).
    Proof.
      unfold region_filled; induction l; simpl; intros.
      omega.
      destruct (addr_eq_dec a1 a0); subst.
      apply sep_star_comm in H; apply sep_star_assoc in H.
      apply ptsto_valid in H; congruence.
      apply sep_star_assoc in H.
      eapply IHl; eauto; omega.
    Qed.

    Lemma mem_match_listupd_l : forall l ma mb a,
      mem_match ma mb ->
      region_filled mb a (length l) ->
      mem_match (listupd ma a l) mb.
    Proof.
      induction l; simpl; auto; intros.
      apply IHl.
      eapply region_filled_sel in H0; eauto.
      destruct H0.
      eapply mem_match_upd_l; eauto.
      omega.
      unfold region_filled in *; intuition.
      eapply H0 with (a := a1); try omega; auto.
    Qed.

  End MEM_REGION.


  Section MEM_INCL.

    Implicit Types m ma mb : rawdisk.

    Definition mem_incl ma mb := forall a,
      (ma a = None /\ mb a = None) \/
      exists va vb, ma a = Some va /\ mb a = Some vb /\
      incl (vsmerge va) (vsmerge vb).

    Lemma mem_incl_refl : forall m,
      mem_incl m m.
    Proof.
      unfold mem_incl; intros.
      destruct (m a) eqn: Heq; intuition.
      right; do 2 eexists; intuition.
    Qed.

    Lemma mem_incl_trans : forall m ma mb,
      mem_incl ma m ->
      mem_incl m mb ->
      mem_incl ma mb.
    Proof.
      unfold mem_incl; intuition.
      specialize (H a); specialize (H0 a).
      intuition; repeat deex; try congruence.
      right.
      rewrite H1 in H0; inversion H0; subst.
      do 2 eexists; intuition eauto.
      eapply incl_tran; eauto.
    Qed.

    Lemma mem_pred_cachepred_mem_incl : forall mm ma mb ,
      @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (cachepred mm) mb ma ->
      mem_incl ma mb.
    Proof.
      intros.
      intro a.
      destruct (mb a) eqn: ?.
      eapply mem_pred_extract in H; eauto.
      right.
      unfold cachepred in H at 2.
      destruct (Map.find a mm) eqn: Heq.
      - destruct_lift H; destruct_pair_eq; subst.
        do 2 eexists; split.
        eapply ptsto_valid'; eauto.
        split; eauto.
        apply incl_tl; apply incl_appr; apply incl_refl.
      - do 2 eexists; intuition.
        eapply ptsto_valid'; eauto.
      - left; intuition.
        eapply mem_pred_cachepred_none; eauto.
    Qed.

    Lemma possible_crash_incl_trans : forall m ma mb,
      possible_crash ma m ->
      mem_incl ma mb ->
      possible_crash mb m.
    Proof.
      unfold possible_crash, mem_incl; intros.
      specialize (H a); specialize (H0 a).
      intuition; repeat deex; try congruence.
      right.
      rewrite H2 in H0; inversion H0; subst.
      do 2 eexists; intuition eauto.
    Qed.

    Lemma mem_incl_upd : forall a va vb ma mb,
      mem_incl ma mb ->
      incl (vsmerge va) (vsmerge vb) ->
      mem_incl (upd ma a va) (upd mb a vb).
    Proof.
      unfold mem_incl; intros.
      specialize (H a0).
      destruct (addr_eq_dec a a0); subst.
      repeat rewrite upd_eq by auto.
      intuition; repeat deex; intuition.
      right; do 2 eexists; eauto.
      right; do 2 eexists; eauto.
      repeat rewrite upd_ne by auto.
      intuition.
    Qed.

    Lemma mem_incl_listupd : forall la lb,
      Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) la lb ->
      forall ma mb st,
      mem_incl ma mb ->
      mem_incl (listupd ma st la) (listupd mb st lb).
    Proof.
      induction 1; simpl; intros; auto.
      apply IHForall2.
      apply mem_incl_upd; auto.
    Qed.

  End MEM_INCL.



  Lemma synced_range_ok_xcrash : forall vs n mm (d raw : @Mem.mem _ addr_eq_dec _) F st m,
    mem_pred (cachepred mm) d raw ->
    (F * arrayN st (vssync_range vs n))%pred d ->
    possible_crash raw m ->
    n < length vs ->
    exists raw', 
    mem_pred (cachepred (Map.empty _)) (listupd d st vs) raw' /\
    possible_crash raw' m.
  Proof.
    intros.
    exists (listupd d st vs); split.

    eapply mem_pred_cachepred_refl.
    eauto.
    apply mem_match_listupd_l.
    apply mem_match_refl.
    erewrite <- vssync_range_length.
    eapply arrayN_region_filled; eauto.
    omega.

    eapply possible_crash_incl_trans; eauto.
    eapply mem_incl_trans.
    eapply mem_pred_cachepred_mem_incl; eauto.
    rewrite arrayN_listupd_eq at 1 by eauto.
    apply mem_incl_listupd.
    apply vssync_range_incl; auto.
    apply mem_incl_refl.
  Qed.


  Theorem sync_range_ok : forall a n cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] * [[ n <= length vs ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_range vs n))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a vs)%pred d' ]]
    >} sync_range a n cs.
  Proof.

    unfold sync_range; intros.
    safestep. auto.
    prestep; unfold rep; cancel.
    rewrite vssync_range_length; omega.

    prestep; unfold rep; cancel.
    apply arrayN_unify.
    apply vssync_range_progress; omega.

    (* crashes *)
    subst.
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    denote crash_xform as Hx; rewrite Hx.
    unfold rep; xform_norm.
    rewrite RCache.crash_xform_rep by eauto.
    cancel.

    edestruct (synced_range_ok_xcrash); eauto. omega.
    repeat deex.
    do 2 (xform_norm; cancel); xform_norm.
    eassign (Build_wbcachestate (RCache.cache0 (CSMaxCount cs')) (Map.empty _)); simpl.
    rewrite <- RCache.crash_xform_rep_r.
    cancel.
    eauto. eauto.
    eapply arrayN_listupd; eauto.
    rewrite vssync_range_length; omega.

    step.
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    Unshelve. exact tt.
  Qed.



  Hint Extern 0 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.
  Hint Extern 0 (okToUnify (arrayN ?a _) (arrayN ?a _)) => constructor : okToUnify.

  Local Hint Resolve vsupd_vecs_length_ok.
  Local Hint Resolve vssync_vecs_length_ok.

  Theorem write_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => fst e < length vs) l ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vsupd_vecs vs l))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a (vsupd_vecs vs l))%pred d' ]]
    >} write_vecs a l cs.
  Proof.
    unfold write_vecs.
    safestep. auto.
    prestep; unfold rep; cancel.

    apply mem_pred_cachepred_add.
    eapply arrayN_selN; eauto; try omega.
    rewrite vsupd_vecs_length; try omega.
    apply Nat.add_lt_mono_l.
    eapply lt_le_trans. apply vsupd_vecs_length_ok; eauto.
    rewrite vsupd_vecs_length; auto.

    erewrite firstn_S_selN_expand by auto.
    setoid_rewrite vsupd_vecs_app; simpl.
    rewrite minus_plus.
    apply arrayN_updN_memupd; auto.

    step.
    rewrite firstn_oob; auto.

    (* crashes *)
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    Unshelve. exact tt.
  Qed.



  Lemma synced_vecs_ok_xcrash : forall vs l mm (d raw : @Mem.mem _ addr_eq_dec _) F st m,
    mem_pred (cachepred mm) d raw ->
    (F * arrayN st (vssync_vecs vs l))%pred d ->
    possible_crash raw m ->
    Forall (fun a => a < length vs) l ->
    exists raw',
    mem_pred (cachepred (Map.empty _)) (listupd d st vs) raw' /\
    possible_crash raw' m.
  Proof.
    intros.
    exists (listupd d st vs); split.

    eapply mem_pred_cachepred_refl.
    eauto.
    apply mem_match_listupd_l.
    apply mem_match_refl.
    erewrite <- vssync_vecs_length.
    eapply arrayN_region_filled; eauto.

    eapply possible_crash_incl_trans; eauto.
    eapply mem_incl_trans.
    eapply mem_pred_cachepred_mem_incl; eauto.
    rewrite arrayN_listupd_eq at 1 by eauto.
    apply mem_incl_listupd.
    apply vssync_vecs_incl; auto.
    apply mem_incl_refl.
  Qed.


  Theorem sync_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l ]]
    POST RET:cs
      exists d', rep cs d' *
      [[ (F * arrayN a (vssync_vecs vs l))%pred d' ]]
    XCRASH
      exists cs' d', rep cs' d' *
      [[ (F * arrayN a vs)%pred d' ]]
    >} sync_vecs a l cs.
  Proof.
    unfold sync_vecs.
    safestep. auto.
    prestep; unfold rep; cancel; auto.

    prestep; unfold rep; cancel.
    apply arrayN_unify.
    apply vssync_vecs_progress; omega.

    (* crashes *)
    subst.
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    denote crash_xform as Hx; rewrite Hx.
    unfold rep; xform_norm.
    rewrite RCache.crash_xform_rep by eauto.
    cancel.

    edestruct (synced_vecs_ok_xcrash); eauto; intuition.
    apply forall_firstn; auto.
    do 2 (xform_norm; cancel); xform_norm.
    eassign (Build_wbcachestate (RCache.cache0 (CSMaxCount cs')) (Map.empty _)); simpl.
    rewrite <- RCache.crash_xform_rep_r.
    cancel. eauto. eauto.
    eapply arrayN_listupd; eauto.
    rewrite vssync_vecs_length; omega.

    step.
    rewrite firstn_oob; auto.
    eapply pimpl_trans; [ | eapply H1 ]; cancel.
    Unshelve. exact tt.
  Qed.

  Theorem evict_vecs_ok : forall a l cs,
    {< d F vs,
    PRE
      rep cs d * [[ (F * arrayN a vs)%pred d ]] *
      [[ Forall (fun e => e < length vs) l ]]
    POST RET:cs
      rep cs d
    XCRASH
      exists cs', rep cs' d
    >} evict_vecs a l cs.
  Proof.
    unfold evict_vecs.
    safestep. auto.
    admit.
    step.
    (* XXX need an XCRASH version of the For loop? *)
    admit.
  Admitted.


  Hint Extern 1 ({{_}} progseq (read_range _ _ _ _ _) _) => apply read_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_range _ _ _) _) => apply write_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (evict_range _ _ _) _) => apply evict_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_range _ _ _) _) => apply sync_range_ok : prog.
  Hint Extern 1 ({{_}} progseq (write_vecs _ _ _) _) => apply write_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (evict_vecs _ _ _) _) => apply evict_vecs_ok : prog.
  Hint Extern 1 ({{_}} progseq (sync_vecs _ _ _) _) => apply sync_vecs_ok : prog.


  Definition init T (cachesize : nat) (rx : wbcachestate -> prog T) : prog T :=
    cs <- RCache.init cachesize;
    rx (Build_wbcachestate cs (Map.empty _)).

  Definition init_load := init.
  Definition init_recover := init.

  Theorem init_recover_ok : forall cachesize,
    {< d F,
    PRE
      exists cs, rep cs d *
      [[ F d ]] * [[ cachesize <> 0 ]]
    POST RET:cs
      exists d', rep cs d' * [[ (crash_xform F) d' ]]
    CRASH
      exists cs, rep cs d
    >} init_recover cachesize.
  Proof.
    unfold init_recover, init, rep.
    intros; eapply pimpl_ok2.
    apply RCache.init_recover_ok.

    intros; xform_norm.
    cancel.
    eauto.

    prestep.  norm. cancel.
    intuition.

    (** XXX:
        Cannot construct such a ?d'0.
        crash_xform F ?d'0 requires ?d'0 to be fully-synced,
        but d' might be unsynced.

        maybe saying [[ (crash_xform F) ?d'0 ]] is too strong.
        we can only say d' is a subset of d.
     *)
    admit.
    admit.

    pimpl_crash; xform_norm.
    cancel.
    eassign (Build_wbcachestate cs0 (WbBuf cs)).
    cancel.
    eauto.
  Admitted.


  Theorem init_recover_xform_ok : forall cachesize,
    {< d F,
    PRE
      exists cs, crash_xform (rep cs d) *
      [[ F d ]] * [[ cachesize <> 0 ]]
    POST RET:cs
      exists d', rep cs d' * [[ (crash_xform F) d' ]]
    CRASH
      exists cs, crash_xform (rep cs d)
    >} init_recover cachesize.
  Proof.
    unfold init_recover, init, rep.
    intros; eapply pimpl_ok2.
    apply RCache.init_recover_xform_ok.

    intros; xform_norm.
    cancel.
    eauto.

    prestep; xform_norm.
    denote crash_xform as Hx.
    apply xform_mem_pred_cachepred in Hx.
    destruct_lift Hx.
    cancel.
    unfold pimpl; intros.
    eapply crash_xform_apply; eauto.

    pimpl_crash; xform_norm.
    rewrite RCache.crash_xform_rep.
    cancel.
    eassign (Build_wbcachestate (RCache.cache0 (CSMaxCount cs')) (WbBuf cs)).
    xform_normr; simpl.
    rewrite <- RCache.crash_xform_rep_r.
    cancel; eauto.
    auto.
  Qed.


End WBCache.

Global Opaque WBCache.write_array.
Global Opaque WBCache.read_array.
Global Opaque WBCache.sync_array.

