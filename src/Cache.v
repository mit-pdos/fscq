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


Module Map := FMapAVL.Make(Nat_as_OT).
Module MapFacts := WFacts_fun Nat_as_OT Map.
Module MapProperties := WProperties_fun Nat_as_OT Map.

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

Module BUFCACHE.

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
    Sync a;;
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

  Definition init T (cachesize : nat) (rx : cachestate -> prog T) : prog T :=
    rx (Build_cachestate (Map.empty valu) 0 cachesize eviction_init).

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

  Lemma mapsto_add : forall a v v' (m : Map.t valu),
    Map.MapsTo a v (Map.add a v' m) -> v' = v.
  Proof.
    intros.
    apply Map.find_1 in H.
    erewrite Map.find_1 in H by (apply Map.add_1; auto).
    congruence.
  Qed.

  Lemma map_remove_cardinal : forall V (m : Map.t V) k, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.remove k m) = Map.cardinal m - 1.
  Proof.
    intros; deex.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m) (m':=m) (x:=k) (e:=v).
    omega.
    apply Map.remove_1; auto.
    intro.
    destruct (Nat_as_OT.eq_dec k y); subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma map_add_cardinal : forall V (m : Map.t V) k v, ~ (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m + 1.
  Proof.
    intros.
    erewrite MapProperties.cardinal_2 with (m:=m).
    omega.
    eauto.
    intro.
    reflexivity.
  Qed.

  Lemma map_add_dup_cardinal' : forall V (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal (Map.remove k m) + 1.
  Proof.
    intros; deex.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    omega.
    apply Map.remove_1; auto.
    intro.
    destruct (Nat_as_OT.eq_dec k y); subst.
    - rewrite MapFacts.add_eq_o; auto.
      rewrite MapFacts.add_eq_o; auto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.add_neq_o; try omega.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma map_add_dup_cardinal : forall V (m : Map.t V) k v, (exists v, Map.MapsTo k v m) ->
    Map.cardinal (Map.add k v m) = Map.cardinal m.
  Proof.
    intros.
    replace (Map.cardinal m) with ((Map.cardinal m - 1) + 1).
    erewrite <- map_remove_cardinal; eauto.
    apply map_add_dup_cardinal'; auto.
    deex.
    assert (Map.cardinal m <> 0); try omega.
    erewrite MapProperties.cardinal_2 with (m:=Map.remove k m).
    omega.
    apply Map.remove_1; reflexivity.
    intro.
    destruct (Nat_as_OT.eq_dec k y); subst.
    - rewrite MapFacts.add_eq_o; auto.
      erewrite Map.find_1; eauto.
    - rewrite MapFacts.add_neq_o; auto.
      rewrite MapFacts.remove_neq_o; auto.
  Qed.

  Lemma map_elements_hd_in : forall V (m : Map.t V) k w l,
    Map.elements m = (k, w) :: l ->
    Map.In k m.
  Proof.
    intros.
    eexists; apply Map.elements_2.
    rewrite H.
    apply InA_cons_hd.
    constructor; eauto.
  Qed.

  Hint Resolve Map.remove_3.
  Hint Resolve Map.add_3.
  Hint Resolve Map.find_2.
  Hint Resolve mapsto_add.

  Ltac unfold_rep := unfold rep.

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
    unfold maybe_evict, rep; hoare.
    rewrite map_remove_cardinal; eauto.
    replace (CSCount cs) with (CSMaxCount cs) in * by omega.
    rewrite Map.cardinal_1 in *. rewrite Heql in *; simpl in *; omega.
    rewrite map_remove_cardinal by (eapply map_elements_hd_in; eauto); eauto.
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
    hoare_unfold unfold_rep.

    apply ptsto_valid' in H3 as H'.
    apply Map.find_2 in Heqo. apply H12 in Heqo. rewrite H' in Heqo. deex; congruence.

    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.

    rewrite <- diskIs_combine_same with (m:=d) (a:=a); try pred_apply; cancel.

    rewrite map_add_cardinal; auto.
    intro Hm; destruct Hm as [? Hm]. apply Map.find_1 in Hm. congruence.

    apply ptsto_valid' in H3 as H'.
    destruct (addr_eq_dec a a0); subst.
    apply mapsto_add in H; subst; eauto.
    edestruct H12. eauto. eexists; eauto.
    simpl in *; auto.

    rewrite <- diskIs_combine_same with (m:=d); try pred_apply; cancel.
    eauto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (read _ _) _) => apply read_ok : prog.

  Theorem write_ok : forall cs a v,
    {< d (F : rawpred) v0,
    PRE
      rep cs d * [[ (F * a |-> v0)%pred d ]]
    POST RET:cs
      exists d',
      rep cs d' * [[ (F * a |-> (v, valuset_list v0))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * a |-> (v, valuset_list v0))%pred d' ]]
    >} write a v cs.
  Proof.
    unfold write.
    hoare_unfold unfold_rep.

    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    destruct (Map.find a (CSMap r_)) eqn:Hfind; hoare.

    rewrite <- diskIs_combine_upd with (m:=d) (a:=a); try pred_apply; cancel.
    rewrite map_add_dup_cardinal; eauto.
    destruct (addr_eq_dec a a0); subst.
    apply mapsto_add in H; subst.
    rewrite upd_eq by auto. eauto.
    apply Map.add_3 in H; auto.
    rewrite upd_ne by auto. auto.

    apply sep_star_comm; apply sep_star_comm in H3.
    eapply ptsto_upd; pred_apply; cancel.

    rewrite <- diskIs_combine_upd with (m:=d) (a:=a); cancel.
    rewrite map_add_cardinal; eauto.
    intro Hm; destruct Hm as [? Hm]. apply Map.find_1 in Hm. congruence.

    destruct (addr_eq_dec a a0); subst.
    apply mapsto_add in H; subst.
    rewrite upd_eq by auto. eauto.
    apply Map.add_3 in H; auto.
    rewrite upd_ne by auto. auto.

    apply sep_star_comm; apply sep_star_comm in H3.
    eapply ptsto_upd; pred_apply; cancel.

    cancel.
    instantiate (cs' := r_).
    apply pimpl_or_r. left. cancel.
    rewrite <- diskIs_combine_same with (m:=d); try pred_apply; cancel.
    eauto.
    cancel.

    apply pimpl_or_r. left. cancel; eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (write _ _ _) _) => apply write_ok : prog.

  Theorem sync_ok : forall a cs,
    {< d (F : rawpred) v,
    PRE
      rep cs d * [[ (F * a |-> v)%pred d ]]
    POST RET:cs
      exists d', rep cs d' * [[ (F * a |-> (fst v, nil))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * a |-> (fst v, nil))%pred d' ]]
    >} sync a cs.
  Proof.
    unfold sync, rep.
    step.
    rewrite diskIs_extract with (a:=a); try pred_apply; cancel.
    eapply pimpl_ok2; eauto with prog.
    intros; norm.
    instantiate (d' := Mem.upd d a (v2_cur, [])); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.
    intuition.
    apply H5 in H; deex.
    destruct (addr_eq_dec a a0); subst.
    apply sep_star_comm in H3; apply ptsto_valid in H3.
    rewrite H3 in H. inversion H. subst.
    rewrite upd_eq by auto. eexists. eauto.
    rewrite upd_ne by auto. eexists. eauto.
    apply sep_star_comm. eapply ptsto_upd. apply sep_star_comm. eauto.
    cancel.
    apply pimpl_or_r; left.
    rewrite <- diskIs_combine_same with (m:=d) (a:=a); try pred_apply; cancel.
    eauto.
    eauto.
    eauto.
    eauto.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync _ _) _) => apply sync_ok : prog.

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
    instantiate (d' := Mem.upd d a (v0_cur, v0_old)); unfold stars; simpl.
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
    instantiate (d' := Mem.upd d a (v0_cur, v0_old)); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.
    intuition.

    destruct (addr_eq_dec a a0).
    apply MapProperties.F.find_mapsto_iff in H0. congruence.
    rewrite upd_ne by eauto. eauto.

    assert ((a |-> (v0_cur, v0_old) * F)%pred (Mem.upd d a (v0_cur, v0_old))).
    eapply ptsto_upd. pred_apply; cancel.
    pred_apply; cancel.

    pimpl_crash. norm.
    instantiate (d' := Mem.upd d a (v0_cur, v0_old)); unfold stars; simpl.
    rewrite <- diskIs_combine_upd with (m:=d); cancel.

    intuition.
    instantiate (cs' := Build_cachestate (Map.empty valu) 0 (CSMaxCount cs) eviction_init).
    all: simpl in *; eauto; try omega.
    apply MapProperties.F.empty_mapsto_iff in H; exfalso; eauto.

    assert ((a |-> (v0_cur, v0_old) * F)%pred (Mem.upd d a (v0_cur, v0_old))).
    eapply ptsto_upd. pred_apply; cancel.
    pred_apply; cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (trim _ _) _) => apply trim_ok : prog.

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
    norm; cancel'; intuition.
    unfold stars; subst; simpl; rewrite star_emp_pimpl.
    unfold pimpl; intros; exists m.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    congruence.
    omega.
    intros.
    contradict H0; apply Map.empty_1.
  Qed.

  Hint Extern 1 ({{_}} progseq (init_load _) _) => apply init_load_ok : prog.

  Theorem init_recover_ok : forall cachesize,
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
    norm; cancel'; intuition.
    unfold stars; subst; simpl; rewrite star_emp_pimpl.
    unfold crash_xform. unfold pimpl; intros; repeat deex. exists m.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    apply sep_star_lift_apply'; eauto.
    congruence.
    omega.
    intros.
    contradict H; apply Map.empty_1.
    destruct_lift H0.
    unfold diskIs in *; subst.
    exists m'.
    intuition.
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
      [[ (F * arrayN a (upd_prepend vs i v))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * arrayN a (upd_prepend vs i v))%pred d' ]]
    >} write_array a i v cs.
  Proof.
    unfold write_array, upd_prepend.
    hoare.

    pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    cancel.
    apply pimpl_or_r; left; cancel.

    cancel.
    apply pimpl_or_r; right; cancel.
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
      [[ (F * arrayN a (upd_sync vs i ($0, nil)))%pred d' ]]
    CRASH
      exists cs', rep cs' d \/
      exists d', rep cs' d' * [[ (F * arrayN a (upd_sync vs i ($0, nil)))%pred d' ]]
    >} sync_array a i cs.
  Proof.
    unfold sync_array, upd_sync.
    hoare.

    pred_apply.
    rewrite isolateN_fwd with (i:=i) by auto. cancel.
    rewrite ptsto_tuple.
    cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    cancel.
    apply pimpl_or_r; left; cancel.

    cancel.
    apply pimpl_or_r; right; cancel.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
  Qed.

  Hint Extern 1 ({{_}} progseq (sync_array _ _ _) _) => apply sync_array_ok : prog.

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

    pred_apply.
    rewrite <- surjective_pairing.
    rewrite isolateN_fwd with (i:=i) by auto. cancel.

    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    pred_apply. cancel.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.

    Grab Existential Variables.
    exact ($0, nil).
  Qed.

  Hint Extern 1 ({{_}} progseq (trim_array _ _ _) _) => apply trim_array_ok : prog.

  Lemma crash_xform_rep: forall cs m,
    crash_xform (rep cs m) =p=> exists m' cs', [[ possible_crash m m' ]] * rep cs' m'.
  Proof.
    unfold rep.
    intros.
    repeat rewrite crash_xform_sep_star_dist.
    rewrite crash_xform_diskIs.
    repeat rewrite crash_xform_lift_empty.
    cancel.
    instantiate (cs' := Build_cachestate (Map.empty valu) 0 (CSMaxCount cs) (CSEvict cs)).
    auto.
    simpl; omega.
    simpl in *; omega.
    inversion H.
  Qed.

  Hint Rewrite crash_xform_rep : crash_xform.

  Hint Extern 0 (okToUnify (rep _ _) (rep _ _)) => constructor : okToUnify.

End BUFCACHE.

Global Opaque BUFCACHE.init.
Global Opaque BUFCACHE.init_load.
Global Opaque BUFCACHE.init_recover.
