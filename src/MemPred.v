Require Import Mem.
Require Import Pred.
Require Import Prog.
Require Import ListPred.
Require Import List.
Require Import SepAuto.
Require Import Array.
Require Import Omega.
Require Import AsyncDisk PredCrash.
Require Import FunctionalExtensionality.


Set Implicit Arguments.
Set Default Proof Using "Type".

Section MemPred.

  Variable LowAT : Type.
  Variable LowAEQ : EqDec LowAT.
  Variable LowV : Type.

  Variable HighAT : Type.
  Variable HighAEQ : EqDec HighAT.
  Variable HighV : Type.

  Definition low_mem := @mem LowAT LowAEQ LowV.
  Definition high_mem := @mem HighAT HighAEQ HighV.

  Definition low_pred := @pred LowAT LowAEQ LowV.
  Definition high_pred := @pred HighAT HighAEQ HighV.


  Fixpoint avs2mem_iter (avs : list (HighAT * HighV)) (m : @mem HighAT HighAEQ HighV) :=
    match avs with
    | nil => m
    | (a, v) :: rest =>
      upd (avs2mem_iter rest m) a v
    end.

  Definition avs2mem avs :=
    avs2mem_iter avs empty_mem.

  Fixpoint avs_except avs victim : @list (HighAT * HighV) :=
    match avs with
    | nil => nil
    | (a, v) :: rest =>
      if HighAEQ a victim then avs_except rest victim else (a, v) :: avs_except rest victim
    end.

  Theorem avs_except_notin_eq : forall avs a,
    ~ In a (map fst avs) -> avs_except avs a = avs.
  Proof.
    induction avs; simpl; intros; auto.
    destruct a; intuition.
    destruct (HighAEQ h a0); subst. intuition.
    f_equal; eauto.
  Qed.

  Theorem avs_except_cons : forall avs a v,
    NoDup (map fst ((a, v) :: avs)) ->
    avs_except ((a, v) :: avs) a = avs.
  Proof.
    intros; simpl.
    destruct (HighAEQ a a); try congruence.
    apply avs_except_notin_eq.
    inversion H; auto.
  Qed.

  Theorem avs2mem_ne : forall avs a v a',
    a <> a' ->
    avs2mem ((a, v) :: avs) a' = avs2mem avs a'.
  Proof.
    unfold avs2mem; simpl; intros.
    rewrite upd_ne; auto.
  Qed.

  Theorem listpred_avs_except : forall avs (lp : _ -> low_pred) a v,
    NoDup (map fst avs) ->
    avs2mem avs a = Some v ->
    listpred lp avs =p=> listpred lp (avs_except avs a) * lp (a, v).
  Proof.
    induction avs; simpl; intros.
    - inversion H0.
    - destruct a.
      destruct (HighAEQ h a0); subst.
      + unfold avs2mem in H0; simpl in H0. rewrite upd_eq in H0 by auto. inversion H0; subst.
        inversion H.
        rewrite avs_except_notin_eq by auto. cancel.
      + inversion H.
        rewrite avs2mem_ne in H0 by auto.
        rewrite IHavs by eauto.
        cancel.
  Qed.

  Theorem avs_except_notin : forall avs a a',
    ~ In a' (map fst avs) -> ~ In a' (map fst (avs_except avs a)).
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    destruct (HighAEQ h a0); subst; eauto.
    simpl in *; intuition; eauto.
  Qed.

  Hint Resolve avs_except_notin.

  Lemma avs2mem_notindomain : forall l a,
    ~ In a (map fst l) ->
    notindomain a (avs2mem l).
  Proof.
    unfold avs2mem, notindomain; induction l; simpl; intros.
    cbv; auto.
    destruct a; simpl in *; intuition.
    rewrite upd_ne; auto.
  Qed.

  Theorem avs_except_nodup : forall avs a,
    NoDup (map fst avs) -> NoDup (map fst (avs_except avs a)).
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    inversion H; subst.
    destruct (HighAEQ h a0); subst; eauto.
    simpl; constructor; eauto.
  Qed.

  Hint Resolve avs_except_nodup.

  Lemma avs2mem_except_eq : forall avs a,
    avs2mem (avs_except avs a) a = None.
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    destruct (HighAEQ h a0); subst; eauto.
    rewrite avs2mem_ne by auto; auto.
  Qed.

  Lemma avs2mem_except_ne : forall avs a a',
    a <> a' ->
    avs2mem (avs_except avs a) a' = avs2mem avs a'.
  Proof.
    induction avs; simpl; intros; eauto.
    destruct a.
    destruct (HighAEQ h a0); subst.
    - rewrite avs2mem_ne; auto.
    - unfold avs2mem in *; simpl.
      destruct (HighAEQ h a'); subst.
      + repeat rewrite upd_eq; auto.
      + repeat rewrite upd_ne; auto.
  Qed.

  Theorem mem_except_avs_except : forall avs a,
    mem_except (avs2mem avs) a = avs2mem (avs_except avs a).
  Proof.
    intros; apply functional_extensionality; intros.
    destruct (HighAEQ a x); subst.
    - rewrite mem_except_eq. rewrite avs2mem_except_eq. auto.
    - rewrite mem_except_ne by auto.
      rewrite avs2mem_except_ne by auto.
      auto.
  Qed.

  Hint Resolve mem_except_avs_except.

  Lemma avs2mem_none_notin : forall avs a,
    avs2mem avs a = None -> ~ In a (map fst avs).
  Proof.
    unfold avs2mem; induction avs; simpl; intros; auto.
    destruct a; intuition; simpl in *; subst.
    rewrite upd_eq in * by auto; congruence.
    destruct (HighAEQ h a0); subst.
    rewrite upd_eq in * by auto; congruence.
    rewrite upd_ne in * by auto; eauto.
  Qed.

  Variable Pred : HighAT -> HighV -> low_pred.

  Definition mem_pred_one (av : HighAT * HighV) : low_pred :=
    Pred (fst av) (snd av).

  Definition mem_pred (hm : high_mem) : low_pred :=
    (exists hm_avs,
     [[ NoDup (map fst hm_avs) ]] *
     [[ hm = avs2mem hm_avs ]] *
     listpred mem_pred_one hm_avs)%pred.

  Theorem mem_pred_extract' : forall hm a v,
    hm a = Some v ->
    mem_pred hm =p=> mem_pred (mem_except hm a) * mem_pred_one (a, v).
  Proof.
    unfold mem_pred; intros.
    cancel.
    eapply listpred_avs_except; subst; eauto.
    eauto.
  Qed.

  Theorem mem_pred_extract : forall hm a v,
    hm a = Some v ->
    mem_pred hm =p=> mem_pred (mem_except hm a) * Pred a v.
  Proof.
    apply mem_pred_extract'.
  Qed.

  Theorem mem_pred_absorb' : forall hm a v,
    mem_pred (mem_except hm a) * mem_pred_one (a, v) =p=> mem_pred (upd hm a v).
  Proof.
    unfold mem_pred; intros.
    norml.
    exists ((a, v) :: hm_avs).
    pred_apply.
    cancel.
    simpl; constructor; auto.
    apply avs2mem_none_notin.
    rewrite <- H3. apply mem_except_eq.
    unfold avs2mem in *; simpl.
    rewrite <- H3.
    rewrite upd_mem_except.
    auto.
  Qed.

  Theorem mem_pred_absorb : forall hm a v,
    mem_pred (mem_except hm a) * Pred a v =p=> mem_pred (upd hm a v).
  Proof.
    apply mem_pred_absorb'.
  Qed.

  Theorem mem_pred_absorb_nop' : forall hm a v,
    hm a = Some v ->
    mem_pred (mem_except hm a) * mem_pred_one (a, v) =p=> mem_pred hm.
  Proof.
    unfold mem_pred; intros.
    norml.
    exists ( (a, v) :: hm_avs).
    pred_apply.
    cancel.
    simpl; constructor; auto.
    apply avs2mem_none_notin.
    rewrite <- H4. apply mem_except_eq.
    unfold avs2mem in *; simpl.
    rewrite <- H4.
    rewrite upd_mem_except.
    rewrite upd_nop; auto.
  Qed.

  Theorem mem_pred_absorb_nop : forall hm a v,
    hm a = Some v ->
    mem_pred (mem_except hm a) * Pred a v =p=> mem_pred hm.
  Proof.
    apply mem_pred_absorb_nop'.
  Qed.

  Theorem mem_pred_empty_mem :
    mem_pred empty_mem <=p=> emp.
  Proof.
    unfold mem_pred, mem_pred_one, avs2mem; split; norm; auto.
    destruct hm_avs; try cancel.
    eapply equal_f with (x := p_1) in H2.
    rewrite upd_eq in H2 by auto.
    unfold empty_mem in H2; congruence.
    instantiate (1 := nil); cancel.
    intuition; constructor.
  Qed.

End MemPred.

Theorem mem_pred_pimpl : forall LA LEQ LV HA HEQ HV hm p1 p2,
  (forall a v, p1 a v =p=> p2 a v) ->
  @mem_pred LA LEQ LV HA HEQ HV p1 hm =p=> mem_pred p2 hm.
Proof.
  unfold mem_pred; intros.
  cancel; eauto.
  subst.
  induction hm_avs; simpl; intros; auto.
  unfold mem_pred_one at 1 3; simpl. rewrite H. cancel.
  eapply IHhm_avs.
  inversion H0; eauto.
Qed.

Theorem mem_pred_pimpl_except : forall LA LEQ LV HA HEQ HV hm p1 p2 a',
  (forall a v, a <> a' -> p1 a v =p=> p2 a v) ->
  @mem_pred LA LEQ LV HA HEQ HV p1 (mem_except hm a') =p=> mem_pred p2 (mem_except hm a').
Proof.
  unfold mem_pred; intros.
  cancel; eauto.
  assert (~ In a' (map fst hm_avs)).
  eapply avs2mem_none_notin. rewrite <- H3. rewrite mem_except_eq. auto.
  clear H3 hm.
  induction hm_avs; simpl; intros; auto.
  unfold mem_pred_one at 1 3; simpl. rewrite H. cancel.
  eapply IHhm_avs; eauto.
  inversion H0; eauto.
  destruct a; firstorder.
Qed.


Theorem mem_pred_absent_hm :
  forall A AEQ LV HV p hm m a,
  m a = None ->
  (forall a v, p a v =p=> exists v', a |-> v') ->
  @mem_pred A AEQ LV A AEQ HV p hm m ->
  hm a = None.
Proof.
  intros.
  case_eq (hm a); intros; auto.
  eapply mem_pred_extract in H1; eauto.
  rewrite H0 in H1; destruct_lift H1.
  apply ptsto_valid' in H1; congruence.
Qed.

Theorem mem_pred_absent_lm :
  forall A AEQ LV HV p hm m a,
  hm a = None ->
  (forall a v, p a v =p=> exists v', a |-> v') ->
  @mem_pred A AEQ LV A AEQ HV p hm m ->
  m a = None.
Proof.
  intros.
  unfold mem_pred, mem_pred_one in H1. destruct_lift H1.
  apply avs2mem_none_notin in H.
  generalize dependent m.
  induction dummy; simpl in *; intros.
  - apply emp_empty_mem_only in H1; subst.
    firstorder.
  - destruct a0; simpl in *.
    rewrite H0 in H1.
    destruct (AEQ a0 a); try solve [ exfalso; eauto ].
    destruct_lift H1.
    generalize dependent H1.
    unfold_sep_star; intros; repeat safedeex.
    inversion H3.
    unfold ptsto, mem_union in H1.
    intuition; subst.
    match goal with
    | [ H : forall _, _ -> m1 _ = None |- _ ] => rewrite H
    end; eauto.
Qed.


Theorem xform_mem_pred : forall prd (hm : rawdisk),
  crash_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => crash_xform (prd a v)) hm.
Proof.
  unfold mem_pred; intros; split.
  xform_norm; subst.
  rewrite xform_listpred.
  cancel.

  cancel; subst.
  xform_normr; cancel.
  rewrite xform_listpred.
  cancel.
  eauto.
Qed.


Theorem sync_xform_mem_pred : forall prd (hm : rawdisk),
  sync_xform (@mem_pred _ addr_eq_dec _ _ addr_eq_dec _ prd hm) <=p=>
  @mem_pred _ addr_eq_dec _ _ addr_eq_dec _ (fun a v => sync_xform (prd a v)) hm.
Proof.
  unfold mem_pred; intros; split.
  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.

  rewrite sync_xform_exists_comm; apply pimpl_exists_l; intros.
  apply pimpl_exists_r; eexists.
  repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty).
  rewrite sync_xform_listpred; cancel.
Qed.


Theorem sync_invariant_mem_pred : forall HighAT HighAEQ HighV (prd : HighAT -> HighV -> _) hm,
  (forall a v, sync_invariant (prd a v)) ->
  sync_invariant (@mem_pred _ _ _ _ HighAEQ _ prd hm).
Proof.
  unfold mem_pred; eauto.
Qed.

Hint Resolve sync_invariant_mem_pred.


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

(*
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
*)

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

  Lemma mem_incl_listupd_same : forall la lb,
    Forall2 (fun va vb => incl (vsmerge va) (vsmerge vb)) la lb ->
    forall m st,
    mem_incl (listupd m st la) (listupd m st lb).
  Proof.
    intros.
    apply mem_incl_listupd; auto.
    apply mem_incl_refl.
  Qed.

End MEM_INCL.
