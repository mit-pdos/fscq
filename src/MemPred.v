Require Import Mem.
Require Import Pred.
Require Import ListPred.
Require Import List.
Require Import SepAuto.
Require Import FunctionalExtensionality.


Set Implicit Arguments.

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
    subst; eauto.
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
    cancel.
    eassign ((a, v) :: hm_avs).
    cancel.
    simpl; constructor; auto.
    apply avs2mem_none_notin. rewrite <- H3. apply mem_except_eq.
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
    cancel.
    eassign ( (a, v) :: hm_avs).
    cancel.
    simpl; constructor; auto.
    apply avs2mem_none_notin. rewrite <- H4. apply mem_except_eq.
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
    eapply equal_f with (x := h) in H2.
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

Require Import AsyncDisk PredCrash.

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
Qed.
