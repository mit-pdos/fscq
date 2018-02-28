Require Import Mem.
Require Import List Omega Ring Word Pred.
Require Import FunctionalExtensionality.
Require Export PermArray.

Set Implicit Arguments.
Set Default Proof Using "Type".

(* bijection on restricted domain *)

Section COND_BIJECTION.

  Variables A B : Type.
  Variable f : A -> B.
  Variable PA : A -> Prop.
  Variable PB : B -> Prop.

  Definition cond_injective :=
    forall x y : A, PA x -> PA y -> f x = f y -> x = y.

  Definition cond_surjective :=
    forall y : B, PB y -> {x : A | PA x /\ f x = y}.

  Inductive cond_bijective : Prop :=
    CondBijective : cond_injective -> cond_surjective -> cond_bijective.

  Section BIJECTION_INVERSION.

    Variable f' : B -> A.

    Definition cond_left_inverse := 
      forall x : A, PA x -> PB (f x) /\ f' (f x) = x.

    Definition cond_right_inverse := 
      forall y : B, PB y -> PA (f' y) /\ f (f' y) = y.

    Definition cond_inverse := 
      cond_left_inverse /\ cond_right_inverse.

    Lemma cond_left_inv_inj : cond_left_inverse -> cond_injective.
    Proof.
      intros H x y P1 P2 H0.
      pose proof (H x P1) as [P3 P4].
      rewrite <- P4.
      rewrite H0.
      apply H.
      auto.
    Qed.

    Lemma cond_right_inv_surj : cond_right_inverse -> cond_surjective.
    Proof.
      intros H y P1.
      pose proof (H y P1) as [P2 P3].
      rewrite <- P3.
      exists (f' y); intuition.
    Qed.

    Lemma cond_inv2bij : cond_inverse -> cond_bijective.
    Proof.
      intros [H1 H2].
      constructor.
      eapply cond_left_inv_inj; eauto.
      eapply cond_right_inv_surj; eauto.
    Qed.

    Lemma cond_inv_rewrite_right : forall y,
      cond_inverse -> PB y -> f (f' y) = y.
    Proof.
      intros; apply H; auto.
    Qed.

    Lemma cond_inv_rewrite_left : forall x,
      cond_inverse -> PA x -> f' (f x) = x.
    Proof.
      intros; apply H; auto.
    Qed.

    Lemma cond_inv_domain_right : forall y,
      cond_inverse -> PB y -> PA (f' y).
    Proof.
      intros; apply H; auto.
    Qed.

    Lemma cond_inv_domain_left : forall x,
      cond_inverse -> PA x -> PB (f x).
    Proof.
      intros; apply H; auto.
    Qed.

  End BIJECTION_INVERSION.

End COND_BIJECTION.


Theorem cond_inverse_sym : forall A B PA PB (f : A -> B) (f' : B -> A),
  cond_inverse f PA PB f'
  -> cond_inverse f' PB PA f.
Proof.
  firstorder.
Qed.

Theorem cond_inv2bij_inv : forall A B PA PB (f : A -> B) (f' : B -> A),
  cond_inverse f PA PB f'
  -> cond_bijective f' PB PA.
Proof.
  intros.
  eapply cond_inv2bij.
  apply cond_inverse_sym; eauto.
Qed.

Section MEMMATCH.

  Variable AT1 : Type.
  Variable AT2 : Type.
  Variable atrans : AT1 -> AT2.

  Variable AEQ1 : EqDec AT1.
  Variable AEQ2 : EqDec AT2.
  Variable V : Type.
  Variable m1 : @mem AT1 AEQ1 V.
  Variable m2 : @mem AT2 AEQ2 V.

  (* restrictions on atrans' domain and codomain *)
  Variable AP1 : AT1 -> Prop.
  Variable AP2 : AT2 -> Prop.

  (* decidablity of subdomain *)
  Variable AP1_dec : forall a1, AP1 a1 \/ ~ AP1 a1.
  Variable AP2_dec : forall a2, AP2 a2 \/ ~ AP2 a2.

  (* well-formedness of memory addresses *)
  Variable AP1_ok : forall a1, indomain a1 m1 -> AP1 a1.
  Variable AP2_ok : forall a2, indomain a2 m2 -> AP2 a2.

  Definition mem_atrans AT1 AEQ1 V AT2 AEQ2
    f (m : @mem AT1 AEQ1 V) (m' : @mem AT2 AEQ2 V) (P : AT1 -> Prop) :=
    forall a, P a -> m a = m' (f a).

  Variable MTrans : mem_atrans atrans m1 m2 AP1.

  Lemma mem_atrans_indomain : forall a1 x,
    indomain a1 m1 ->
    m1 a1 = x -> m2 (atrans a1) = x.
  Proof using MTrans AP1_ok.
    intros.
    apply AP1_ok in H.
    rewrite <- (MTrans H); auto.
  Qed.

  Lemma mem_atrans_mem_except : forall a (ap : AP1 a),
    cond_bijective atrans AP1 AP2 ->
    mem_atrans atrans (mem_except m1 a) (mem_except m2 (atrans a)) AP1.
  Proof using MTrans AP1_ok.
    intros; unfold mem_atrans, mem_except; intro x.
    destruct (AEQ1 x a); destruct (AEQ2 (atrans x) (atrans a));
      subst; auto; try tauto.
    destruct (indomain_dec x m1); auto.
    contradict n.
    apply H; auto.
  Qed.

  Section MEMMATCH_INVERSION.

    Variable ainv : AT2 -> AT1.
    Variable HInv : cond_inverse atrans AP1 AP2 ainv.

    Lemma mem_ainv_any : forall a (ap : AP2 a) x,
      m1 (ainv a) = x -> m2 a = x.
    Proof using MTrans HInv.
      intros.
      replace a with (atrans (ainv a)) by (apply HInv; auto).
      assert (AP1 (ainv a)) as Hx by (apply HInv; auto).
      rewrite <- (MTrans Hx); auto.
    Qed.

    Lemma mem_atrans_inv_ptsto : forall a (ap : AP2 a) F v,
      (F * (ainv a) |-> v)%pred m1
      -> (any * a |-> v)%pred m2.
    Proof using MTrans HInv.
      intros.
      apply any_sep_star_ptsto.
      eapply mem_ainv_any; eauto.
      eapply ptsto_valid'; eauto.
    Qed.

    Lemma mem_atrans_inv_notindomain : forall a (ap : AP2 a),
      notindomain (ainv a) m1 -> notindomain a m2.
    Proof using MTrans HInv.
      unfold notindomain; intros.
      eapply mem_ainv_any; eauto.
    Qed.

    Lemma mem_atrans_inv_indomain : forall a (ap : AP2 a),
      indomain (ainv a) m1 -> indomain a m2.
    Proof using MTrans HInv.
      unfold indomain; intros.
      destruct H; eexists.
      eapply mem_ainv_any; eauto.
    Qed.

    Lemma mem_atrans_emp :
      emp m1 -> emp m2.
    Proof using MTrans HInv AP2_ok AP2_dec.
      unfold emp; intros.
      destruct (AP2_dec a).

      replace a with (atrans (ainv a)).
      apply mem_ainv_any; auto.
      replace (atrans (ainv a)) with a; auto.
      apply eq_sym; apply HInv; auto.
      apply HInv; auto.

      destruct (indomain_dec a m2); auto.
      contradict H0.
      apply AP2_ok; auto.
    Qed.

    Lemma mem_ainv_mem_except : forall a (ap : AP2 a),
      mem_atrans atrans (mem_except m1 (ainv a)) (mem_except m2 a) AP1.
    Proof using MTrans HInv AP1_ok.
      intros; unfold mem_atrans, mem_except; intro x.
      destruct (AEQ1 x (ainv a)); destruct (AEQ2 (atrans x) a);
        try subst; auto; try tauto.

      contradict n.
      apply HInv; auto.
      destruct (indomain_dec x m1); auto.
      contradict n.
      apply eq_sym.
      apply HInv; auto.
    Qed.

    Lemma mem_ainv_mem_upd : forall a v (ap : AP2 a),
      mem_atrans atrans (Mem.upd m1 (ainv a) v) (Mem.upd m2 a v) AP1.
    Proof using MTrans HInv.
      intros; unfold mem_atrans, Mem.upd; intro x.
      destruct (AEQ1 x (ainv a)); destruct (AEQ2 (atrans x) a); auto.
      contradict n; subst.
      apply HInv; auto.

      intros; subst.
      contradict n.
      erewrite cond_inv_rewrite_left; eauto.
    Qed.

    Lemma mem_atrans_cond_inv : mem_atrans ainv m2 m1 AP2.
    Proof using HInv MTrans.
      cbv [mem_atrans cond_inverse cond_left_inverse cond_right_inverse] in *.
      destruct HInv as [_ H'].
      intros a ?; specialize (H' a).
      rewrite MTrans by intuition.
      f_equal. intuition.
    Qed.

  End MEMMATCH_INVERSION.

End MEMMATCH.

