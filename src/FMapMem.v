Require Import List.
Require Import FMapFacts.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import MapUtils.
Require Import Mem.
Require Import Pred.
Require Import FunctionalExtensionality.

Module MapMem (OT : UsualOrderedType) (M : S with Module E := OT).

  Module Map := M.
  Module Defs := MapDefs OT.

  Section MapMemSec.

    Variable V : Type.
    Definition mem_type := @mem Map.key OT.eq_dec V.

    Definition mm (m : Map.t V) : mem_type := fun a => Map.find a m.

    Lemma find_add_eq : forall m a (v : V),
      Map.find a (Map.add a v m) = Some v.
    Proof.
      intros.
      erewrite M.find_1; eauto.
      apply M.add_1.
      reflexivity.
    Qed.

    Lemma find_add_ne : forall m a a' (v : V),
      a <> a' -> Map.find a (Map.add a' v m) = Map.find a m.
    Proof.
      intros.
      case_eq (Map.find a (Map.add a' v m)); intros.
      - apply M.find_2 in H0.
        eapply M.add_3 in H0; [| congruence ].
        erewrite M.find_1 with (e := v0); auto.
      - case_eq (Map.find a m); intros; eauto.
        eapply M.find_2 in H1.
        eapply M.add_2 with (x := a') (e' := v) in H1.
        eapply M.find_1 in H1; congruence.
        congruence.
    Qed.

    Lemma find_remove_eq : forall m a,
      @Map.find V a (Map.remove a m) = None.
    Proof.
      intros.
      case_eq (Map.find a (Map.remove a m)); eauto; intros.
      apply M.find_2 in H.
      exfalso.
      eapply M.remove_1; unfold M.In; try eauto.
      reflexivity.
    Qed.

    Lemma find_remove_ne : forall m a a',
      a <> a' -> @Map.find V a (Map.remove a' m) = Map.find a m.
    Proof.
      intros.
      case_eq (Map.find a (Map.remove a' m)); intros.
      - apply M.find_2 in H0.
        apply M.remove_3 in H0.
        erewrite M.find_1; eauto.
      - case_eq (Map.find a m); eauto; intros.
        eapply M.find_2 in H1.
        eapply M.remove_2 with (x := a') in H1.
        eapply M.find_1 in H1; congruence.
        congruence.
    Qed.

    Theorem mm_init :
      @emp _ OT.eq_dec _ (mm (Map.empty _)).
    Proof.
      unfold emp, mm; intros.
      case_eq (Map.find a (Map.empty V)); intros; auto.
      apply M.find_2 in H.
      exfalso.
      eapply M.empty_1; eauto.
    Qed.

    Theorem mm_add : forall m (F : @pred Map.key OT.eq_dec V) a v,
      Map.find a m = None ->
      F (mm m) ->
      (F * a |-> v)%pred (mm (Map.add a v m)).
    Proof.
      unfold_sep_star; intros; repeat deex.
      exists (mm m).
      unfold mm in *.
      exists (fun a' => if OT.eq_dec a' a then Some v else None).
      split; [|split].
      - apply functional_extensionality; intro.
        unfold mem_union; destruct (OT.eq_dec x a); unfold OT.eq in *; subst.
        rewrite find_add_eq; rewrite H; auto.
        rewrite find_add_ne by auto.
        destruct (Map.find x m); auto.
      - unfold mem_disjoint in *. intuition. repeat deex.
        destruct (OT.eq_dec a0 a); subst; intuition; pred.
      - intuition; eauto.
        unfold ptsto; intuition.
        destruct (OT.eq_dec a a); pred.
        destruct (OT.eq_dec a' a); pred.
    Qed.

    Theorem mm_replace : forall m (F : @pred Map.key OT.eq_dec V) a v0 v,
      (a |-> v0 * F)%pred (mm m) ->
      (a |-> v * F)%pred (mm (Map.add a v m)).
    Proof.
      unfold_sep_star; intros; repeat deex.
      exists (fun a' => if OT.eq_dec a' a then Some v else None).
      exists m2.
      unfold mm in *.
      split; [|split].
      - apply functional_extensionality; intro.
        unfold mem_union; destruct (OT.eq_dec x a); unfold OT.eq in *; subst; eauto.
        rewrite find_add_eq; eauto.
        rewrite find_add_ne by auto.
        destruct H1; repeat deex.
        apply equal_f with (x0 := x) in H0; rewrite H0.
        unfold mem_union. rewrite H2; auto.
      - unfold mem_disjoint in *. intuition. repeat deex.
        apply H.
        destruct H1; repeat deex.
        repeat eexists; eauto.
        destruct (OT.eq_dec a0 a); unfold OT.eq in *; subst; eauto.
        pred.
      - intuition eauto.
        unfold ptsto; intuition; unfold OT.eq in *.
        destruct (OT.eq_dec a a); pred.
        destruct (OT.eq_dec a' a); pred.
    Qed.

    Theorem mm_remove : forall m (F : @pred Map.key OT.eq_dec V) a v,
      (a |-> v * F)%pred (mm m) ->
      F (mm (Map.remove a m)).
    Proof.
      unfold_sep_star; unfold mm; intros; repeat deex.
      match goal with
      | [ |- F ?m ] => replace (m) with m2; eauto
      end.
      apply functional_extensionality; intro.
      destruct (OT.eq_dec x a); unfold OT.eq in *; subst.
      - rewrite find_remove_eq.
        unfold mem_disjoint in *.
        case_eq (m2 a); intros; try congruence.
        exfalso. apply H.
        exists a. exists v. exists v0.
        unfold ptsto in *; intuition.
      - rewrite find_remove_ne by auto.
        eapply equal_f in H0. rewrite H0.
        unfold mem_union.
        case_eq (m1 x); intros; try congruence.
        unfold ptsto in *; intuition.
        rewrite H5 in H2; eauto.
        congruence.
    Qed.

    Theorem mm_find : forall m (F : @pred Map.key OT.eq_dec V) a v,
      (a |-> v * F)%pred (mm m) ->
      Map.find a m = Some v.
    Proof.
      unfold ptsto, mm; unfold_sep_star.
      intros; repeat deex.
      eapply equal_f in H0; rewrite H0.
      apply mem_union_addr; eauto.
    Qed.

  End MapMemSec.

End MapMem.
