Require Import Bool.
Require Import Word.
Require Import String.
Require Import Pred.
Require Import Arith.
Require Import List ListUtils.
Require Import FunctionalExtensionality.


Import ListNotations.

Set Implicit Arguments.

(**
 * Some helper lemmas to help with reasoning about pathnames 
 *)

Theorem pathname_decide_prefix : forall (base pn : list string),
    (exists suffix, pn = base ++ suffix) \/
    (~ exists suffix, pn = base ++ suffix).
  Proof.
    induction base; simpl. eauto.
    destruct pn.
    right. intro H'; destruct H'. congruence.
    destruct (string_dec s a); subst.
    - destruct (IHbase pn); repeat deex.
      left; eauto.
      right. intro H'; apply H. deex. inversion H0; eauto.
    - right. intro H. deex. inversion H. eauto.
  Qed.

  Definition pathname_prefix p1 p2 :=
    (exists suffix : list string, p1 ++ suffix = p2).

  Lemma pathname_prefix_nil: forall suffix,
    pathname_prefix [] suffix.
  Proof.
    intros.
    unfold pathname_prefix.
    eexists suffix.
    rewrite app_nil_l; eauto.
  Qed.

  Lemma pathname_prefix_head: forall n suffix,
    pathname_prefix [n] ([n]++suffix).
  Proof.
    intros.
    unfold pathname_prefix.
    eexists suffix.
    reflexivity.
  Qed.

  Lemma pathname_prefix_head_neq: forall a s suffix,
    a <> s ->
    ~pathname_prefix [a] (s::suffix).
  Proof.
    intros. unfold pathname_prefix.
    intro.
    eapply H.
    deex.
    rewrite cons_app with (l:= suffix) in H0.
    inversion H0. subst.
    eauto.
  Qed.

  Lemma pathname_prefix_ex_falso: forall name suffix,
    ~ pathname_prefix [name] suffix ->
    (exists suffix0 : list string, suffix = [name] ++ suffix0) -> False.
  Proof.
    intros.
    deex. exfalso.
    eapply H.
    unfold pathname_prefix.
    exists suffix0; eauto.
  Qed.

  Lemma pathname_prefix_neq: forall path path',
    ~ (exists suffix : list string, path = path' ++ suffix) ->
    ~ pathname_prefix path' path.
  Proof.
    unfold pathname_prefix; eauto.
    intros. 
    intro.
    eapply H.
    destruct H0.
    eexists x; eauto.
  Qed.

  Lemma pathname_prefix_head_neq': forall path name name',
    ~ pathname_prefix [name] (name' :: path) ->
    name <> name'.
  Proof.
    intros.
    unfold pathname_prefix in H.
    intro; subst.
    eapply H.
    exists path; eauto.
  Qed.

  Lemma pathname_prefix_trim : forall a b c,
    pathname_prefix a b <-> pathname_prefix (c ++ a) (c ++ b).
  Proof.
    unfold pathname_prefix; split; intros; repeat deex.
    - eexists. rewrite <- app_assoc. eauto.
    - rewrite <- app_assoc in H. eexists.
      apply app_inv_head in H. eauto.
  Qed.

