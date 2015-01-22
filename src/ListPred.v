Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg Array.
Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* 
A general list predicate *)

Section LISTPRED.

  Variable T : Type.
  Variable V : Type.
  Variable prd : T -> @pred V.

  Fixpoint listpred (ts : list T) :=
    match ts with
    | nil => emp
    | t :: ts' => (prd t) * listpred ts'
    end%pred.

  Lemma listpred_nil: forall T V (prd : T -> @pred V),
    listpred nil = emp.
  Proof.
    unfold listpred; intros; auto.
  Qed.

  Theorem listpred_fwd : forall l i def, 
    i < length l ->
      listpred l =p=> listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l).
  Proof.
    induction l; simpl; intros; [omega |].
    destruct i; simpl; cancel.
    apply IHl; omega.
  Qed.

  Theorem listpred_bwd : forall l i def, 
    i < length l ->
      listpred (firstn i l) * (prd (selN l i def)) * listpred (skipn (S i) l) =p=> listpred l.
  Proof.
    induction l; simpl; intros; [omega |].
    destruct i; [cancel | simpl].
    destruct l; simpl in H; [omega |].
    cancel.
    eapply pimpl_trans; [| apply IHl ].
    cancel.
    omega.
  Qed.

  Theorem listpred_extract : forall l i def,
    i < length l ->
    listpred l =p=> exists F, F * prd (selN l i def).
  Proof.
    intros; rewrite listpred_fwd with (def:=def) by eauto; cancel.
  Qed.

  Theorem listpred_inj: forall l1 l2,
     l1 = l2 -> listpred l1 <=p=> listpred l2.
  Proof.
     intros; subst; auto.
  Qed.

  Definition sep_star_fold : (T -> @pred V -> @pred V) := fun x => sep_star (prd x).
  Definition listpred' := fold_right sep_star_fold emp.

  Theorem listpred_listpred': forall l,
    listpred l = listpred' l.
  Proof.
    induction l; unfold listpred, listpred', sep_star_fold, fold_right; auto.
  Qed.

  Theorem listpred'_app_fwd: forall l1 l2,
    listpred' (l1 ++ l2) =p=> listpred' l1 * listpred' l2.
  Proof.
    unfold listpred'.
    induction l1; destruct l2; unfold sep_star_fold; try cancel;
    rewrite IHl1; unfold sep_star_fold; cancel.
  Qed.

  Theorem listpred'_app_bwd: forall l1 l2,
    listpred' l1 * listpred' l2 =p=> listpred' (l1 ++ l2).
  Proof.
    unfold listpred'.
    induction l1; destruct l2; unfold sep_star_fold; try cancel;
    rewrite <- IHl1; unfold sep_star_fold; cancel.
  Qed.

  Theorem listpred_app: forall l1 l2,
    listpred (l1 ++ l2) <=p=> listpred l1 * listpred l2.
  Proof.
    intros; replace listpred with listpred'.
    unfold piff; split.
    apply listpred'_app_fwd.
    apply listpred'_app_bwd.
    apply functional_extensionality.
    apply listpred_listpred'.
  Qed.

  Theorem listpred_isolate : forall l i def,
    i < length l ->
    listpred l <=p=> listpred (removeN l i) * prd (selN l i def).
  Proof.
    intros.
    unfold removeN.
    rewrite listpred_app.
    unfold piff; split.
    rewrite listpred_fwd by eauto; cancel.
    eapply pimpl_trans2.
    apply listpred_bwd; eauto.
    cancel.
  Qed.

  Theorem listpred_updN : forall l i v,
    i < length l ->
    listpred (updN l i v) <=p=> listpred (removeN l i) * prd v.
  Proof.
    intros; rewrite listpred_isolate with (def:=v);
       [ | rewrite length_updN; eauto].
    rewrite removeN_updN.
    rewrite selN_updN_eq; auto.
  Qed.

  Theorem listpred_updN_selN: forall l i v def,
    i < length l ->
    prd (selN l i def) =p=> prd v ->
    listpred l =p=> listpred (updN l i v).
  Proof.
    intros.
    rewrite listpred_updN by auto.
    rewrite listpred_isolate with (def:=def) at 1 by eauto.
    cancel; auto.
  Qed.

End LISTPRED.



(* predicate over a pair of lists *)

Section LISTMATCH.

  Variable A : Type.
  Variable B : Type.
  Variable V : Type.
  Variable prd : A -> B -> @pred V.

  Definition pprd := prod_curry prd.

  Definition listmatch (a : list A) (b : list B) :=
    listpred pprd (List.combine a b).


End LISTMATCH.
