Require Import List Omega Ring Word Pred Prog Hoare SepAuto BasicProg Array.
Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* 
A general list predicate *)

Section LISTPRED.

  Variable T : Type.
  Variable AT : Type.
  Variable AEQ : DecEq AT.
  Variable V : Type.
  Variable prd : T -> @pred AT AEQ V.

  Fixpoint listpred (ts : list T) :=
    match ts with
    | nil => emp
    | t :: ts' => (prd t) * listpred ts'
    end%pred.

  Lemma listpred_nil:
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

  Theorem listpred_pick : forall x l, 
    In x l -> listpred l =p=> exists F, prd x * F.
  Proof.
    induction l; intro Hi.
    inversion Hi.
    simpl.
    destruct Hi.
    cancel.
    rewrite IHl by assumption.
    cancel.
  Qed.

  Theorem listpred_inj: forall l1 l2,
     l1 = l2 -> listpred l1 <=p=> listpred l2.
  Proof.
     intros; subst; auto.
  Qed.

  Definition sep_star_fold : (T -> @pred AT AEQ V -> @pred AT AEQ V) := fun x => sep_star (prd x).
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

  Theorem listpred_nodup : forall l m,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l m -> NoDup l.
  Proof.
    induction l; intuition; constructor; simpl in H0.
    intro Hin.
    revert H0.
    erewrite listpred_pick by (apply Hin).
    (* XXX should be possible not to bash this *)
    unfold_sep_star; intuition.
    do 2 destruct H0. intuition. destruct H4. do 2 destruct H3. intuition.
    eapply H.
    unfold_sep_star.
    exists x. exists x2.
    repeat split; intuition; eauto.
    subst. apply mem_disjoint_comm. apply mem_disjoint_comm in H0. rewrite mem_union_comm in H0.
    eapply mem_disjoint_union. eauto. eauto.

    revert H0.
    unfold_sep_star.
    intuition. do 2 destruct H0. intuition.
    eapply IHl; eauto.
  Qed.

  Theorem listpred_nodup' : forall l,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l =p=> [[ NoDup l ]] * listpred l.
  Proof.
    intros. apply lift_impl. intros. eapply listpred_nodup; eauto.
  Qed.

  Theorem remove_not_In :
    forall dec (a : T) l, ~ In a l -> remove dec a l = l.
  Proof.
    induction l.
    auto.
    intro Hni. simpl.
    destruct (dec a a0).
    subst. destruct Hni. simpl. tauto.
    rewrite IHl. trivial.
    simpl in Hni. tauto.
  Qed.

  Theorem remove_still_In : forall dec (a b : T) l,
    In a (remove dec b l) -> In a l.
  Proof.
    induction l; simpl; [tauto|].
    destruct (dec b a0).
    right; apply IHl; assumption.
    intro H. destruct H. subst. auto.
    right; apply IHl; assumption.
  Qed.

  Theorem remove_still_In_ne : forall dec (a b : T) l,
    In a (remove dec b l) -> b <> a.
  Proof.
    induction l; simpl; [tauto|].
    destruct (dec b a0).
    assumption.
    intro H. destruct H. subst. auto.
    apply IHl; assumption.
  Qed.

  Theorem remove_other_In : forall dec (a b : T) l,
    b <> a -> In a l -> In a (remove dec b l).
  Proof.
    induction l.
    auto.
    simpl. destruct (dec b a0).
    subst. intros. destruct H0; [subst; tauto | apply IHl; auto].
    simpl. intros. destruct H0; [left; auto | right; apply IHl; auto].
  Qed.


  Theorem listpred_remove :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    In x l ->
    listpred l =p=> prd x * listpred (remove dec x l).
  Proof.
    intros.
    induction l.
    cancel.
    rewrite listpred_nodup'; eauto.
    simpl; destruct (dec x a).
    cancel; inversion H2; rewrite remove_not_In; eauto.
    rewrite IHl; [ cancel | destruct H0; subst; tauto ].
  Qed.

  (**
   * For certain kinds of "complete" predicates, if two memories match
   * [listpred] over the same list, then the memories are equal.
   *)
  Theorem listpred_eq : forall l m1 m2,
    (forall x ma mb, prd x ma -> prd x mb -> ma = mb) ->
    listpred l m1 -> listpred l m2 -> m1 = m2.
  Proof.
    induction l; simpl; intros.
    - apply emp_complete; eauto.
    - unfold sep_star in *; rewrite sep_star_is in *; unfold sep_star_impl in *.
      repeat deex.
      assert (x0 = x2) by eauto; subst.
      assert (x1 = x) by eauto; subst.
      reflexivity.
  Qed.

End LISTPRED.


(* predicate over a pair of lists *)

Section LISTMATCH.

  Variable A : Type.
  Variable B : Type.
  Variable AT : Type.
  Variable AEQ : DecEq AT.
  Variable V : Type.
  Variable prd : A -> B -> @pred AT AEQ V.

  Definition pprd := prod_curry prd.

  Definition listmatch (a : list A) (b : list B) :=
    ([[ length a = length b ]] *
     listpred pprd (List.combine a b))%pred.

  Lemma listmatch_length : forall a b m,
    (listmatch a b)%pred m -> length a = length b.
  Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.

  Lemma listmatch_length_r : forall F a b m,
    (F * listmatch a b)%pred m -> length a = length b.
  Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.

  Lemma listmatch_length_l : forall F a b m,
    (listmatch a b * F)%pred m -> length a = length b.
  Proof.
    unfold listmatch; intros.
    destruct_lift H; auto.
  Qed.


  Theorem listmatch_isolate : forall a b i ad bd,
    i < length a -> i < length b ->
    listmatch a b <=p=>
    listmatch (removeN a i) (removeN b i) * prd (selN a i ad) (selN b i bd).
  Proof.
    intros; unfold listmatch.
    unfold piff; split.

    cancel.
    rewrite listpred_isolate with (i := i) (def := (ad, bd)) at 1.
    rewrite removeN_combine.
    rewrite selN_combine; auto.
    rewrite combine_length; rewrite <- H2; rewrite Nat.min_id; auto.
    repeat rewrite removeN_length by omega.
    omega.

    cancel.
    eapply removeN_length_eq with (a:=a) (b:=b) in H0; eauto.
    eapply pimpl_trans2.
    rewrite listpred_isolate with (i := i) (def := (ad, bd)).
    rewrite removeN_combine.
    rewrite selN_combine; auto.
    apply pimpl_refl.
    rewrite combine_length; rewrite <- H0; rewrite Nat.min_id; auto.
    repeat rewrite removeN_length by omega.
    cancel.
    eapply removeN_length_eq with (a:=a) (b:=b) in H1; eauto.
  Qed.

  Theorem listmatch_extract : forall a b i ad bd,
    i < length a ->
    listmatch a b =p=>
    [[ length a = length b ]] * 
    listmatch (removeN a i) (removeN b i) * prd (selN a i ad) (selN b i bd).
  Proof.
    intros; unfold listmatch.
    cancel.
    rewrite listpred_isolate with (i := i) (def := (ad, bd)) at 1.
    rewrite removeN_combine.
    rewrite selN_combine; auto.
    rewrite combine_length; rewrite <- H1; rewrite Nat.min_id; auto.
    repeat rewrite removeN_length by omega.
    omega.
  Qed.

  Theorem listmatch_updN_removeN : forall a b i av bv,
    i < length a -> i < length b ->
    listmatch (updN a i av) (updN b i bv) <=p=>
    listmatch (removeN a i) (removeN b i) * (prd av bv).
  Proof.
    intros; unfold piff; split.
    rewrite listmatch_isolate with (ad := av) (bd := bv);
      [ | rewrite length_updN; eauto ..].
    repeat rewrite selN_updN_eq by auto.
    repeat rewrite removeN_updN; auto.

    eapply pimpl_trans2.
    rewrite listmatch_isolate with (i := i) (ad := av) (bd := bv);
      [ | rewrite length_updN; eauto ..].
    apply pimpl_refl.
    repeat rewrite selN_updN_eq by auto.
    repeat rewrite removeN_updN; auto.
  Qed.

  Theorem listmatch_updN_selN: forall a b i av bv ad bd,
    i < length a -> i < length b ->
    prd (selN a i ad) (selN b i bd) =p=> prd av bv ->
    listmatch a b =p=> listmatch (updN a i av) (updN b i bv).
  Proof.
    intros.
    rewrite listmatch_updN_removeN by auto.
    rewrite listmatch_isolate with (ad := ad) (bd := bd) by eauto.
    cancel; auto.
  Qed.

  Theorem listmatch_updN_selN_r: forall F a b i av bv ad bd,
    i < length a -> i < length b ->
    (prd (selN a i ad) (selN b i bd)) * F =p=> prd av bv ->
    (listmatch a b) * F =p=> listmatch (updN a i av) (updN b i bv).
  Proof.
    intros.
    rewrite listmatch_updN_removeN by auto.
    rewrite listmatch_isolate with (ad := ad) (bd := bd) by eauto.
    cancel; rewrite sep_star_comm; auto.
  Qed.


  Theorem listmatch_app_r: forall F a b av bv,
    length a = length b ->
    F =p=> prd av bv ->
    (listmatch a b) * F =p=> listmatch (a ++ av :: nil) (b ++ bv :: nil).
  Proof.
    intros.
    eapply pimpl_trans2.
    eapply listmatch_isolate with (i := length a);
    try rewrite app_length; simpl; omega.
    rewrite removeN_tail.
    rewrite selN_last with (def := av); auto.
    rewrite H.
    rewrite removeN_tail.
    rewrite selN_last with (def := bv); auto.
    cancel; auto.
  Qed.


End LISTMATCH.

Hint Resolve listmatch_length_r.
Hint Resolve listmatch_length_l.
Hint Resolve listmatch_length.

Ltac solve_length_eq :=
  eauto; try congruence ; try omega;
  match goal with
  | [ H : length ?l = _ |- context [ length ?l ] ] =>
        solve [ rewrite H ; eauto ; try congruence ; try omega ]
  | [ H : _ = length ?l |- context [ length ?l ] ] =>
        solve [ rewrite <- H ; eauto ; try congruence ; try omega ]
  | [ H : context [ listmatch _ ?a ?b ] |- context [ length ?c ] ] =>
        let Heq := fresh in
        first [ apply listmatch_length_r in H as Heq
              | apply listmatch_length_l in H as Heq
              | apply listmatch_length in H as Heq ];
        solve [ constr_eq a c; repeat rewrite Heq ;
                eauto ; try congruence ; try omega
              | constr_eq b c; repeat rewrite <- Heq;
                eauto; try congruence ; try omega ];
        clear Heq
  end.


Ltac extract_listmatch_at ix :=
  match goal with
    | [  H : context [ listmatch ?p ?a _ ] |- _ ] =>
            erewrite listmatch_extract with (i := wordToNat ix) in H;
            try autorewrite with defaults in H; auto;
            match p with
            | ?n _ => try unfold n at 2 in H
            | _    => try unfold p at 2 in H
            end;
            destruct_lift H
  end.

