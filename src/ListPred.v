Require Import Mem.
Require Import List Omega Ring Word Pred PredCrash Prog Hoare SepAuto BasicProg Array ListUtils.
Require Import FunctionalExtensionality.

Set Implicit Arguments.


(* A general list predicate *)

Section LISTPRED.

  Set Default Proof Using "Type".

  Variable T : Type.
  Variable AT : Type.
  Variable AEQ : EqDec AT.
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
    apply pimpl_refl.
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

  Theorem listpred_split : forall l n,
    listpred l <=p=> listpred (firstn n l) * listpred (skipn n l).
  Proof.
    intros.
    setoid_rewrite <- firstn_skipn with (n := n) at 1.
    rewrite listpred_app.
    split; cancel.
  Qed.

  Theorem listpred_isolate_fwd : forall l i def,
    i < length l ->
    listpred l =p=> listpred (removeN l i) * prd (selN l i def).
  Proof.
    intros.
    apply listpred_isolate; auto.
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

  Theorem listpred_nodup_piff : forall l,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    listpred l <=p=> [[ NoDup l ]] * listpred l.
  Proof.
    intros. split. apply lift_impl. intros. eapply listpred_nodup; eauto.
    cancel.
  Qed.

  Theorem listpred_nodup_F : forall l m,
    (forall x y : T, {x = y} + {x <> y}) ->
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    (exists F, F * listpred l)%pred m -> NoDup l.
  Proof.
    intros.
    destruct_lift H0.
    rewrite listpred_nodup_piff in H0 by eauto.
    destruct_lift H0.
    eauto.
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
    rewrite listpred_nodup_piff; eauto.
    simpl; destruct (dec x a).
    cancel; inversion H2; rewrite remove_not_In; eauto.
    rewrite IHl; [ cancel | destruct H0; subst; tauto ].
  Qed.

  Theorem listpred_remove' :
    forall (dec : forall x y : T, {x = y} + {x <> y}) x l,
    (forall (y : T) m', ~ (prd y * prd y)%pred m') ->
    NoDup l ->
    In x l ->
    prd x * listpred (remove dec x l) =p=> listpred l.
  Proof.
    intros.
    induction l.
    cancel.
    simpl; destruct (dec x a); subst.
    - inversion H0. rewrite remove_not_In; eauto.
    - simpl; cancel.
      rewrite <- IHl. cancel. inversion H0. eauto. eauto.
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
      assert (m2 = m0) by eauto; subst.
      assert (m4 = m3) by eauto; subst.
      reflexivity.
  Qed.

End LISTPRED.


(* predicate over a pair of lists *)

Section LISTMATCH.

  Set Default Proof Using "Type".

  Variable A : Type.
  Variable B : Type.
  Variable AT : Type.
  Variable AEQ : EqDec AT.
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

  Lemma listmatch_length_pimpl : forall a b,
    listmatch a b =p=> (listmatch a b) * [[ length a = length b ]].
  Proof.
    unfold listmatch; cancel.
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


  Theorem listmatch_app_tail: forall F a b av bv,
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

  Theorem listmatch_app : forall a1 b1 a2 b2,
    listmatch a1 b1 * listmatch a2 b2 =p=> listmatch (a1 ++ a2) (b1 ++ b2).
  Proof.
    unfold listmatch; intros; cancel.
    repeat rewrite combine_app by auto.
    rewrite listpred_app; cancel.
    repeat rewrite app_length; omega.
  Qed.

  Theorem listmatch_split : forall a b n,
    listmatch a b <=p=> listmatch (firstn n a) (firstn n b) * listmatch (skipn n a) (skipn n b).
  Proof.
    unfold listmatch; intros.
    rewrite listpred_split with (n := n).
    rewrite firstn_combine_comm.
    split; cancel.
    rewrite skipn_combine; eauto; cancel.
    repeat rewrite firstn_length; auto.
    repeat rewrite skipn_length; auto.
    rewrite skipn_combine; auto.
    eapply skipn_firstn_length_eq; eauto.
    eapply skipn_firstn_length_eq; eauto.
  Qed.

End LISTMATCH.





Lemma listmatch_sym : forall AT AEQ V A B (al : list A) (bl : list B) f,
  (@listmatch _ _ AT AEQ V) f al bl <=p=>
  listmatch (fun b a => f a b) bl al.
Proof.
  unfold listmatch; intros.
  split; cancel;
  generalize dependent bl;
  generalize dependent al;
  induction al; destruct bl; cancel; auto.
Qed.

Lemma listmatch_map_l : forall AT AEQ V A B C al bl f (g : A -> C),
  (@listmatch C B AT AEQ V) f (map g al) bl <=p=>
  (@listmatch A B _ _ _) (fun a b => f (g a) b) al bl.
Proof.
  unfold listmatch; intros.
  split; cancel; autorewrite with lists in *; auto;
  generalize dependent bl;
  generalize dependent al;
  induction al; destruct bl; cancel; auto.
Qed.

Lemma listmatch_map_r : forall AT AEQ V A B C al bl f (g : B -> C),
  (@listmatch A C AT AEQ V) f al (map g bl) <=p=>
  (@listmatch A B _ _ _) (fun a b => f a (g b)) al bl.
Proof.
  intros.
  rewrite listmatch_sym.
  rewrite listmatch_map_l.
  rewrite listmatch_sym; auto.
Qed.

Lemma listmatch_map : forall AT AEQ V A B A' B' al bl f (fa : A -> A') (fb : B -> B'),
  (@listmatch A B AT AEQ V) (fun a b => f (fa a) (fb b)) al bl <=p=>
  (@listmatch A' B' _ _ _) f (map fa al) (map fb bl).
Proof.
  intros; rewrite listmatch_map_l, listmatch_map_r; auto.
Qed.

Lemma listpred_map : forall AT AEQ V A B l f (g : A -> B),
  @listpred B AT AEQ V f (map g l) <=p=>
  @listpred A AT AEQ V (fun a => f (g a)) l.
Proof.
  induction l; simpl; intros; auto.
  split; cancel; rewrite IHl; auto.
Qed.


Lemma listmatch_ptsto_listpred : forall AT AEQ V (al : list AT) (vl : list V),
  listmatch (fun v a => a |-> v) vl al =p=>
  (@listpred _ _ AEQ _) (fun a => a |->?) al.
Proof.
  unfold listmatch; induction al; destruct vl.
  cancel. cancel.
  norml; inversion H0.
  cancel; inversion H0.
  unfold pimpl in *; intros.
  eapply IHal; eauto.
  pred_apply; cancel.
Qed.

Theorem xform_listpred : forall V (l : list V) prd,
  crash_xform (listpred prd l) <=p=> listpred (fun x => crash_xform (prd x)) l.
Proof.
  induction l; simpl; intros; split; auto; xform_dist; auto.
  rewrite IHl; auto.
  rewrite IHl; auto.
Qed.


Lemma crash_xform_pprd : forall A B (prd : A -> B -> rawpred),
  (fun p => crash_xform (pprd prd p)) =
  (pprd (fun x y => crash_xform (prd x y))).
Proof.
  unfold pprd, prod_curry, crash_xform; intros.
  apply functional_extensionality; intros; destruct x; auto.
Qed.

Theorem xform_listmatch : forall A B (a : list A) (b : list B) prd,
  crash_xform (listmatch prd a b) <=p=> listmatch (fun x y => crash_xform (prd x y)) a b.
Proof.
  unfold listmatch; intros; split; xform_norm;
  rewrite xform_listpred; cancel;
  rewrite crash_xform_pprd; auto.
Qed.

Theorem xform_listpred_idem_l : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) =p=> prd e) ->
  crash_xform (listpred prd l) =p=> listpred prd l.
Proof.
  induction l; simpl; intros; auto.
  xform_dist.
  rewrite H.
  rewrite IHl; auto.
Qed.


Theorem xform_listpred_idem_r : forall V (l : list V) prd,
  (forall e,  prd e =p=> crash_xform (prd e)) ->
  listpred prd l =p=> crash_xform (listpred prd l).
Proof.
  induction l; simpl; intros; auto.
  xform_dist; auto.
  xform_dist.
  rewrite <- H.
  rewrite <- IHl; auto.
Qed.

Theorem xform_listpred_idem : forall V (l : list V) prd,
  (forall e, crash_xform (prd e) <=p=> prd e) ->
  crash_xform (listpred prd l) <=p=> listpred prd l.
Proof.
  split.
  apply xform_listpred_idem_l; intros.
  apply H.
  apply xform_listpred_idem_r; intros.
  apply H.
Qed.

Theorem xform_listmatch_idem_l : forall A B (a : list A) (b : list B) prd,
  (forall a b, crash_xform (prd a b) =p=> prd a b) ->
  crash_xform (listmatch prd a b) =p=> listmatch prd a b.
Proof.
  unfold listmatch; intros.
  xform_norm; cancel.
  apply xform_listpred_idem_l; intros.
  destruct e; cbn; auto.
Qed.

Theorem xform_listmatch_idem_r : forall A B (a : list A) (b : list B) prd,
  (forall a b,  prd a b =p=> crash_xform (prd a b)) ->
  listmatch prd a b =p=> crash_xform (listmatch prd a b).
Proof.
  unfold listmatch; intros.
  cancel.
  xform_normr.
  rewrite <- xform_listpred_idem_r; cancel.
  auto.
Qed.

Theorem xform_listmatch_idem : forall A B (a : list A) (b : list B) prd,
  (forall a b, crash_xform (prd a b) <=p=> prd a b) ->
  crash_xform (listmatch prd a b) <=p=> listmatch prd a b.
Proof.
  split.
  apply xform_listmatch_idem_l; auto.
  apply H.
  apply xform_listmatch_idem_r; auto.
  apply H.
Qed.

Lemma xform_listpred_ptsto : forall l,
  crash_xform (listpred (fun a => a |->?) l) =p=>
               listpred (fun a => a |->?) l.
Proof.
  induction l; simpl.
  rewrite crash_invariant_emp; auto.
  xform_dist.
  rewrite crash_xform_ptsto_exis, IHl.
  auto.
Qed.

Lemma xform_listmatch_ptsto : forall al vl,
  crash_xform (listmatch (fun v a => a |-> v) vl al) =p=>
    exists l, [[ possible_crash_list vl l ]] *
    listmatch (fun v a => a |-> v) (synced_list l) al.
Proof.
  unfold listmatch; induction al; destruct vl; xform_norm.
  - cancel. instantiate (1 := nil); simpl; auto.
    unfold possible_crash_list; intuition; inversion H.
    rewrite synced_list_length; auto.
  - inversion H0.
  - inversion H0.
  - rewrite crash_xform_ptsto.
    specialize (IHal vl).
    rewrite crash_xform_sep_star_dist, crash_xform_lift_empty in IHal.
    inversion H; subst.
    setoid_rewrite lift_impl with (Q := length vl = length al) at 3; intros; eauto.
    rewrite IHal; simpl.

    cancel.
    eassign (v' :: l); cancel.
    simpl; cancel.
    apply possible_crash_list_cons; simpl; auto.
    rewrite synced_list_length in *; simpl; omega.
    apply possible_crash_list_cons; simpl; auto.
    rewrite synced_list_length in *; simpl; omega.
Qed.

Theorem sync_invariant_listpred : forall T prd (l : list T),
  (forall x, sync_invariant (prd x)) ->
  sync_invariant (listpred prd l).
Proof.
  induction l; simpl; intros.
  apply sync_xform_emp.
  apply sync_invariant_sep_star; eauto.
Qed.
