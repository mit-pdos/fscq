Require Import List FMapAVL Structures.OrderedTypeEx.
Require Import RelationClasses Morphisms.
Require Import VerdiTactics.
Require Import Go.

Set Implicit Arguments.
Unset Printing Implicit Defensive.

Import Go.

(* TODO What here is actually necessary? *)

Class GoWrapper (WrappedType: Type) :=
  { wrap:      WrappedType -> Go.value;
    wrap_inj:  forall v v', wrap v = wrap v' -> v = v' }.

Inductive ScopeItem :=
| SItem A {H: GoWrapper A} (v : A).

(* None matches nothing *)
Definition pred := option (VarMap.t ScopeItem).

Definition pred_matches (p : pred) (m : locals) : Prop :=
  match p with
    | None => False
    | Some p' =>
      forall k item,
        VarMap.find k p' = Some item ->
        match item with
            | SItem val =>
              VarMap.find k m = Some (wrap val)
        end
  end.

Definition pimpl (p q : pred) := forall m, pred_matches p m -> pred_matches q m.

Definition any : pred := Some (VarMap.empty _).

Definition ptsto var val : pred := Some (VarMap.add var val (VarMap.empty _)).

Module VarMapProperties := FMapFacts.WProperties_fun(Nat_as_OT)(VarMap).

(* TODO move this and its associated theorems somewhere else *)
Definition maps_disjoint T (m1 m2 : VarMap.t T) := 
  VarMapProperties.for_all (fun k1 _ => negb (VarMap.mem k1 m2)) m1.

Lemma for_all_if :
  forall elt (f : VarMap.key -> elt -> bool),
    Morphisms.Proper (Morphisms.respectful eq (Morphisms.respectful eq eq)) f ->
    forall m,
      VarMapProperties.for_all f m = true ->
      (forall k e, VarMap.MapsTo k e m -> f k e = true).
Proof.
  firstorder using VarMapProperties.for_all_iff.
Qed.

Lemma not_for_all_if : forall T (m : VarMap.t T) f,
  VarMapProperties.for_all f m = false ->
  exists k v, VarMap.MapsTo k v m /\ f k v = false.
Proof.
  unfold VarMapProperties.for_all.
  setoid_rewrite VarMap.fold_1.
  setoid_rewrite VarMapProperties.F.elements_mapsto_iff.
  setoid_rewrite SetoidList.InA_alt.
  intros T m f.
  induction (VarMap.elements m) as [|a l]; intros.
  inversion H.
  destruct a. simpl in *.
  destruct (f k t) eqn:HH.
  edestruct IHl; auto.
  repeat match goal with
  | [x : _ * _ |- _ ] => destruct x
  | [H : exists _, _ |- _] => destruct H
  | [H : _ /\ _ |- _] => destruct H
  end.
  match goal with
    [H : VarMap.eq_key_elt _ _ |- _] => inversion H
  end. simpl in *. subst.
  repeat eexists; eauto.
  repeat eexists; intuition.
Qed.

Lemma not_for_all_rev : forall T (t : VarMap.t T) P,
  (exists k v, VarMap.MapsTo k v t /\ P k v = false) ->
  VarMapProperties.for_all P t = false.
Proof.
  intros.
  repeat deex.
  apply Bool.not_true_is_false.
  intro.
  rewrite VarMapProperties.for_all_iff in * by congruence.
  rewrite H in H1 by auto. inversion H1.
Qed.

Lemma not_for_all_iff : forall T (t : VarMap.t T) P,
  (exists k v, VarMap.MapsTo k v t /\ P k v = false) <->
  VarMapProperties.for_all P t = false.
Proof.
  split.
  apply not_for_all_rev.
  apply not_for_all_if.
Qed.

Lemma for_all_mem_disagree : forall T (m1 m2 : VarMap.t T),
  VarMapProperties.for_all (fun k _ => negb (VarMap.mem k m1)) m2 = false ->
  VarMapProperties.for_all (fun k _ => negb (VarMap.mem k m2)) m1 = true ->
  False.
Proof.
  intros.
  apply not_for_all_iff in H.
  destruct H as [k [v [H H']]].
  rewrite VarMapProperties.for_all_iff in H0; try congruence.
  rewrite Bool.negb_false_iff in *.
  setoid_rewrite Bool.negb_true_iff in H0.
  rewrite <- VarMapProperties.F.mem_in_iff in *.
  rewrite VarMapProperties.F.in_find_iff in *.
  destruct (VarMap.find k m1) eqn:HH.
  apply VarMap.find_2 in HH.
  apply H0 in HH.
  rewrite <- VarMapProperties.F.not_mem_in_iff in *.
  contradiction HH.
  apply VarMapProperties.F.in_find_iff.
  rewrite VarMapProperties.F.find_mapsto_iff in H.
  rewrite H. intro H''. inversion H''.
  contradiction H'; auto.
Qed.

Lemma maps_disjoint_comm :
  forall T m1 m2, @maps_disjoint T m1 m2 = maps_disjoint m2 m1.
Proof.
  unfold maps_disjoint.
  intros.
  match goal with
    | [ |- context[VarMapProperties.for_all ?p m1] ] => case_eq (VarMapProperties.for_all p m1)
  end;
  match goal with
    | [ |- context[VarMapProperties.for_all ?p m2] ] => case_eq (VarMapProperties.for_all p m2)
  end; try congruence;
    intros; exfalso; eapply for_all_mem_disagree; eauto.
Qed.

Lemma mapsto_in : forall T k v (t : VarMap.t T),
  VarMap.MapsTo k v t -> VarMap.In k t.
Proof.
  intros.
  apply VarMapProperties.F.in_find_iff.
  find_eapply_lem_hyp VarMap.find_1.
  intro. rewrite H in *. inversion H0.
Qed.

Hint Resolve mapsto_in.

Lemma maps_disjoint_in' : forall T k (t0 t1 : VarMap.t T),
  maps_disjoint t0 t1 = true ->
  VarMap.In k t0 -> ~VarMap.In k t1.
Proof.
  unfold maps_disjoint.
  intros.
  find_eapply_lem_hyp VarMapProperties.F.in_find_iff.
  destruct VarMap.find eqn:H'.
  find_eapply_lem_hyp for_all_if; try congruence.
  rewrite Bool.negb_true_iff in *.
  apply VarMapProperties.F.not_mem_in_iff. eauto.
  apply VarMap.find_2. eauto.
  contradiction H0; auto.
Qed.

Lemma maps_disjoint_in : forall T k (t0 t1 : VarMap.t T),
  maps_disjoint t0 t1 = true ->
  VarMap.In k t0 -> VarMap.In k t1 -> False.
Proof.
  intros.
  find_eapply_lem_hyp maps_disjoint_in'; eauto.
  rewrite maps_disjoint_comm. auto.
Qed.

Hint Resolve maps_disjoint_in.

Lemma maps_disjoint_assoc : forall T (t0 t1 t2 : VarMap.t T),
  maps_disjoint t0 (VarMapProperties.update t1 t2) = true ->
  maps_disjoint t1 t2 = true ->
  maps_disjoint t2 (VarMapProperties.update t1 t0) = true.
Proof.
  intros.
  rewrite maps_disjoint_comm.
  pose proof H.
  unfold maps_disjoint in H. unfold maps_disjoint.
  rewrite VarMapProperties.for_all_iff in *; try congruence.
  intros. apply Bool.negb_true_iff.
  setoid_rewrite Bool.negb_true_iff in H.
  find_eapply_lem_hyp VarMapProperties.update_mapsto_iff.
  apply VarMapProperties.F.not_mem_in_iff.
  intuition; eauto.
  find_eapply_lem_hyp H.
  find_eapply_lem_hyp VarMapProperties.F.not_mem_in_iff; auto.
  rewrite VarMapProperties.update_in_iff in *.
  intuition.
Qed.

Lemma maps_disjoint_empty : forall T (t : VarMap.t T),
  maps_disjoint t (VarMap.empty _) = true.
Proof.
  intros.
  unfold maps_disjoint; simpl; auto.
  apply VarMapProperties.for_all_iff; intuition.
Qed.

Definition sep_star_impl (p1 p2 : pred) : pred :=
  match p1, p2 with
    | Some m1, Some m2 =>
      if maps_disjoint m1 m2
      then Some (VarMapProperties.update m1 m2)
      else None
    | _, _ => None
  end.

Module Type SEP_STAR.
  Parameter sep_star : pred -> pred -> pred.
  Axiom sep_star_is : @sep_star = @sep_star_impl.
End SEP_STAR.

Module Sep_Star : SEP_STAR.
  Definition sep_star := @sep_star_impl.
  Theorem sep_star_is : @sep_star = @sep_star_impl.
  Proof. auto. Qed.
End Sep_Star.

Definition sep_star := @Sep_Star.sep_star.
Definition sep_star_is := Sep_Star.sep_star_is.

Infix "|->" := ptsto (at level 35) : go_pred_scope.
Bind Scope go_pred_scope with pred.

Delimit Scope go_pred_scope with go_pred.

Notation "k ~> v" := (k |-> (SItem v))%go_pred (at level 35) : go_pred_scope.

Infix "*" := sep_star : go_pred_scope.
Notation "∅" := any : go_pred_scope.
Notation "p =p=> q" := (pimpl p%go_pred q%go_pred) (right associativity, at level 60) : go_pred_scope.
Notation "m ## p" := (pred_matches p%go_pred m) (at level 70).

Local Open Scope go_pred.

Ltac unfold_sep_star := unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.

Theorem sep_star_comm :
  forall p1 p2,
    p1 * p2 =p=> p2 * p1.
Proof.
  unfold pimpl, pred_matches.
  unfold_sep_star.
  intros.
  destruct p1, p2; eauto.
  rewrite maps_disjoint_comm.
  case_eq (maps_disjoint t t0); intro He; rewrite ?He in *; auto; intros.
  destruct item.
  specialize (H k (SItem v)). simpl in *.
  find_eapply_lem_hyp VarMap.find_2.
  destruct (VarMapProperties.update_mapsto_iff t t0 k (SItem v));
  destruct (VarMapProperties.update_mapsto_iff t0 t k (SItem v)).
  intuition; apply H, VarMap.find_1; intuition; eauto.
Qed.

Theorem maps_disjoint_update_eq' : forall T (t0 t1 : VarMap.t T),
  maps_disjoint t0 t1 = true ->
  VarMap.Equal (VarMapProperties.update t0 t1) (VarMapProperties.update t1 t0).
Proof.
  intros.
  unfold VarMap.Equal; intros.
  destruct VarMap.find eqn:H'; symmetry.
  rewrite <- VarMapProperties.F.find_mapsto_iff in *.
  rewrite VarMapProperties.update_mapsto_iff in *.
  intuition. right; eauto.
  rewrite <- VarMapProperties.F.not_find_in_iff in *.
  intuition.
  rewrite VarMapProperties.update_in_iff in *.
  firstorder.
Qed.

Theorem maps_disjoint_update_eq : forall T (t t0 t1 : VarMap.t T),
  maps_disjoint t (VarMapProperties.update t0 t1) =
  maps_disjoint t (VarMapProperties.update t1 t0).
Proof.
  intros.
  destruct maps_disjoint eqn:H; symmetry; unfold maps_disjoint in *.
  rewrite VarMapProperties.for_all_iff in * by congruence.
  intros.
  find_eapply_lem_hyp H.
  rewrite Bool.negb_true_iff in *.
  rewrite <- VarMapProperties.F.not_mem_in_iff in *.
  rewrite VarMapProperties.update_in_iff in *; intuition.
  rewrite <- not_for_all_iff in *.
  repeat deex; repeat eexists;
    rewrite ?Bool.negb_false_iff in *; eauto.
  rewrite <- VarMapProperties.F.mem_in_iff in *.
  rewrite VarMapProperties.update_in_iff in *; intuition.
Qed.

Theorem maps_not_disjoint : forall T (t0 t1 : VarMap.t T),
  maps_disjoint t0 t1 = false ->
  exists k, VarMap.In k t0 /\ VarMap.In k t1.
Proof.
  unfold maps_disjoint.
  intros.
  find_eapply_lem_hyp not_for_all_iff.
  repeat deex.
  rewrite Bool.negb_false_iff in *.
  eexists; split; eauto.
  apply VarMapProperties.F.mem_in_iff; auto.
Qed.

Theorem sep_star_assoc_1 :
  forall p1 p2 p3,
    p1 * p2 * p3 =p=> p1 * (p2 * p3).
Proof.
  unfold pimpl, pred_matches.
  unfold sep_star.
  intros.
  destruct p1, p2, p3;
    rewrite sep_star_is in *; simpl in *;
    repeat (match goal with
    | [H : context [if ?X then _ else _] |- _ ] => let H := fresh in destruct X eqn:H
    | [|- context [if ?X then _ else _]] => let H := fresh in destruct X eqn:H
    end; simpl in *); intros; auto; intuition.

  intros.
  apply H.
  rewrite <- VarMapProperties.F.find_mapsto_iff in *.
  repeat rewrite VarMapProperties.update_mapsto_iff in *.
  rewrite VarMapProperties.update_in_iff in *.
  intuition.
  apply Bool.not_true_iff_false in H3; contradiction H3.
  rewrite maps_disjoint_comm in H1.
  eapply maps_disjoint_assoc; [rewrite maps_disjoint_update_eq |]; auto.
  rewrite maps_disjoint_comm; auto.
  find_eapply_lem_hyp maps_not_disjoint. deex.
  eapply maps_disjoint_in; eauto.
  apply VarMapProperties.update_in_iff; auto.
Qed.

Theorem sep_star_assoc_2 :
  forall p1 p2 p3,
    p1 * (p2 * p3) =p=> p1 * p2 * p3.
Proof.
  unfold pimpl, pred_matches.
  unfold sep_star.
  intros.
  destruct p1, p2, p3;
    rewrite sep_star_is in *; simpl in *;
    repeat (match goal with
    | [H : context [if ?X then _ else _] |- _ ] => let H := fresh in destruct X eqn:H
    | [|- context [if ?X then _ else _]] => let H := fresh in destruct X eqn:H
    end; simpl in *); intros; auto; intuition.

  intros.
  apply H.
  rewrite <- VarMapProperties.F.find_mapsto_iff in *.
  repeat rewrite VarMapProperties.update_mapsto_iff in *.
  rewrite VarMapProperties.update_in_iff in *.
  intuition.
  apply Bool.not_true_iff_false in H3; contradiction H3.
  rewrite maps_disjoint_comm.
  rewrite maps_disjoint_update_eq.
  eapply maps_disjoint_assoc; auto.
  find_eapply_lem_hyp maps_not_disjoint. deex.
  eapply maps_disjoint_in; eauto.
  apply VarMapProperties.update_in_iff; auto.
Qed.

Theorem pimpl_refl :
  forall p, p =p=> p.
Proof.
  unfold pimpl. eauto.
Qed.

Theorem pimpl_trans :
  forall p q r,
    p =p=> q ->
    q =p=> r ->
    p =p=> r.
Proof.
  intros.
  unfold pimpl in *.
  firstorder.
Qed.

Theorem pimpl_apply :
  forall p q m,
    p =p=> q ->
    m ## p ->
    m ## q.
Proof.
  intros.
  firstorder.
Qed.

Theorem pimpl_l :
  forall p q,
    p * q =p=> p.
Proof.
  unfold pimpl, pred_matches, sep_star;
    rewrite sep_star_is.
  destruct p, q; simpl; intros; intuition.
  destruct maps_disjoint eqn:H'; intuition.
  apply H.
  rewrite <- VarMapProperties.F.find_mapsto_iff in *.
  apply VarMapProperties.update_mapsto_iff.
  intuition; eauto.
Qed.

Theorem pimpl_r :
  forall p q,
    p * q =p=> q.
Proof.
  intros. intro; intros.
  eapply pimpl_l.
  apply sep_star_comm; eauto.
Qed.

Theorem pimpl_any :
  forall p,
    p =p=> any.
Proof.
  unfold pimpl, pred_matches.
  destruct p; simpl; intros; intuition.
  rewrite VarMapProperties.F.empty_o in *.
  inversion H0.
Qed.

Theorem any_l_1 :
  forall p,
    p =p=> p * any.
Proof.
  unfold pimpl, pred_matches, sep_star;
    rewrite sep_star_is.
  destruct p; simpl in *; intuition.
  rewrite maps_disjoint_empty; intros.
  apply H.
  rewrite <- VarMapProperties.F.find_mapsto_iff in *.
  find_eapply_lem_hyp VarMapProperties.update_mapsto_iff.
  intuition; eauto.
  rewrite VarMapProperties.F.empty_mapsto_iff in *; intuition.
Qed.

Theorem any_l_2 :
  forall p,
    p * any =p=> p.
Proof.
  intros. apply pimpl_l.
Qed.

Theorem any_r_1 :
  forall p,
    p =p=> any * p.
Proof.
  unfold pimpl, pred_matches, sep_star;
    rewrite sep_star_is.
  destruct p; simpl in *; intuition.
  apply H.
  rewrite <- VarMapProperties.F.find_mapsto_iff in *.
  find_eapply_lem_hyp VarMapProperties.update_mapsto_iff.
  intuition; eauto.
  rewrite VarMapProperties.F.empty_mapsto_iff in *; intuition.
Qed.

Theorem any_r_2 :
  forall p,
    any * p =p=> p.
Proof.
  intros. apply pimpl_r.
Qed.

(* TODO move this *)
Lemma update_add_empty : forall T (t : VarMap.t T) k v,
  VarMapProperties.update t (VarMap.add k v (VarMap.empty _)) = VarMap.add k v t.
Proof.
  intros.
  unfold VarMapProperties.update.
  rewrite VarMap.fold_1. auto.
Qed.

Theorem ptsto_find :
  forall A {H : GoWrapper A} k (v : A) F m,
    m ## k ~> v * F ->
    VarMap.find k m = Some (wrap v).
Proof.
  unfold pred_matches, ptsto.
  unfold_sep_star.
  intros.
  break_match; intuition.
  break_match; subst.
  break_match. find_inversion.
  specialize (H0 k (SItem v)). simpl in *.
  apply H0.
  rewrite maps_disjoint_update_eq' by auto.
  rewrite update_add_empty.
  apply VarMapProperties.F.add_eq_o; auto.
  all : inversion Heqp.
Qed.

Theorem ptsto_update :
  forall A {H : GoWrapper A} k (v : A) F m,
    ~ VarMap.In k m ->
    m ## F ->
    VarMap.add k (wrap v) m ## k ~> v * F.
Proof.
  unfold pred_matches, ptsto, sep_star.
  rewrite sep_star_is.
  intros.
  destruct F; simpl in *; intuition.
  destruct maps_disjoint eqn:H'; intros.
  rewrite maps_disjoint_update_eq' in * by auto.
  rewrite update_add_empty in *.
  rewrite VarMapProperties.F.add_o in *.
  destruct Nat_as_OT.eq_dec; subst.
  find_inversion; auto.
  firstorder.
  apply maps_not_disjoint in H' as H''.
  deex.
  rewrite VarMapProperties.F.add_in_iff in *.
  intuition; subst.
 
  rewrite VarMapProperties.F.in_find_iff in *.
  destruct VarMap.find eqn:H''.
  find_eapply_lem_hyp H1.
  destruct s.
  apply H0. rewrite H''. intro.
  inversion H3.
  apply H4. auto.
  find_eapply_lem_hyp VarMapProperties.F.empty_in_iff. auto.
Qed.

Lemma pimpl_sep_star :
  forall a b c d,
  (a =p=> c) ->
  (b =p=> d) ->
  (a * b =p=> c * d).
Proof.
  unfold pimpl; unfold_sep_star; intros.
  destruct a, b; try solve [ simpl pred_matches in *; intuition idtac ].
Admitted.

Lemma pimpl_cancel_one :
  forall p q k v,
    p =p=> q ->
    p * k |-> v =p=> q * k |-> v.
Admitted.


Instance pimpl_preorder :
  PreOrder pimpl.
Proof.
  split.
  exact pimpl_refl.
  exact pimpl_trans.
Qed.

Instance pred_apply_pimpl_proper :
  Proper (pimpl ==> eq ==> Basics.impl) pred_matches.
Proof.
  unfold pimpl, pred_matches.
  intros p q Hpq ma mb Hmab H.
  destruct p, q; intuition subst.
  eapply Hpq; eauto.
  apply Hpq in H; trivial.
Qed.

Instance pimpl_pimpl_proper1 :
  Proper (pimpl ==> Basics.flip pimpl ==> Basics.flip Basics.impl) pimpl.
Proof.
  firstorder.
Qed.

Instance pimpl_pimpl_proper2 :
  Proper (Basics.flip pimpl ==> pimpl ==> Basics.impl) pimpl.
Proof.
  firstorder.
Qed.

Instance sep_star_pimpl_proper :
  Proper (pimpl ==> pimpl ==> pimpl) sep_star.
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.


Instance sep_star_pimpl_proper' :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> Basics.flip pimpl) sep_star.
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.