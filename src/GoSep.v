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

Definition emp : pred := Some (VarMap.empty _).

Definition ptsto var val : pred := Some (VarMap.add var val (VarMap.empty _)).

Module VarMapProperties := FMapFacts.WProperties_fun(Nat_as_OT)(VarMap).

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
  end; try congruence; intros; exfalso.
Admitted.

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
Notation "∅" := emp : go_pred_scope.
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
  eapply VarMap.find_1.
  find_eapply_lem_hyp VarMap.find_2.
  pose proof (VarMapProperties.update_mapsto_iff t t0 k (SItem v)).
  pose proof (VarMapProperties.update_mapsto_iff t0 t k (SItem v)).
Admitted.

Theorem sep_star_assoc_1 :
  forall p1 p2 p3,
    p1 * p2 * p3 =p=> p1 * (p2 * p3).
Proof.
Admitted.

Theorem sep_star_assoc_2 :
  forall p1 p2 p3,
    p1 * (p2 * p3) =p=> p1 * p2 * p3.
Proof.
Admitted.

Theorem pimpl_refl :
  forall p, p =p=> p.
Admitted.

Theorem pimpl_trans :
  forall p q r,
    p =p=> q ->
    q =p=> r ->
    p =p=> r.
Admitted.

Theorem pimpl_apply :
  forall p q m,
    p =p=> q ->
    m ## p ->
    m ## q.
Proof.
  intros.
Admitted.

Theorem pimpl_l :
  forall p q,
    p * q =p=> p.
Admitted.

Theorem pimpl_r :
  forall p q,
    p * q =p=> q.
Admitted.

Theorem emp_l_1 :
  forall p,
    p =p=> p * emp.
Admitted.

Theorem emp_l_2 :
  forall p,
    p * emp =p=> p.
Admitted.

Theorem ptsto_find :
  forall A {H : GoWrapper A} k (v : A) F m,
    m ## k ~> v * F ->
    VarMap.find k m = Some (wrap v).
Proof.
  unfold pred_matches, ptsto.
  unfold_sep_star.
  intros.
  break_match; intuition.
Admitted.

Theorem ptsto_update :
  forall A {H : GoWrapper A} k (v : A) F m,
    m ## F ->
    VarMap.add k (wrap v) m ## k ~> v * F.
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
