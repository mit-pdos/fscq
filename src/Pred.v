Require Import Arith.
Require Import Omega.
Require Import FunctionalExtensionality.
Require Import ProofIrrelevance.
Require Import Mem.
Require Import RelationClasses.
Require Import Morphisms.
Require Import Automation.
Require Import List.

Set Implicit Arguments.


(** ** Predicates *)

Section GenPredDef.

Variable AT : Type.
Variable AEQ : DecEq AT.
Variable V : AT -> Type.

Definition pred := @mem AT AEQ V -> Prop.

Implicit Type m : @mem AT AEQ V.
Implicit Types p q : pred.

Definition ptsto (a : AT) (v : V a) : pred :=
  fun m => m a = Some v /\ forall a', a <> a' -> m a' = None.

Definition impl p q : pred :=
  fun m => p m -> q m.

Definition and p q : pred :=
  fun m => p m /\ q m.

Definition or p q : pred :=
  fun m => p m \/ q m.

Definition foral_ A (p : A -> pred) : pred :=
  fun m => forall x, p x m.

Definition exis A (p : A -> pred) : pred :=
  fun m => exists x, p x m.

Definition uniqpred A (p : A -> pred) (x : A) : pred :=
  fun m => p x m /\ (forall (x' : A), p x' m -> x = x').

Definition emp : pred :=
  fun m => forall a, m a = None.

Definition any : pred :=
  fun m => True.

Definition lift (P : Prop) : pred :=
  fun m => P.

Definition lift_empty (P : Prop) : pred :=
  fun m => P /\ forall a, m a = None.

Definition pimpl p q := forall m, p m -> q m.

Definition piff p q : Prop := (pimpl p q) /\ (pimpl q p).

Definition mem_disjoint m1 m2 :=
  ~ exists a (v1 v2 : V a), m1 a = Some v1 /\ m2 a = Some v2.

Definition mem_union m1 m2 : (@mem AT AEQ V) := fun a =>
  match m1 a with
  | Some v => Some v
  | None => m2 a
  end.

Definition sep_star_impl p1 p2 : pred :=
  fun m => exists m1 m2, m = mem_union m1 m2 /\ mem_disjoint m1 m2 /\ p1 m1 /\ p2 m2.

Definition septract p q : pred :=
  fun m => exists m1, mem_disjoint m m1 /\ p m1 /\ q (mem_union m m1).

Definition indomain (a: AT) m :=
  exists (v:V a), m a = Some v.

Definition notindomain (a : AT) m :=
  m a = None.

Definition diskIs m : pred :=
  fun m' => m = m'.

Definition mem_except m (a: AT) : @mem AT AEQ V :=
  fun a' => if AEQ a' a then None else m a'.

Definition pred_apply m p := p m.

Definition strictly_exact p : Prop :=
  forall m1 m2, p m1 -> p m2 -> m1 = m2.

Definition exact_domain p : Prop :=
  forall m1 m2, p m1 -> p m2 -> (forall a, m1 a = None <-> m2 a = None).

Definition precise p : Prop :=
  forall m1 m1' m2 m2',
  mem_union m1 m1' = mem_union m2 m2' ->
  mem_disjoint m1 m1' ->
  mem_disjoint m2 m2' ->
  p m1 -> p m2 -> m1 = m2.

End GenPredDef.

Arguments pred {AT AEQ V}.
Arguments emp {AT AEQ V} _.
Arguments any {AT AEQ V} _.
Arguments pimpl {AT AEQ V} _ _.
Arguments piff {AT AEQ V} _ _.
Arguments sep_star_impl {AT AEQ V} _ _ _.
Arguments septract {AT AEQ V} _ _ _.
Arguments indomain {AT AEQ V} _ _.
Arguments notindomain {AT AEQ V} _ _.
Arguments diskIs {AT AEQ V} _ _.
Arguments pred_apply {AT AEQ V} _ _.
Arguments strictly_exact {AT AEQ V} _.
Arguments exact_domain {AT AEQ V} _.
Arguments precise {AT AEQ V} _.

Hint Unfold pimpl.
Hint Unfold piff.

Infix "|->" := ptsto (at level 35) : pred_scope.
Bind Scope pred_scope with pred.
Delimit Scope pred_scope with pred.

Infix "-p->" := impl (right associativity, at level 95) : pred_scope.
Infix "/\" := and : pred_scope.
Infix "\/" := or : pred_scope.
Notation "'foral' x .. y , p" := (foral_ (fun x => .. (foral_ (fun y => p)) ..)) (at level 200, x binder, right associativity) : pred_scope.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : pred_scope.
Notation "a |->?" := (exists v, a |-> v)%pred (at level 35) : pred_scope.
Notation "'exists' ! x .. y , p" := (exis (uniqpred (fun x => .. (exis (uniqpred (fun y => p))) ..))) : pred_scope.
Notation "[ P ]" := (lift P) : pred_scope.
Notation "[[ P ]]" := (lift_empty P) : pred_scope.
Notation "p =p=> q" := (pimpl p%pred q%pred) (right associativity, at level 90).
Notation "p <=p=> q" := (piff p%pred q%pred) (at level 90).
Notation "m ## p" := (pred_apply m p%pred) (at level 90).

Theorem exists_unique_incl_exists : forall A P,
  (exists ! (x:A), P x) -> exists (x:A), P x.
Proof.
  intros.
  inversion H.
  inversion H0.
  eauto.
Qed.

Module Sep_Star.
  Definition sep_star : forall {AT:Type} {AEQ:DecEq AT} {V:AT -> Type}, @pred AT AEQ V -> @pred AT AEQ V -> @pred AT AEQ V  := @sep_star_impl.
  Theorem sep_star_is : @sep_star = @sep_star_impl.
  Proof. auto. Qed.
End Sep_Star.

Definition sep_star := @Sep_Star.sep_star.
Definition sep_star_is := Sep_Star.sep_star_is.
Arguments sep_star {AT AEQ V} _ _ _.
Infix "*" := sep_star : pred_scope.
Notation "p --* q" := (septract p%pred q%pred) (at level 40) : pred_scope.

Ltac deex_this H name :=
  let name := fresh name in
  destruct H as [name ?]; intuition subst.

Ltac deex' t :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    t H varname
  | [ H : (exists (varname : _), _)%pred _ |- _ ] =>
    t H varname
  end.

Ltac deex := deex' deex_this.

Ltac destruct_and H :=
  match type of H with
  | _ /\ _ =>
    let Hl := fresh in
    let Hr := fresh in
    destruct H as [Hl Hr];
      destruct_and Hr
  | (and _ _) _ =>
    unfold and in H at 1;
    destruct_and H
  | _ => idtac
  end.

Ltac deex_this_local H name :=
  let name := fresh name in
  destruct H as [name ?];
  destruct_and H.

Ltac deex_local := deex' deex_this_local.

Ltac deex_unique :=
  match goal with
  | [ H : exists ! (varname : _), _ |- _] =>
    let newvar := fresh varname in
    let Hunique := fresh in
    let Huniqueness := fresh "H" newvar "_uniq" in
    destruct H as [newvar Hunique];
    inversion Hunique as [? Huniqueness]; clear Hunique;
    intuition subst
  end.

Ltac pred_unfold :=
  unfold impl, and, or, foral_, exis, uniqpred, lift in *.
Ltac pred := pred_unfold;
  repeat (repeat deex; simpl in *;
    intuition (try (congruence || omega);
      try autorewrite with core in *; eauto); try subst).

Tactic Notation "unfold_sep_star" :=
  unfold sep_star; rewrite sep_star_is; unfold sep_star_impl.
Tactic Notation "unfold_sep_star" "in" hyp(H) :=
  unfold sep_star in H; rewrite sep_star_is in H; unfold sep_star_impl in H.
Tactic Notation "unfold_sep_star" "at" integer(K) "in" hyp(H) :=
  unfold sep_star in H at K; rewrite sep_star_is in H; unfold sep_star_impl in H.
Tactic Notation "unfold_sep_star" "at" integer(K) :=
  unfold sep_star at K; rewrite sep_star_is; unfold sep_star_impl.


Section GenPredThm.

Set Default Proof Using "Type".

Variable AT : Type.
Variable AEQ : DecEq AT.
Variable V : AT -> Type.

Implicit Type m : @mem AT AEQ V.
Implicit Type p q : @pred AT AEQ V.

Theorem pimpl_refl : forall p, p =p=> p.
Proof.
  pred.
Qed.

Hint Resolve pimpl_refl.

Theorem mem_disjoint_comm:
  forall m1 m2,
  mem_disjoint m1 m2 <-> mem_disjoint m2 m1.
Proof.
  split; unfold mem_disjoint, not; intros; repeat deex; eauto 10.
Qed.

Theorem mem_disjoint_assoc_1:
  forall m1 m2 m3,
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_disjoint m1 (mem_union m2 m3).
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  case_eq (m2 a); intros.
  - apply H. eauto.
  - rewrite H1 in H3.
    apply H0. repeat eexists; eauto. rewrite H2. eauto.
Qed.

Theorem mem_disjoint_assoc_2:
  forall m1 m2 m3,
  mem_disjoint m2 m3 ->
  mem_disjoint m1 (mem_union m2 m3) ->
  mem_disjoint (mem_union m1 m2) m3.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  case_eq (m2 a); intros.
  - apply H. eauto.
  - case_eq (m1 a); intros.
    + apply H0. repeat eexists; eauto. rewrite H1. eauto.
    + rewrite H4 in H2. firstorder.
Qed.

Theorem mem_disjoint_union:
  forall m1 m2 m3,
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_disjoint m2 m3.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  apply H; exists a; destruct (m1 a); eauto.
Qed.

Theorem mem_disjoint_union_2:
  forall m1 m2 m3,
  mem_disjoint m1 (mem_union m2 m3) ->
  mem_disjoint m1 m2.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  apply H; exists a. destruct (m1 a); destruct (m2 a); try congruence; eauto.
Qed.

Theorem mem_disjoint_union_parts : forall m1 m2 m3,
  mem_disjoint m1 m3 ->
  mem_disjoint m2 m3 ->
  mem_disjoint (mem_union m1 m2) m3.
Proof.
  intros.
  unfold mem_disjoint, mem_union.
  intro Hfalse.
  repeat deex.
  case_eq (m1 a); intros.
  apply H.
  repeat eexists; eauto.
  apply H0.
  rewrite H1 in H2.
  repeat eexists; eauto.
Qed.

Theorem mem_disjoint_upd:
  forall m1 m2 a v v0,
  m1 a = Some v0 ->
  mem_disjoint m1 m2 ->
  mem_disjoint (upd m1 a v) m2.
Proof.
  unfold mem_disjoint, upd, not; intros; repeat deex;
    destruct (AEQ a0 a); subst; eauto 10.
Qed.

Lemma mem_disjoint_either:
  forall m1 m2 a v,
  mem_disjoint m1 m2
  -> m1 a = Some v -> m2 a = None.
Proof.
  unfold mem_disjoint; intros; firstorder.
  pose proof (H a); firstorder.
  pose proof (H1 v); firstorder.
  destruct (m2 a); auto.
  pose proof (H2 v0); firstorder.
Qed.

Theorem mem_union_comm:
  forall m1 m2,
  mem_disjoint m1 m2 ->
  mem_union m1 m2 = mem_union m2 m1.
Proof.
  unfold mem_disjoint, mem_union; intros; extensionality a; intros.
  case_eq (m1 a); case_eq (m2 a); intros; eauto; destruct H; eauto.
Qed.


Theorem mem_disjoint_union_cancel:
  forall m1 m2 m2',
  mem_disjoint m1 m2 ->
  mem_disjoint m1 m2' ->
  mem_union m1 m2 = mem_union m1 m2' ->
  m2 = m2'.
Proof.
  intros.
  rewrite mem_union_comm in H1 by auto.
  replace (mem_union m1 m2') with (mem_union m2' m1) in H1 by
    (apply mem_union_comm; apply mem_disjoint_comm; auto).
  extensionality a.
  assert (mem_union m2 m1 a = mem_union m2' m1 a) by congruence.
  unfold mem_disjoint, mem_union in *.
  case_eq (m2 a); case_eq (m2' a); intros;
    replace (m2 a) in *; replace (m2' a) in *;
    eauto.
  destruct H.
  repeat eexists; eauto.
  destruct H0.
  repeat eexists; eauto.
Qed.

Theorem mem_disjoint_union_cancel_r:
  forall m1 m1' m2,
  mem_disjoint m1 m2 ->
  mem_disjoint m1' m2 ->
  mem_union m1 m2 = mem_union m1' m2 ->
  m1 = m1'.
Proof.
  intros.
  rewrite mem_union_comm in H1; auto.
  rewrite mem_union_comm with (m1 := m1') in H1; auto.
  eapply mem_disjoint_union_cancel; eauto.
  apply mem_disjoint_comm; auto.
  apply mem_disjoint_comm; auto.
Qed.

Theorem disjoint_union_comm_eq : forall (m1a m1b m2a m2b : @mem AT AEQ V),
    mem_union m1a m1b = mem_union m2a m2b ->
    mem_disjoint m1a m1b ->
    mem_disjoint m2a m2b ->
    mem_union m1b m1a = mem_union m2b m2a.
Proof.
  intros.
  rewrite mem_union_comm with (m1 := m1b).
  rewrite mem_union_comm with (m1 := m2b).
  auto.
  rewrite mem_disjoint_comm; auto.
  rewrite mem_disjoint_comm; auto.
Qed.

Theorem mem_union_addr:
  forall m1 m2 a v,
  mem_disjoint m1 m2 ->
  m1 a = Some v ->
  mem_union m1 m2 a = Some v.
Proof.
  unfold mem_disjoint, mem_union; intros; rewrite H0; auto.
Qed.

Lemma mem_union_ptsto_to_upd : forall (m1 m2: @mem AT AEQ V) a v,
    mem_disjoint m1 m2 ->
    (a |-> v)%pred m2 ->
    mem_union m1 m2 = upd m1 a v.
Proof.
  unfold ptsto, mem_disjoint, mem_union; intuition.
  extensionality a'; destruct (AEQ a a'); subst;
  autorewrite with upd.
  case_eq (m1 a'); intros; auto.
  exfalso; eapply H; eauto.
  erewrite H2; eauto.
  destruct (m1 a'); auto.
Qed.

Require Import Eqdep_dec.

Theorem mem_union_upd:
  forall m1 m2 a v v0,
  m1 a = Some v0 ->
  mem_union (upd m1 a v) m2 = upd (mem_union m1 m2) a v.
Proof.
  unfold mem_union; intros; extensionality a'.
  destruct (AEQ a' a); now simpl_upd.
Qed.

Theorem mem_union_assoc:
  forall m1 m2 m3,
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_union (mem_union m1 m2) m3 = mem_union m1 (mem_union m2 m3).
Proof.
  unfold mem_union, mem_disjoint; intros; extensionality a.
  destruct (m1 a); auto.
Qed.

Theorem sep_star_comm1:
  forall p1 p2,
  (p1 * p2 =p=> p2 * p1)%pred.
Proof.
  unfold pimpl; unfold_sep_star; pred.
  exists m2; exists m1. intuition eauto using mem_union_comm. apply mem_disjoint_comm; auto.
Qed.

Theorem sep_star_comm:
  forall p1 p2,
  (p1 * p2 <=p=> p2 * p1)%pred.
Proof.
  unfold piff; split; apply sep_star_comm1.
Qed.

Theorem sep_star_assoc_1:
  forall p1 p2 p3,
  (p1 * p2 * p3 =p=> p1 * (p2 * p3))%pred.
Proof.
  unfold pimpl; unfold_sep_star; pred.
  eexists; eexists (mem_union _ _); intuition eauto.
  apply mem_union_assoc; auto.
  apply mem_disjoint_assoc_1; auto.
  eexists; eexists; intuition eauto.
  eapply mem_disjoint_union; eauto.
Qed.

Theorem sep_star_assoc_2:
  forall p1 p2 p3,
  (p1 * (p2 * p3) =p=> p1 * p2 * p3)%pred.
Proof.
  unfold pimpl; unfold_sep_star; pred.
  eexists (mem_union _ _); eexists; intuition eauto.
  rewrite mem_union_assoc; auto.
  apply mem_disjoint_comm. eapply mem_disjoint_union. apply mem_disjoint_comm.
  rewrite mem_union_comm. eauto. apply mem_disjoint_comm. eauto.
  apply mem_disjoint_assoc_2; eauto.
  apply mem_disjoint_assoc_2; eauto.
  repeat eexists; eauto.
  apply mem_disjoint_comm. eapply mem_disjoint_union.
  rewrite mem_union_comm; [|apply mem_disjoint_comm;eassumption].
  apply mem_disjoint_comm; assumption.
Qed.

Theorem sep_star_assoc:
  forall p1 p2 p3,
  (p1 * p2 * p3 <=p=> p1 * (p2 * p3))%pred.
Proof.
  split; [ apply sep_star_assoc_1 | apply sep_star_assoc_2 ].
Qed.

Theorem sep_star_mem_union :
  forall p q mp mq,
  mem_disjoint mp mq ->
  p mp -> q mq ->
  (p * q)%pred (mem_union mp mq).
Proof.
  unfold_sep_star; intros.
  do 2 eexists; intuition.
Qed.

Local Hint Extern 1 =>
  match goal with
    | [ |- upd _ ?a ?v ?a = Some ?v ] => apply upd_eq; auto
  end.

Lemma pimpl_exists_l:
  forall T (p:T -> pred) q,
  (forall x:T, p x =p=> q) ->
  (exists x:T, p x) =p=> q.
Proof.
  firstorder.
Qed.

Lemma pimpl_exists_r:
  forall T p (q:T -> pred),
  (exists x:T, p =p=> q x) ->
  (p =p=> exists x:T, q x).
Proof.
  firstorder.
Qed.

Lemma pimpl_exists_l_star:
  forall T (p:T->pred) q r,
  ((exists x:T, p x * r) =p=> q) ->
  (exists x:T, p x) * r =p=> q.
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  eapply H.
  do 3 eexists.
  intuition eauto.
Qed.

Lemma exis_to_exists : forall A P m,
    (exists x:A, (P x m)) -> (exists x:A, P x)%pred m.
Proof.
  firstorder.
Qed.

Lemma pimpl_exists_r_star:
  forall T (p:T -> pred) q,
  (exists x:T, p x * q) =p=> ((exists x:T, p x) * q).
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  do 2 eexists.
  intuition eauto.
Qed.

Lemma pimpl_exists_r_star' : forall T (p: T -> pred) q,
    (exists x, p x) * q =p=> (exists x, p x * q).
Proof.
  unfold pimpl, exis; unfold_sep_star; intros.
  repeat deex.
  do 2 eexists.
  intuition eauto.
Qed.

Lemma pimpl_exists_l_and:
  forall T (p:T -> pred) q r,
  ((exists x:T, p x /\ r) =p=> q) ->
  (exists x:T, p x) /\ r =p=> q.
Proof.
  firstorder.
Qed.

(* introduce a section for implicit typing *)
Section PimplThms.

Implicit Types a b c d : @pred AT AEQ V.

Lemma pimpl_trans:
  forall a b c,
  (a =p=> b) ->
  (b =p=> c) ->
  (a =p=> c).
Proof.
  firstorder.
Qed.

Lemma pimpl_trans2:
  forall a b c,
  (b =p=> c) ->
  (a =p=> b) ->
  (a =p=> c).
Proof.
  firstorder.
Qed.

Lemma piff_trans:
  forall a b c,
  (a <=p=> b) ->
  (b <=p=> c) ->
  (a <=p=> c).
Proof.
  unfold piff; intuition; eapply pimpl_trans; eauto.
Qed.

Lemma piff_comm:
  forall a b,
  (a <=p=> b) ->
  (b <=p=> a).
Proof.
  unfold piff; intuition.
Qed.

Lemma piff_refl:
  forall a,
  (a <=p=> a).
Proof.
  unfold piff; intuition.
Qed.

Lemma pimpl_apply:
  forall p q m,
  (p =p=> q) ->
  p m ->
  q m.
Proof.
  firstorder.
Qed.

Lemma piff_apply:
  forall p q m,
  (p <=p=> q) ->
  q m ->
  p m.
Proof.
  firstorder.
Qed.

Lemma pimpl_fun_l:
  forall p,
  (fun m => p m) =p=> p.
Proof.
  firstorder.
Qed.

Lemma pimpl_fun_r:
  forall p,
  p =p=> (fun m => p m).
Proof.
  firstorder.
Qed.

Lemma pimpl_sep_star:
  forall a b c d,
  (a =p=> c) ->
  (b =p=> d) ->
  (a * b =p=> c * d).
Proof.
  unfold pimpl; unfold_sep_star; intros.
  do 2 deex.
  do 2 eexists.
  intuition eauto.
Qed.

Lemma pimpl_and:
  forall a b c d,
  (a =p=> c) ->
  (b =p=> d) ->
  (a /\ b =p=> c /\ d).
Proof.
  firstorder.
Qed.

Lemma pimpl_or : forall p q p' q',
  p =p=> p'
  -> q =p=> q'
  -> p \/ q =p=> p' \/ q'.
Proof.
  firstorder.
Qed.

Lemma sep_star_lift_l:
  forall (a: Prop) b c,
  (a -> (b =p=> c)) ->
  b * [[a]] =p=> c.
Proof.
  unfold pimpl, lift_empty; unfold_sep_star; intros.
  repeat deex.
  assert (mem_union m1 m2 = m1).
  extensionality x; unfold mem_union; intros.
  case_eq (m1 x); pred.
  rewrite H. eauto.
Qed.

Lemma sep_star_lift_r':
  forall (b: Prop) a c,
  (a =p=> [b] /\ c) ->
  (a =p=> [[b]] * c).
Proof.
  unfold pimpl, lift_empty, and; unfold_sep_star; intros.
  exists (fun _ => None).
  exists m.
  intuition firstorder.
  unfold mem_disjoint. intuition. repeat deex. congruence.
Qed.

Lemma sep_star_lift_r:
  forall a b (c: Prop),
  (a =p=> b /\ [c]) ->
  (a =p=> b * [[c]]).
Proof.
  intros.
  eapply pimpl_trans; [|apply sep_star_comm].
  apply sep_star_lift_r'.
  firstorder.
Qed.

Theorem sep_star_lift_apply : forall (a : Prop) b (m : mem),
  (b * [[a]])%pred m -> (b m /\ a).
Proof.
  unfold lift_empty; unfold_sep_star; intros.
  repeat deex.
  assert (mem_union m1 m2 = m1).
  unfold mem_union; extensionality x.
  case_eq (m1 x); pred.
  congruence.
Qed.

Theorem sep_star_lift_apply' : forall (a : Prop) b (m : mem),
  b m -> a -> (b * [[ a ]])%pred m.
Proof.
  unfold lift_empty; unfold_sep_star; intros.
  exists m. exists (fun _ => None).
  intuition.
  unfold mem_union; extensionality x.
  destruct (m x); auto.
  unfold mem_disjoint; intro.
  repeat deex.
  congruence.
Qed.

Lemma pimpl_star_emp: forall p, p =p=> emp * p.
Proof.
  unfold pimpl; unfold_sep_star; intros.
  repeat eexists; eauto.
  unfold mem_union; eauto.
  unfold mem_disjoint; pred.
Qed.

Lemma star_emp_pimpl: forall p, emp * p =p=> p.
Proof.
  unfold pimpl; unfold_sep_star; intros.
  unfold emp in *; pred.
  assert (mem_union m1 m2 = m2).
  unfold mem_union; extensionality x.
  case_eq (m1 x); intuition. rewrite H1 in H0; pred.
  pred.
Qed.

Lemma emp_star: forall p, p <=p=> (@emp AT AEQ V) * p.
Proof.
  intros; split; [ apply pimpl_star_emp | apply star_emp_pimpl ].
Qed.

Lemma piff_star_r: forall a b c,
  (a <=p=> b) ->
  (a * c <=p=> b * c).
Proof.
  unfold piff, pimpl; unfold_sep_star; intuition;
    repeat deex; repeat eexists; eauto.
Qed.

Lemma piff_star_l: forall a b c,
  (a <=p=> b) ->
  (c * a <=p=> c * b).
Proof.
  unfold piff, pimpl; unfold_sep_star; intuition;
    repeat deex; repeat eexists; eauto.
Qed.

Lemma piff_l :
  forall p p' q,
  (p <=p=> p')
  -> (p' =p=> q)
  -> (p =p=> q).
Proof.
  firstorder.
Qed.

Lemma piff_r :
  forall p q q',
  (q <=p=> q')
  -> (p =p=> q')
  -> (p =p=> q).
Proof.
  firstorder.
Qed.

Lemma sep_star_lift2and:
  forall a (b:Prop),
  (a * [[b]]) =p=> a /\ [b].
Proof.
  unfold and, lift, lift_empty, pimpl; unfold_sep_star.
  intros; repeat deex.
  assert (mem_union m1 m2 = m1).
  extensionality x.
  unfold mem_union. destruct (m1 x); eauto.
  congruence.
Qed.

Lemma sep_star_and2lift:
  forall a (b:Prop),
  (a /\ [b]) =p=> (a * [[b]]).
Proof.
  unfold and, lift, lift_empty, pimpl; unfold_sep_star.
  intros; repeat deex.
  do 2 eexists; intuition; eauto.
  - unfold mem_union.
    extensionality x. destruct (m x); auto.
  - unfold mem_disjoint, not; intros.
    repeat deex.
    congruence.
Qed.

End PimplThms.

Lemma incl_cons : forall T (a b : list T) (v : T), incl a b
  -> incl (v :: a) (v :: b).
Proof.
  firstorder.
Qed.

Lemma ptsto_valid:
  forall a v F m,
  (a |-> v * F)%pred m
  -> m a = Some v.
Proof.
  unfold ptsto; unfold_sep_star.
  intros; repeat deex.
  apply mem_union_addr; eauto.
Qed.

Lemma ptsto_valid':
  forall a v F m,
  (F * (a |-> v))%pred m
  -> m a = Some v.
Proof.
  unfold ptsto; unfold_sep_star.
  intros; repeat deex.
  rewrite mem_union_comm; eauto.
  apply mem_union_addr; eauto.
  rewrite mem_disjoint_comm; eauto.
Qed.

Lemma ptsto_valid_iff : forall a v (m : @mem AT AEQ V),
    m a = Some v ->
    (any * a |-> v)%pred m.
Proof.
  intros.
  unfold_sep_star.
  exists (mem_except m a).
  exists (upd empty_mem a v).
  intuition.
  extensionality a0.
  unfold mem_union.
  unfold mem_except.
  case_eq (AEQ a0 a); intros; subst; try simpl_upd; eauto.
  case_eq (m a0); try simpl_upd; eauto.
  unfold mem_disjoint, mem_except.
  intro.
  repeat deex.
  case_eq (AEQ a0 a); intros; eauto.
  rewrite H0 in *.
  congruence.
  rewrite H0 in *.
  rewrite upd_ne in H2 by auto.
  unfold empty_mem in H2.
  congruence.
  unfold any; auto.
  unfold ptsto; intuition.
  simpl_upd; unfold empty_mem; auto.
Qed.

Lemma ptsto_disjoint_hole:
  forall a v m1 m2,
  mem_disjoint m1 m2 ->
  (a |-> v)%pred m2 ->
  m1 a = None.
Proof.
  unfold mem_disjoint.
  intros.
  case_eq (m1 a); intros.
  apply emp_star in H0.
  apply sep_star_comm in H0.
  apply ptsto_valid in H0.
  contradiction H.
  eexists; eauto.
  auto.
Qed.

Lemma ptsto_valid_neq:
  forall a a' v m,
  a' <> a ->
  (a |-> v)%pred m ->
  m a' = None.
Proof.
  intros.
  apply H0; auto.
Qed.


Lemma ptsto_upd_disjoint: forall (F : @pred AT AEQ V) a v m,
  F m -> m a = None
  -> (F * a |-> v)%pred (upd m a v).
Proof.
  unfold_sep_star; intros; repeat deex.
  exists m.
  exists (upd empty_mem a v).
  intuition.
  - extensionality x.
    unfold mem_union; destruct (AEQ x a); simpl_upd; intuition.
    rewrite H0; auto.
    destruct (m x); auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    destruct (AEQ a0 a); subst; intuition; pred.
    rewrite upd_ne in H3 by auto.
    unfold empty_mem in *; congruence.
  - intuition; eauto.
    unfold ptsto; intuition.
    simpl_upd; auto.
Qed.


Lemma ptsto_upd:
  forall a v v0 F m,
  (a |-> v0 * F)%pred m ->
  (a |-> v * F)%pred (upd m a v).
Proof.
  unfold_sep_star; intros; repeat deex.
  exists (upd empty_mem a v).
  exists m2.
  intuition.
  - extensionality x.
    unfold mem_union; destruct (AEQ x a); simpl_upd; eauto.
    destruct H1; repeat deex.
    rewrite H1; auto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H.
    destruct H1; repeat deex.
    destruct (AEQ a0 a); subst.
    rewrite upd_eq in H2; inversion H2; subst.
    eauto.
    rewrite upd_ne in H2 by auto; unfold empty_mem in *; congruence.
  - intuition eauto.
    unfold ptsto; intuition.
    rewrite upd_ne; auto.
Qed.

Lemma ptsto_upd' : forall F a v v' m,
  (F * a |-> v)%pred m ->
  (F * a |-> v')%pred (upd m a v').
Proof.
  intros.
  apply sep_star_comm.
  apply sep_star_comm in H.
  eapply ptsto_upd; eauto.
Qed.

Lemma ptsto_upd_bwd:
  forall a b v w F m,
  a <> b ->
  (a |-> v * F)%pred (upd m b w) ->
  (a |-> v * any)%pred m.
Proof.
  unfold ptsto; unfold_sep_star; intros; repeat deex.
  exists (upd empty_mem a v).
  exists (fun a' => if AEQ a' b then m a' else m2 a').
  intuition.
  - extensionality x.
    unfold mem_union in *.
    pose proof (equal_f_dep H1 x);
    pose proof (equal_f_dep H1 a);
    pose proof (equal_f_dep H1 b); clear H1; simpl in *.
    destruct (AEQ x a); subst.
    + rewrite H3 in H2. destruct (AEQ a b); simpl_upd in *; congruence.
    + rewrite H5 in H2 by congruence.
      destruct (AEQ x b); simpl_upd in *; unfold empty_mem; congruence.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H0; clear H0.
    destruct (AEQ a0 a); destruct (AEQ a0 b);
    simpl_upd in *; unfold empty_mem in *; try congruence; eauto.
  - intuition eauto.
    simpl_upd; unfold empty_mem; auto.
  - unfold any; auto.
Qed.

Lemma any_sep_star_ptsto : forall a v m,
  m a = Some v -> (any * a |-> v)%pred m.
Proof.
  intros.
  unfold_sep_star; unfold ptsto.
  exists (mem_except m a).
  exists (upd empty_mem a v).
  split; [ | split ].

  extensionality x; auto.
  unfold mem_union, mem_except.
  destruct (AEQ x a); simpl_upd; auto.
  destruct (m x); auto.

  unfold mem_disjoint, mem_except.
  intuition; repeat deex.
  destruct (AEQ a0 a); simpl_upd in *; unfold empty_mem in *;
  congruence.

  unfold any, mem_except; intuition;
   now simpl_upd.
 Qed.

Lemma ptsto_eq : forall p1 p2 m a v1 v2,
  p1 m -> p2 m ->
  (exists F, p1 =p=> a |-> v1 * F) ->
  (exists F, p2 =p=> a |-> v2 * F) ->
  v1 = v2.
Proof.
  intros.
  repeat deex.
  apply H1 in H; clear H1.
  apply H2 in H0; clear H2.
  apply ptsto_valid in H.
  apply ptsto_valid in H0.
  repeat deex.
  congruence.
Qed.

Lemma ptsto_value_eq : forall a v1 v2,
  v1 = v2 -> (@pimpl AT AEQ V) (a |-> v1)%pred (a |-> v2)%pred.
Proof.
  intros; subst.
  apply pimpl_refl.
Qed.

Lemma pimpl_and_split:
  forall (a b c : @pred AT AEQ V),
  (a =p=> b)
  -> (a =p=> c)
  -> (a =p=> b /\ c).
Proof.
  firstorder.
Qed.

Lemma pimpl_and_lift: forall (a b: @pred AT AEQ V) (c:Prop),
  (a =p=> b)
  -> c
  -> (a =p=> b /\ [c]).
Proof.
  firstorder.
Qed.

Lemma pimpl_or_l: forall (a b c: @pred AT AEQ V),
  (a =p=> c)
  -> (b =p=> c)
  -> (a \/ b =p=> c).
Proof.
  firstorder.
Qed.

Lemma pimpl_or_r: forall (a b c: @pred AT AEQ V),
  ((a =p=> b) \/ (a =p=> c))
  -> (a =p=> b \/ c).
Proof.
  firstorder.
Qed.

Lemma pimpl_or_apply : forall (a b : @pred AT AEQ V) m,
  (a \/ b)%pred m ->
  a m \/ b m.
Proof.
  firstorder.
Qed.

Lemma pimpl_any :
  forall p,
  p =p=> any.
Proof.
  firstorder.
Qed.

Lemma pimpl_emp_any :
  forall p,
  p =p=> emp * any.
Proof.
  intros.
  eapply pimpl_trans; [|apply pimpl_star_emp]; apply pimpl_any.
Qed.

Lemma eq_pimpl : forall (a b : @pred AT AEQ V),
  a = b
  -> (a =p=> b).
Proof.
  intros; subst; firstorder.
Qed.

Theorem sep_star_indomain : forall p q a,
  (p =p=> indomain a) ->
  (p * q =p=> indomain a).
Proof.
  unfold_sep_star; unfold pimpl, indomain, mem_union.
  intros.
  repeat deex.
  edestruct H; eauto.
  rewrite H1.
  eauto.
Qed.

Theorem ptsto_indomain : forall (a : AT) v,
  a |-> v =p=> (@indomain AT AEQ V) a.
Proof.
  firstorder.
Qed.

Theorem sep_star_ptsto_some : forall a v F m,
  (a |-> v * F)%pred m -> m a = Some v.
Proof.
  unfold_sep_star; unfold ptsto, mem_union, exis.
  intros.
  repeat deex.
  rewrite H2.
  auto.
Qed.

Lemma sep_star_ptsto_some_eq : forall m F a v v',
  (a |-> v * F)%pred m -> m a = Some v' -> v = v'.
Proof.
  intros.
  apply sep_star_ptsto_some in H.
  rewrite H in H0.
  inversion H0; auto.
Qed.


Theorem sep_star_ptsto_indomain : forall a v F m,
  (a |-> v * F)%pred m -> indomain a m.
Proof.
  intros.
  eapply sep_star_ptsto_some in H.
  repeat deex; eexists; eauto.
Qed.

Theorem sep_star_or_distr : forall (a b c : @pred AT AEQ V),
  (a * (b \/ c))%pred <=p=> (a * b \/ a * c)%pred.
Proof.
  split.
  - unfold_sep_star; unfold pimpl, or.
    intros; repeat deex.
    + left. do 2 eexists. eauto.
    + right. do 2 eexists. eauto.
  - apply pimpl_or_l.
    + apply pimpl_sep_star; [apply pimpl_refl|].
      apply pimpl_or_r; left; apply pimpl_refl.
    + apply pimpl_sep_star; [apply pimpl_refl|].
      apply pimpl_or_r; right; apply pimpl_refl.
Qed.

Theorem lift_impl : forall (P : @pred AT AEQ V) (Q : Prop), (forall m, P m -> Q) -> P =p=> [[ Q ]] * P.
Proof.
  intros. unfold_sep_star.
  exists (fun _ => None). exists m.
  intuition; hnf; try tauto; firstorder discriminate.
Qed.

Lemma ptsto_conflict : forall a m,
  ~ (a |->? * a |->?)%pred m.
Proof.
  unfold_sep_star; firstorder discriminate.
Qed.

Lemma ptsto_conflict_F : forall a F m,
  ~ (a |->? * a |->? * F)%pred m.
Proof.
  unfold_sep_star; firstorder discriminate.
Qed.

Theorem ptsto_complete : forall a v m1 m2,
  (a |-> v)%pred m1 -> (a |-> v)%pred m2 -> m1 = m2.
Proof.
  unfold ptsto; intros; extensionality x.
  destruct H; destruct H0.
  destruct (AEQ a x); subst; try congruence.
  erewrite H1; eauto.
  erewrite H2; eauto.
Qed.



Theorem ptsto_diff_ne : forall a0 a1 (v0: V a0) (v1: V a1) F0 F1 m
  (Heq: V a0 = V a1),
  (a0 |-> v0 * F0)%pred m ->
  (a1 |-> v1 * F1)%pred m ->
  @eq_rect _ _ (fun T => T) v0 _ Heq  <> v1 ->
  a0 <> a1.
Proof.
  unfold not; intros.
  subst.
  apply sep_star_ptsto_some in H.
  apply sep_star_ptsto_some in H0.
  rewrite H in H0.
  inversion H0.
  subst.
  rewrite <- eq_rect_eq in H1.
  congruence.
Qed.

Theorem emp_complete : forall m1 m2,
  (@emp AT AEQ V) m1 -> emp m2 -> m1 = m2.
Proof.
  intros.
  extensionality a; unfold emp in *; congruence.
Qed.

Theorem sep_star_empty_mem : forall (a b : @pred AT AEQ V),
  (a * b)%pred empty_mem -> a empty_mem /\ b empty_mem.
Proof.
  unfold_sep_star.
  intros.
  destruct H. destruct H. destruct H. destruct H0. destruct H1.
  cut (x = empty_mem).
  cut (x0 = empty_mem).
  intros; subst; intuition.

  unfold mem_union, empty_mem in *.
  extensionality fa.
  apply equal_f_dep with (x1:=fa) in H.
  destruct (x0 fa); auto.
  destruct (x fa); auto.
  inversion H.

  unfold mem_union, empty_mem in *.
  extensionality fa.
  apply equal_f_dep with (x1:=fa) in H.
  destruct (x fa); auto.
Qed.

Theorem ptsto_empty_mem : forall a v,
  ~ (a |-> v)%pred (@empty_mem AT AEQ V).
Proof.
  unfold empty_mem, ptsto.
  intuition discriminate.
Qed.

Theorem emp_empty_mem :
  emp (@empty_mem AT AEQ V).
Proof.
  firstorder.
Qed.

Theorem emp_empty_mem_only : forall m,
  emp m -> m = empty_mem.
Proof.
  intros; extensionality x.
  firstorder.
Qed.

Lemma mem_union_empty_mem : forall m,
  mem_union empty_mem m = m.
Proof.
  unfold mem_union; intros; extensionality x.
  firstorder.
Qed.

Lemma mem_disjoint_empty_mem : forall m,
  mem_disjoint empty_mem m.
Proof.
  unfold mem_disjoint, empty_mem, not. intros; repeat deex. congruence.
Qed.

Lemma mem_disjoint_empty_mem_r : forall m,
  mem_disjoint m empty_mem.
Proof.
  intros.
  apply mem_disjoint_comm.
  apply mem_disjoint_empty_mem.
Qed.

Lemma mem_union_empty_mem_r : forall m,
  mem_union m empty_mem = m.
Proof.
  intros.
  rewrite mem_union_comm.
  apply mem_union_empty_mem.
  apply mem_disjoint_empty_mem_r.
Qed.

Theorem notindomain_empty_mem : forall a,
  notindomain a (@empty_mem AT AEQ V).
Proof.
  firstorder.
Qed.

Theorem emp_notindomain : forall a m,
  emp m -> notindomain a m.
Proof.
  intros; unfold notindomain.
  pose proof (H a); auto.
Qed.

Theorem emp_pimpl_notindomain : forall a,
  emp =p=> (@notindomain AT AEQ V) a.
Proof.
  unfold pimpl; intros.
  apply emp_notindomain; auto.
Qed.

Theorem emp_mem_except : forall m a,
  emp m -> emp (mem_except m a).
Proof.
  unfold emp, mem_except; intros.
  destruct (AEQ a0 a); auto.
Qed.

Theorem mem_except_double : forall m a,
  mem_except (mem_except m a) a = mem_except m a.
Proof.
  unfold mem_except; intros.
  extensionality x.
  destruct (AEQ x a); auto.
Qed.

Theorem mem_except_upd : forall m a v,
  mem_except (upd m a v) a = mem_except m a.
Proof.
  unfold mem_except, upd; intros.
  extensionality a'.
  destruct (AEQ a' a); auto.
Qed.

Lemma mem_except_union_comm: forall m1 m2 a1 a2 v1,
  a1 <> a2
  -> (a1 |-> v1)%pred m1
  -> mem_except (mem_union m1 m2) a2 = mem_union m1 (mem_except m2 a2).
Proof.
  unfold mem_union, mem_except, ptsto.
  intuition.
  extensionality x.
  destruct (AEQ x a2) eqn:Heq; auto.
  destruct (m1 x) eqn:Hx; auto; subst.
  pose proof (H2 a2 H) as Hy.
  rewrite Hx in Hy.
  inversion Hy.
Qed.

Lemma mem_disjoint_mem_except : forall m1 m2 a,
  mem_disjoint m1 m2
  -> mem_disjoint m1 (mem_except m2 a).
Proof.
  unfold mem_disjoint, mem_except; intuition.
  repeat deex.
  destruct (AEQ a0 a).
  inversion H2.
  apply H.
  firstorder.
Qed.

Theorem notindomain_mem_union : forall a m1 m2,
  notindomain a (mem_union m1 m2)
  <-> notindomain a m1 /\ notindomain a m2.
Proof.
  unfold notindomain, mem_union; split; intros; intuition.
  destruct (m1 a); auto.
  destruct (m1 a); auto.
  inversion H.
  rewrite H0; auto.
Qed.

Theorem notindomain_indomain_conflict : forall a m,
  notindomain a m -> indomain a m -> False.
Proof.
  unfold notindomain, indomain.
  firstorder.
  rewrite H in H0.
  inversion H0.
Qed.

Theorem notindomain_mem_except : forall a a' m,
  a <> a'
  -> notindomain a (mem_except m a')
  -> notindomain a m.
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.

Theorem notindomain_mem_except' : forall a a' m,
  notindomain a m
  -> notindomain a (mem_except m a').
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.

Theorem notindomain_mem_eq : forall a m,
  notindomain a m -> m = mem_except m a.
Proof.
  unfold notindomain, mem_except; intros.
  extensionality x.
  destruct (AEQ x a); subst; auto.
Qed.

Theorem mem_except_notindomain : forall a m,
  notindomain a (mem_except m a).
Proof.
  unfold notindomain, mem_except; intros.
  destruct (AEQ a a); congruence.
Qed.

Theorem indomain_mem_except : forall a a' v m,
  a <> a'
  -> (mem_except m a') a = Some v
  -> m a = Some v.
Proof.
  unfold mem_except; intros.
  destruct (AEQ a a'); firstorder.
Qed.

Theorem notindomain_not_indomain : forall a m,
  notindomain a m <-> ~ indomain a m.
Proof.
  unfold notindomain, indomain; split; intros; destruct (m a);
    try congruence.
  destruct 1; discriminate.
  exfalso; eauto.
Qed.

Lemma indomain_upd_ne : forall m a a' v,
  indomain a (upd m a' v)
  -> a <> a' -> indomain a m.
Proof.
  unfold indomain; intros.
  destruct H.
  rewrite upd_ne in H; auto.
  eexists; eauto.
Qed.

Theorem indomain_dec : forall a m,
  {indomain a m} + {notindomain a m}.
Proof.
  unfold notindomain, indomain.
  intros; destruct (m a) eqn:Heq.
  left; exists v; auto.
  right; auto.
Defined.


Theorem ptsto_mem_except : forall F a v m,
  (a |-> v * F)%pred m -> F (mem_except m a).
Proof.
  unfold ptsto; unfold_sep_star.
  intuition; repeat deex.
  replace ((mem_except (mem_union m1 m2) a)) with m2; auto.

  unfold mem_except.
  extensionality x.
  destruct (AEQ x a); subst.
  eapply mem_disjoint_either; eauto.

  unfold mem_union.
  pose proof (H4 x); intuition.
  rewrite H1; simpl; auto.
Qed.


Theorem mem_except_ptsto : forall (F : @pred AT AEQ V) a v m,
  m a = Some v
  -> F (mem_except m a)
  -> (a |-> v * F)%pred m.
Proof.
  unfold indomain, ptsto; unfold_sep_star; intros.
  exists (upd empty_mem a v).
  exists (mem_except m a).
  split; [ | split].

  extensionality x.
  unfold mem_union, mem_except.
  destruct (AEQ x a); now simpl_upd.

  unfold mem_disjoint, mem_except; intuition; repeat deex.
  destruct (AEQ a0 a); now simpl_upd in *.

  intuition.
  simpl_upd; unfold empty_mem; auto.
Qed.

Theorem indomain_mem_except_indomain : forall m a a',
  indomain a (mem_except m a') -> indomain a m.
Proof.
  unfold indomain; intros.
  destruct H; exists x.
  destruct (AEQ a a'); subst.
  unfold mem_except in H.
  destruct (AEQ a' a'); congruence.
  eapply indomain_mem_except; eauto.
Qed.


Theorem ptsto_mem_except_F : forall (F F' : @pred AT AEQ V) a a' v m,
  (a |-> v * F)%pred m
  -> a <> a'
  -> (forall m', F m' -> F' (mem_except m' a'))
  -> (a |-> v * F')%pred (mem_except m a').
Proof.
  unfold_sep_star.
  intros; repeat deex.
  eexists; exists (mem_except m2 a'); intuition eauto.
  eapply mem_except_union_comm; eauto.
  apply mem_disjoint_mem_except; auto.
Qed.

Theorem ptsto_mem_except_exF : forall (F : @pred AT AEQ V) a a' v m,
  (a |-> v * F)%pred m
  -> a <> a'
  -> (a |-> v * (exists F', F'))%pred (mem_except m a').
Proof.
  unfold_sep_star.
  intros; repeat deex.
  eexists; exists (mem_except m2 a'); intuition eauto.
  eapply mem_except_union_comm; eauto.
  apply mem_disjoint_mem_except; auto.
  exists (diskIs (mem_except m2 a')). firstorder.
Qed.

Theorem exact_domain_disjoint_union : forall p m1 m2 m1' m2',
  exact_domain p ->
  mem_union m1 m2 = mem_union m1' m2' ->
  mem_disjoint m1 m2 ->
  mem_disjoint m1' m2' ->
  p m1 ->
  p m1' ->
  m1 = m1' /\ m2 = m2'.
Proof.
  unfold exact_domain; split; extensionality x;
    specialize (H m1 m1' H3 H4 x);
    unfold mem_union in H0;
    apply equal_f_dep with (x) in H0.
  - destruct (m1 x); destruct (m1' x); firstorder.
  - unfold mem_disjoint in *.
    firstorder.
    specialize (H1 x).
    specialize (H2 x).
    destruct (m1 x); destruct (m1' x); destruct (m2 x); destruct (m2' x); firstorder;
      exfalso; eauto.
Qed.

Theorem septract_sep_star :
  forall (p q : @pred AT AEQ V),
  exact_domain p ->
  (p --* (p * q) =p=> q)%pred.
Proof.
  unfold septract; unfold_sep_star; unfold pimpl; intros; repeat deex.
  rewrite mem_union_comm in H3 by eauto.
  apply mem_disjoint_comm in H1.
  edestruct exact_domain_disjoint_union; try eassumption.
  congruence.
Qed.

Theorem septract_pimpl_l :
  forall (p p' q : @pred AT AEQ V),
  (p =p=> p') ->
  (p --* q =p=> p' --* q).
Proof.
  unfold septract; unfold pimpl; intros; repeat deex.
  eauto.
Qed.

Theorem septract_pimpl_r :
  forall (p q q' : @pred AT AEQ V),
  (q =p=> q') ->
  (p --* q =p=> p --* q').
Proof.
  unfold septract; unfold pimpl; intros; repeat deex.
  eauto.
Qed.

Theorem strictly_exact_to_exact_domain : forall p,
  strictly_exact p -> exact_domain p.
Proof.
  unfold strictly_exact, exact_domain; intros.
  specialize (H m1 m2 H0 H1).
  subst; intuition.
Qed.

Theorem strictly_exact_to_precise : forall p,
  strictly_exact p -> precise p.
Proof.
  unfold strictly_exact, precise; eauto.
Qed.

Theorem ptsto_strictly_exact : forall a v,
  @strictly_exact AT AEQ V (a |-> v)%pred.
Proof.
  unfold ptsto, strictly_exact; intros.
  extensionality x; intuition.
  destruct (AEQ a x); subst; try congruence.
  rewrite H2 by eauto.
  rewrite H3 by eauto.
  eauto.
Qed.

Theorem emp_strictly_exact : strictly_exact (@emp AT AEQ V).
Proof.
  unfold emp, strictly_exact; intros.
  extensionality x; congruence.
Qed.

Theorem sep_star_exact_domain : forall p q,
  exact_domain p -> exact_domain q ->
  exact_domain (p * q)%pred.
Proof.
  unfold exact_domain; unfold_sep_star; unfold mem_union; intros.
  repeat deex;
    specialize (H _ _ H5 H6 a);
    specialize (H0 _ _ H7 H9 a);
    destruct (m0 a); destruct (m2 a); intuition; congruence.
Qed.

Theorem sep_star_strictly_exact : forall p q,
  strictly_exact p -> strictly_exact q ->
  strictly_exact (p * q)%pred.
Proof.
  unfold strictly_exact; unfold_sep_star; unfold mem_union; intros.
  repeat deex.
  specialize (H _ _ H4 H5).
  specialize (H0 _ _ H6 H8).
  subst.
  eauto.
Qed.

Hint Resolve mem_disjoint_assoc_1.
Hint Resolve mem_disjoint_assoc_2.
Hint Resolve mem_union_assoc.
Hint Resolve mem_disjoint_union.
Hint Resolve mem_disjoint_union_2.

Theorem sep_star_precise : forall p q,
  precise p -> precise q ->
  precise (p * q)%pred.
Proof.
  unfold precise; unfold_sep_star; intros; repeat deex.
  specialize (H m0 (mem_union m3 m2') m2 (mem_union m4 m1')).
  specialize (H0 m3 (mem_union m0 m2') m4 (mem_union m2 m1')).
  rewrite H; clear H; eauto.
  rewrite H0; clear H0; eauto.
  - rewrite <- mem_union_assoc; try apply mem_disjoint_comm; auto.
    rewrite <- mem_union_assoc; try apply mem_disjoint_comm; auto.
    rewrite <- (mem_union_comm H5).
    rewrite <- (mem_union_comm H4).
    auto.
    rewrite <- (mem_union_comm H4). apply mem_disjoint_comm. eauto.
    rewrite <- (mem_union_comm H5). apply mem_disjoint_comm. eauto.
  - rewrite (mem_union_comm H5) in H3.
    apply mem_disjoint_assoc_1; auto; try apply mem_disjoint_comm; auto.
  - rewrite (mem_union_comm H4) in H2.
    apply mem_disjoint_assoc_1; auto; try apply mem_disjoint_comm; auto.
  - repeat rewrite <- mem_union_assoc; auto.
Qed.

Theorem ptsto_any_precise : forall a,
  @precise AT AEQ V (a |->?)%pred.
Proof.
  unfold ptsto, precise; intros.
  destruct H2.
  destruct H3.
  apply equal_f_dep with (x1 := a) in H.
  unfold mem_union in H.
  intuition.
  rewrite H4 in H; rewrite H2 in H.
  inversion H.
  extensionality x1; intuition.
  destruct (AEQ a x1); subst; try congruence.
  rewrite H5 by eauto.
  rewrite H6 by eauto.
  eauto.
Qed.

Theorem forall_strictly_exact : forall A (a : A) (p : A -> @pred AT AEQ V),
  (forall x, strictly_exact (p x)) ->
  strictly_exact (foral x, p x).
Proof.
  unfold foral_, strictly_exact; intros.
  specialize (H a).
  eauto.
Qed.

End GenPredThm.

(* this tactic could use much more generalization *)
Ltac solve_disjoint_union :=
  match goal with
  | [ |- mem_disjoint _ _ ] =>
    now ( eauto ||rewrite mem_disjoint_comm; eauto)
  | [ H: mem_union ?m1a ?m1b = mem_union ?m2a ?m2b |-
      mem_union ?m1b ?m1a = mem_union ?m2b ?m2a ] =>
    now (apply disjoint_union_comm_eq; eauto)
  | [ H: mem_union ?m1a ?m1b = mem_union ?m2a ?m2b |-
      mem_union ?m2b ?m2a = mem_union ?m1b ?m1a ] =>
    now (apply disjoint_union_comm_eq; eauto)
  end.


Hint Resolve sep_star_precise : precision.
Hint Resolve strictly_exact_to_precise : precision.
Hint Resolve ptsto_any_precise : precision.
Hint Resolve emp_strictly_exact : precision.
Hint Resolve ptsto_strictly_exact : precision.

Instance piff_equiv {AT AEQ V} :
  Equivalence (@piff AT AEQ V).
Proof.
  split.
  exact (@piff_refl AT AEQ V).
  exact (@piff_comm AT AEQ V).
  exact (@piff_trans AT AEQ V).
Qed.

Instance pimpl_preorder {AT AEQ V} :
  PreOrder (@pimpl AT AEQ V).
Proof.
  split.
  exact (@pimpl_refl AT AEQ V).
  exact (@pimpl_trans AT AEQ V).
Qed.

Instance piff_pimpl_subrelation {AT AEQ V} :
  subrelation (@piff AT AEQ V) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance piff_flip_pimpl_subrelation {AT AEQ V} :
  subrelation (@piff AT AEQ V) (Basics.flip (@pimpl AT AEQ V)).
Proof.
  firstorder.
Qed.

Instance pimpl_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance pimpl_pimpl_proper1 {AT AEQ V} :
  Proper (pimpl ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance pimpl_pimpl_proper2 {AT AEQ V} :
  Proper (Basics.flip pimpl ==> pimpl ==> Basics.impl) (@pimpl AT AEQ V).
Proof.
  firstorder.
Qed.

Instance sep_star_apply_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.

Instance sep_star_apply_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> eq ==> Basics.flip Basics.impl) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star; assumption.
Qed.


Instance sep_star_apply_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> Basics.impl) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm H.
  subst.
  eapply pimpl_apply; [| eassumption ].
  apply pimpl_sep_star. 
  apply Hp.
  apply Hq.
Qed.

Instance sep_star_apply_piff_proper' {AT AEQ V} :
  Proper (piff ==> piff ==> eq ==> iff) (@sep_star AT AEQ V).
Proof.
  intros p p' Hp q q' Hq m m' Hm.
  subst; split; intros.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
  - eapply pimpl_apply; [| eassumption ]. apply pimpl_sep_star. apply Hp. apply Hq.
Qed.

Instance sep_star_apply_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
  congruence.
Qed.


Instance sep_star_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@sep_star AT AEQ V).
Proof.
  congruence.
Qed.

Instance sep_star_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@sep_star AT AEQ V).
Proof.
  intros a b H c d H'.
  split; ( apply pimpl_sep_star; [ apply H | apply H' ] ).
Qed.

Instance sep_star_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@sep_star AT AEQ V).
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.

Instance sep_star_pimpl_proper' {AT AEQ V} :
  Proper (Basics.flip pimpl ==> Basics.flip pimpl ==> Basics.flip pimpl) (@sep_star AT AEQ V).
Proof.
  intros a b H c d H'.
  apply pimpl_sep_star; assumption.
Qed.

Instance and_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@and AT AEQ V).
Proof.
  congruence.
Qed.

Instance and_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@and AT AEQ V).
Proof.
  firstorder.
Qed.

Instance and_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@and AT AEQ V).
Proof.
  firstorder.
Qed.

Instance or_eq_proper {AT AEQ V} :
  Proper (eq ==> eq ==> eq) (@or AT AEQ V).
Proof.
  congruence.
Qed.

Instance or_piff_proper {AT AEQ V} :
  Proper (piff ==> piff ==> piff) (@or AT AEQ V).
Proof.
  firstorder.
Qed.

Instance or_pimpl_proper {AT AEQ V} :
  Proper (pimpl ==> pimpl ==> pimpl) (@or AT AEQ V).
Proof.
  firstorder.
Qed.

Example pimpl_rewrite : forall AT AEQ V a b (p q : @pred AT AEQ V) x y, p =p=> q
  -> (x /\ a * p * b \/ y =p=> x /\ a * q * b \/ y).
Proof.
  intros.
  rewrite H.
  reflexivity.
Qed.

Instance exists_proper_eq {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A eq ==> eq) (@exis AT AEQ V A).
Proof.
  intros pf qf Heq.
  assert (pf = qf) by (apply functional_extensionality_dep; congruence); subst.
  reflexivity.
Qed.

Instance exists_proper_piff {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> piff) (@exis AT AEQ V A).
Proof.
  firstorder.
Qed.

Instance exists_proper_pimpl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A pimpl ==> pimpl) (@exis AT AEQ V A).
Proof.
  firstorder.
Qed.

Example pimpl_exists_rewrite : forall AT AEQ V (p q : @pred AT AEQ V), p =p=> q
  -> (exists x, p * x) =p=> (exists x, q * x).
Proof.
  intros.
  setoid_rewrite H.
  reflexivity.
Qed.

(**
 * The following variation is needed for situations where a [pred] containing
 * an [exis] is applied to a [mem], and [setoid_rewrite] tries to rewrite the
 * term that appears under [exis].
 *)
Instance exists_proper_pimpl_impl {AT AEQ V} {A : Type} :
  Proper (pointwise_relation A piff ==> eq ==> iff) (@exis AT AEQ V A).
Proof.
  intros a b Hab m1 m2 Hm.
  split; unfold Basics.impl, exis; intros; deex; eexists.
  eapply Hab; eauto.
  eapply Hab; eauto.
Qed.

(**
 * The following instance is needed to make [setoid_rewrite] fast on terms
 * that involve [lift_empty].  Otherwise, typeclass search takes forever.
 *)
Instance lift_empty_proper_iff {AT AEQ V} :
  Proper (iff ==> @piff _ _ _) (@lift_empty AT AEQ V).
Proof.
  firstorder.
Qed.

(**
 * The following instances are needed to rewrite under [lift_empty].
 *)
Instance lift_empty_proper_impl {AT AEQ V} :
  Proper (Basics.impl ==> @pimpl _ _ _) (@lift_empty AT AEQ V).
Proof.
  firstorder.
Qed.

Instance lift_empty_proper_eq {AT AEQ V} :
  Proper (eq ==> eq) (@lift_empty AT AEQ V).
Proof.
  congruence.
Qed.

Instance lift_empty_proper_expanded_impl {AT AEQ V} :
  Proper (Basics.impl ==> eq ==> Basics.impl) (@lift_empty AT AEQ V).
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.

Instance lift_empty_proper_expanded_flipimpl {AT AEQ V} :
  Proper (Basics.flip Basics.impl ==> eq ==> Basics.flip Basics.impl) (@lift_empty AT AEQ V).
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm H; subst.
  intuition.
Qed.

Instance lift_empty_proper_expanded_iff {AT AEQ V} :
  Proper (iff ==> eq ==> iff) (@lift_empty AT AEQ V).
Proof.
  unfold lift_empty.
  intros a b Hab m1 m2 Hm; subst.
  intuition.
Qed.


(**
 * This instance in effect tells [setoid_rewrite] about functional extensionality.
 *)
Instance funext_subrelation {A f R} {subf : subrelation R eq}:
  subrelation (@pointwise_relation A f R) eq.
Proof.
  unfold pointwise_relation.
  intros a b Hab.
  apply functional_extensionality_dep; auto.
Qed.

(**
 * This helps rewrite using [eq] under deep predicates, [prog]s, etc.
 * See https://coq.inria.fr/bugs/show_bug.cgi?id=3795
 *)
Global Program Instance eq_equivalence {A} : Equivalence (@eq A) | 0.


Instance pred_apply_pimpl_proper {AT AEQ V} :
  Proper (eq ==> pimpl ==> Basics.impl) (@pred_apply AT AEQ V).
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.

Instance pred_apply_pimpl_flip_proper {AT AEQ V} :
  Proper (eq ==> Basics.flip pimpl ==> Basics.flip Basics.impl) (@pred_apply AT AEQ V).
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq H.
  subst.
  auto.
Qed.

Instance pred_apply_piff_proper {AT AEQ V} :
  Proper (eq ==> piff ==> iff) (@pred_apply AT AEQ V).
Proof.
  unfold pred_apply.
  intros ma mb Hmab p q Hpq.
  subst. destruct Hpq.
  intuition.
Qed.


Example pred_apply_rewrite : forall AT AEQ V (p q : @pred AT AEQ V) m,
  m ## p*q -> m ## q*p.
Proof.
  intros.
  rewrite sep_star_comm1 in H.
  auto.
Qed.


Theorem diskIs_extract : forall AT AEQ V a v (m:@mem AT AEQ V),
  (exists F, F * a |-> v)%pred m
  -> (diskIs m =p=> diskIs (mem_except m a) * a |-> v).
Proof.
  intros.
  destruct H.
  apply sep_star_comm in H. apply ptsto_valid in H.
  unfold pimpl, diskIs, ptsto; unfold_sep_star; intros; subst.
  exists (fun a' => if AEQ a' a then None else m0 a').
  exists (upd empty_mem a v).
  intuition.
  - unfold mem_union; extensionality x0.
    destruct (AEQ x0 a); subst; simpl_upd; auto.
    destruct (m0 x0); auto.
  - unfold mem_disjoint; unfold not; intros. repeat deex.
    destruct (AEQ a0 a); try congruence.
    rewrite upd_ne in H2 by auto.
    unfold empty_mem in H2.
    congruence.
  - now simpl_upd.
  - now simpl_upd.
Qed.

Theorem diskIs_combine_upd : forall AT AEQ V a v (m:@mem AT AEQ V),
  diskIs (mem_except m a) * a |-> v =p=> diskIs (upd m a v).
Proof.
  unfold pimpl, diskIs, ptsto, upd; unfold_sep_star; intros; subst; repeat deex.
  extensionality x.
  case_eq (AEQ x a); intros; subst.
  - rewrite mem_union_comm; auto.
    erewrite mem_union_addr; eauto.
    unfold eq_rect_r.
    erewrite <- eq_rect_eq_dec; eauto.
    apply mem_disjoint_comm; auto.
  - unfold mem_union, mem_except.
    destruct (AEQ x a); try discriminate.
    case_eq (m x); intros; auto.
    rewrite H4; auto.
Qed.

Theorem diskIs_combine_same : forall AT AEQ V a v (m:@mem AT AEQ V),
  (exists F, F * a |-> v)%pred m
  -> diskIs (mem_except m a) * a |-> v =p=> diskIs m.
Proof.
  intros.
  destruct H.
  apply sep_star_comm in H. apply ptsto_valid in H.
  unfold pimpl, diskIs, ptsto, upd; unfold_sep_star; intros; subst; repeat deex.
  extensionality x0.
  unfold mem_union, mem_except.
  destruct (AEQ x0 a); subst; try congruence.
  destruct (m x0); auto.
  rewrite H5; auto; discriminate.
Qed.

Lemma diskIs_combine_same':
forall AT AEQ V a v (m: @mem AT AEQ V),
  m a = Some v ->
  diskIs m =p=> diskIs (mem_except m a) * a |-> v.
Proof.
  unfold_sep_star; unfold pimpl, diskIs.
  intros; subst.
  exists (mem_except m0 a).
  exists (upd empty_mem a v).
  unfold mem_except, ptsto, mem_disjoint, mem_union, empty_mem in *.
  intuition eauto; destruct matches; simpl_upd; auto.
  extensionality a'; destruct matches; now simpl_upd.
  repeat deex; destruct matches in *; now simpl_upd in *.
Qed.

Lemma diskIs_combine_same'_applied
  : forall AT AEQ V a v (m d : @mem AT AEQ V),
    m a = Some v ->
    diskIs m d ->
    (diskIs (mem_except m a) * a |-> v)%pred d.
Proof.
  intros.
  apply diskIs_combine_same'; auto.
Qed.

Lemma diskIs_same : forall AT AEQ V (d: @mem AT AEQ V),
    diskIs d d.
Proof.
  unfold diskIs; auto.
Qed.

Lemma diskIs_split_upd : forall AT AEQ V a v (m: @mem AT AEQ V),
  diskIs (upd m a v) =p=>
  diskIs (mem_except m a) * a |-> v.
Proof.
  unfold diskIs, pimpl, mem_except, mem_union, mem_disjoint.
  unfold_sep_star.
  intros.
  eexists.
  exists (upd empty_mem a v).
  intuition eauto.
  unfold mem_union; subst.
  extensionality a'.
  destruct matches; simpl_upd; auto.

  unfold mem_disjoint, empty_mem; intro; repeat deex.
  destruct matches in *; simpl_upd in *; congruence.
  unfold ptsto; destruct matches; intuition simpl_upd; auto.
Qed.

Section MemDomains.

Variable (AT:Type).
Variable (AEQ: DecEq AT).
Variable (V:AT -> Type).

Implicit Types (m: @mem AT AEQ V).

(* m <= m' *)
Definition subset m m' :=
  forall a v, m a = Some v -> exists v', m' a = Some v'.

Definition same_domain m m' :=
  subset m m' /\
  subset m' m.

Theorem same_domain_refl : forall m,
  same_domain m m.
Proof.
  firstorder.
Qed.

Theorem same_domain_sym : forall m m',
  same_domain m m' ->
  same_domain m' m.
Proof.
  firstorder.
Qed.

Theorem same_domain_trans : forall m m' m'',
  same_domain m m' ->
  same_domain m' m'' ->
  same_domain m m''.
Proof.
  unfold same_domain, subset.
  intuition eauto;
  match goal with
  | [ H: context[forall _, ?m _ = Some _ -> _], H': ?m _ = Some _ |- _] =>
    apply H in H'
  end; deex; eauto.
Qed.

Theorem same_domain_upd : forall m a v v0,
  m a = Some v0 ->
  same_domain m (upd m a v).
Proof.
  unfold same_domain, subset, upd.
  unfold eq_rect_r.
  firstorder.
  destruct matches; subst; eauto;
    rewrite <- eq_rect_eq in *; eauto.
  destruct matches in *; eauto.
Qed.

Lemma subset_inverse : forall m m' a,
    m a = None ->
    subset m' m ->
    m' a = None.
Proof.
  unfold subset.
  intros.
  case_eq (m' a); intros; eauto.
  specialize (H0 _ _ H1).
  deex; congruence.
Qed.

Lemma same_domain_none : forall m m' a,
    m a = None ->
    same_domain m m' ->
    m' a = None.
Proof.
  unfold same_domain.
  intuition.
  eapply subset_inverse; eassumption.
Qed.

Lemma same_domain_remove_upd : forall m m' a v v',
    m a = Some v ->
    same_domain (upd m a v') m' ->
    same_domain m m'.
Proof.
  unfold same_domain, subset.
  intuition; case_eq (AEQ a a0); intros; subst.
  eapply H1; autorewrite with upd; eauto.
  eapply H1; autorewrite with upd; eauto.

  edestruct H2; eauto; autorewrite with upd in *; eauto.
  edestruct H2; eauto; autorewrite with upd in *; eauto.
Qed.

End MemDomains.

Instance same_domain_equiv AT AEQ V : Equivalence (@same_domain AT AEQ V).
Proof.
  constructor; hnf; intros;
    eauto using same_domain_refl,
    same_domain_sym,
    same_domain_trans.
Qed.

Global Opaque pred.
