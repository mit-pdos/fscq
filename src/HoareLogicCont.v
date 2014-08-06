Require Import Arith Omega List.
Require Import FunctionalExtensionality.
Require Import Tactics.

Set Implicit Arguments.


(** * The programming language *)

Definition addr := nat.
Definition valu := nat.

Parameter donetoken : Set.

Inductive prog :=
| Fail
| Done (t: donetoken)
| Read (a: addr) (rx: valu -> prog)
| Write (a: addr) (v: valu) (rx: prog).

Definition progseq1 (A B:Type) (a:B->A) (b:B) := a b.
Definition progseq2 (A B:Type) (a:B->A) (b:B) := a b.

Notation "p1 ;; p2" := (progseq1 p1 p2) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (progseq2 p1 (fun x => p2)) (at level 60, right associativity).

Notation "!" := Read.
Infix "<--" := Write (at level 8).


Definition mem := addr -> option valu.
Definition mem0 : mem := fun _ => Some 0.
Definition upd (m : mem) (a : addr) (v : valu) : mem :=
  fun a' => if eq_nat_dec a' a then Some v else m a'.

Inductive outcome :=
| Failed
| Finished
| Crashed.

Inductive exec : mem -> prog -> mem -> outcome -> Prop :=
| XFail : forall m, exec m Fail m Failed
| XDone : forall m t, exec m (Done t) m Finished
| XReadFail : forall m a rx,
  m a = None ->
  exec m (Read a rx) m Failed
| XWriteFail : forall m a v rx,
  m a = None ->
  exec m (Write a v rx) m Failed
| XReadOK : forall m a v rx m' out,
  m a = Some v ->
  exec m (rx v) m' out ->
  exec m (Read a rx) m' out
| XWriteOK : forall m a v v0 rx m' out,
  m a = Some v0 ->
  exec (upd m a v) rx m' out ->
  exec m (Write a v rx) m' out
| XCrash : forall m p, exec m p m Crashed.

Inductive exec_recover : mem -> prog -> prog -> mem -> outcome -> Prop :=
| XRFail : forall m p1 p2 m',
  exec m p1 m' Failed -> exec_recover m p1 p2 m' Failed
| XRFinished : forall m p1 p2 m',
  exec m p1 m' Finished -> exec_recover m p1 p2 m' Finished
| XRCrashed : forall m p1 p2 m' m'' out,
  exec m p1 m' Crashed ->
  exec_recover m' p2 p2 m'' out -> exec_recover m p1 p2 m'' out.

Hint Constructors exec.
Hint Constructors exec_recover.

(** * The program logic *)

(** ** Predicates *)

Definition pred := mem -> Prop.

Definition ptsto (a : addr) (v : valu) : pred :=
  fun m => m a = Some v /\ forall a', a <> a' -> m a' = None.
Infix "|->" := ptsto (at level 35) : pred_scope.
Bind Scope pred_scope with pred.
Delimit Scope pred_scope with pred.

Definition impl (p q : pred) : pred :=
  fun m => p m -> q m.
Infix "-->" := impl (right associativity, at level 95) : pred_scope.

Definition and (p q : pred) : pred :=
  fun m => p m /\ q m.
Infix "/\" := and : pred_scope.

Definition or (p q : pred) : pred :=
  fun m => p m \/ q m.
Infix "\/" := or : pred_scope.

Definition foral_ A (p : A -> pred) : pred :=
  fun m => forall x, p x m.
Notation "'foral' x .. y , p" := (foral_ (fun x => .. (foral_ (fun y => p)) ..)) (at level 200, x binder, right associativity) : pred_scope.

Definition exis A (p : A -> pred) : pred :=
  fun m => exists x, p x m.
Notation "'exists' x .. y , p" := (exis (fun x => .. (exis (fun y => p)) ..)) : pred_scope.

Definition uniqpred A (p : A -> pred) (x : A) :=
  fun m => p x m /\ (forall (x' : A), p x' m -> x = x').
Notation "'exists' ! x .. y , p" := (exis (uniqpred (fun x => .. (exis (uniqpred (fun y => p))) ..))) : pred_scope.

Definition emp : pred :=
  fun m => forall a, m a = None.

Definition lift (P : Prop) : pred :=
  fun m => P.
Notation "[ P ]" := (lift P) : pred_scope.
(*
Notation "[[ P ]]" := (lift_empty P) : pred_scope.
 /\ forall a, m a = None
*)

Definition pimpl (p q : pred) := forall m, p m -> q m.
Notation "p ==> q" := (pimpl p%pred q%pred) (right associativity, at level 90).

Definition piff (p q : pred) : Prop := (p ==> q) /\ (q ==> p).
Notation "p <==> q" := (piff p%pred q%pred) (at level 90).

Definition pupd (p : pred) (a : addr) (v : valu) : pred :=
  fun m => exists m', p m' /\ m = upd m' a v.
Notation "p [ a <--- v ]" := (pupd p a v) (at level 0) : pred_scope.

Definition diskIs (m : mem) : pred := eq m.

Definition mem_disjoint (m1 m2:mem) :=
  ~ exists a v1 v2, m1 a = Some v1 /\ m2 a = Some v2.

Definition mem_union (m1 m2:mem) := fun a =>
  match m1 a with
  | Some v => Some v
  | None => m2 a
  end.

Definition sep_star (p1: pred) (p2: pred) :=
  fun m => exists m1 m2, m = mem_union m1 m2 /\ mem_disjoint m1 m2 /\ p1 m1 /\ p2 m2.
Infix "*" := sep_star : pred_scope.


Ltac deex := match goal with
               | [ H : ex _ |- _ ] => destruct H; intuition subst
             end.

Ltac pred_unfold := unfold impl, and, or, foral_, exis, uniqpred, lift,
                           pupd, diskIs, addr, valu in *.
Ltac pred := pred_unfold;
  repeat (repeat deex; simpl in *;
    intuition (try (congruence || omega);
      try autorewrite with core in *; eauto); try subst).

Theorem pimpl_refl : forall p, p ==> p.
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
  case_eq (m2 x); intros.
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
  case_eq (m2 x); intros.
  - apply H. eauto.
  - case_eq (m1 x); intros.
    + apply H0. repeat eexists; eauto. rewrite H1. eauto.
    + rewrite H4 in H2. firstorder.
Qed.

Theorem mem_disjoint_union:
  forall m1 m2 m3,
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_disjoint m2 m3.
Proof.
  unfold mem_disjoint, mem_union; intuition; repeat deex.
  apply H; exists x; destruct (m1 x); eauto.
Qed.

Theorem mem_disjoint_upd:
  forall m1 m2 a v v0,
  m1 a = Some v0 ->
  mem_disjoint m1 m2 ->
  mem_disjoint (upd m1 a v) m2.
Proof.
  unfold mem_disjoint, upd, not; intros; repeat deex;
    destruct (eq_nat_dec x a); subst; eauto 10.
Qed.

Theorem mem_union_comm:
  forall m1 m2,
  mem_disjoint m1 m2 ->
  mem_union m1 m2 = mem_union m2 m1.
Proof.
  unfold mem_disjoint, mem_union; intros; apply functional_extensionality; intros.
  case_eq (m1 x); case_eq (m2 x); intros; eauto; destruct H; eauto.
Qed.

Theorem mem_union_addr:
  forall m1 m2 a v,
  mem_disjoint m1 m2 ->
  m1 a = Some v ->
  mem_union m1 m2 a = Some v.
Proof.
  unfold mem_disjoint, mem_union; intros; rewrite H0; auto.
Qed.

Theorem mem_union_upd:
  forall m1 m2 a v v0,
  m1 a = Some v0 ->
  mem_union (upd m1 a v) m2 = upd (mem_union m1 m2) a v.
Proof.
  unfold mem_union, upd; intros; apply functional_extensionality; intros.
  destruct (eq_nat_dec x a); eauto.
Qed.

Theorem mem_union_assoc:
  forall m1 m2 m3,
  mem_disjoint m1 m2 ->
  mem_disjoint (mem_union m1 m2) m3 ->
  mem_union (mem_union m1 m2) m3 = mem_union m1 (mem_union m2 m3).
Proof.
  unfold mem_union, mem_disjoint; intros; apply functional_extensionality; intuition.
  destruct (m1 x); auto.
Qed.

Theorem sep_star_comm:
  forall p1 p2,
  (p1 * p2 ==> p2 * p1)%pred.
Proof.
  unfold pimpl, sep_star; pred.
  exists x0; exists x. intuition eauto using mem_union_comm. apply mem_disjoint_comm; auto.
Qed.

Theorem sep_star_assoc:
  forall p1 p2 p3,
  (p1 * p2 * p3 <==> p1 * (p2 * p3))%pred.
Proof.
  split; unfold pimpl, sep_star; pred.
  - exists x1; exists (mem_union x2 x0); intuition.
    apply mem_union_assoc; auto.
    apply mem_disjoint_assoc_1; auto.
    exists x2; exists x0; intuition eauto.
    eapply mem_disjoint_union; eauto.
  - exists (mem_union x x1); exists x2; intuition.
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


(** ** Hoare triples *)

Definition corr (pre: pred) (prog1 prog2: prog) :=
  forall m m' out,
  pre m ->
  exec_recover m prog1 prog2 m' out ->
  out = Finished.

Notation "{{ pre }} p1 >> p2" := (corr pre%pred p1 p2)
  (at level 0, p1 at level 60, p2 at level 60).

Theorem upd_eq : forall m a v a',
  a' = a
  -> upd m a v a' = Some v.
Proof.
  intros; subst; unfold upd.
  destruct (eq_nat_dec a a); tauto.
Qed.

Local Hint Extern 1 =>
  match goal with
    | [ |- upd _ ?a ?v ?a = Some ?v ] => apply upd_eq; auto
  end.

Theorem upd_ne : forall m a v a',
  a' <> a
  -> upd m a v a' = m a'.
Proof.
  intros; subst; unfold upd.
  destruct (eq_nat_dec a' a); tauto.
Qed.

Ltac inv_option :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H; subst
  | [ H: ?a = Some ?b |- _ ] =>
    match goal with
    | [ H': a = Some ?c |- _ ] =>
      match b with
      | c => fail 1
      | _ => rewrite H in H'
      end
    end
  end.

Ltac inv_exec_recover :=
  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Theorem pimpl_ok:
  forall pre pre' pr rec,
  {{pre'}} pr >> rec ->
  (pre ==> pre') ->
  {{pre}} pr >> rec.
Proof.
  unfold corr, pimpl. eauto.
Qed.

Theorem pimpl_pre:
  forall pre pre' pr rec,
  (pre ==> [{{pre'}} pr >> rec]) ->
  (pre ==> pre') ->
  {{pre}} pr >> rec.
Proof.
  firstorder.
Qed.

Theorem read_ok:
  forall (a:addr) (rx:valu->prog) (rec:prog),
  ({{ exists v F, a |-> v * F
   /\ [{{ a |-> v * F }} (rx v) >> rec]
   /\ [{{ a |-> v * F }} rec >> rec] }}
   Read a rx >> rec)%pred.
Proof.
  unfold corr; unfold exis, foral_, lift, and; pred.
  remember H1 as H1'; clear HeqH1'.
  unfold ptsto, sep_star in H1'; simpl in H1'; repeat deex.
  inv_exec_recover; auto; inv_exec.
  - erewrite mem_union_addr in H11. inversion H11. eauto. eauto.
  - eapply H. eauto. constructor.
    erewrite mem_union_addr in H10; eauto.
    inv_option. eauto.
  - eapply H; eauto.
    erewrite mem_union_addr in H11; eauto. inv_option.
    econstructor; eauto.
  - eapply H3; eauto.
Qed.

Lemma ptsto_upd:
  forall a v v0 F m,
  (a |-> v0 * F)%pred m ->
  (a |-> v * F)%pred (upd m a v).
Proof.
  unfold sep_star, upd; intros; repeat deex.
  exists (fun a' => if eq_nat_dec a' a then Some v else None).
  exists x0.
  split; [|split].
  - apply functional_extensionality; intro.
    unfold mem_union; destruct (eq_nat_dec x1 a); eauto.
    unfold ptsto in H1; destruct H1. rewrite H1; eauto.
  - unfold mem_disjoint in *. intuition. repeat deex.
    apply H. repeat eexists; eauto.
    unfold ptsto in H1; destruct H1.
    destruct (eq_nat_dec x1 a); subst; eauto.
    pred.
  - intuition eauto.
    unfold ptsto; intuition.
    destruct (eq_nat_dec a a); pred.
    destruct (eq_nat_dec a' a); pred.
Qed.

Theorem write_ok:
  forall (a:addr) (v:valu) (rx:prog) (rec:prog),
  ({{ exists v0 F, a |-> v0 * F
   /\ [{{ a |-> v * F }} rx >> rec]
   /\ [{{ a |-> v * F \/ a |-> v0 * F }} rec >> rec]}}
   Write a v rx >> rec)%pred.
Proof.
  unfold corr; pred.
  remember H1 as H1'; clear HeqH1'.
  unfold ptsto, sep_star in H1'; simpl in H1'; repeat deex.
  inv_exec_recover; auto; inv_exec.
  - erewrite mem_union_addr in H12. inversion H12. eauto. eauto.
  - eapply H. instantiate (1:=upd (mem_union x1 x2) a v).
    eapply ptsto_upd; eauto.
    eauto.
  - eapply H. instantiate (1:=upd (mem_union x1 x2) a v).
    eapply ptsto_upd; eauto.
    eauto.
  - eapply H3; eauto.
Qed.


(** * Some helpful [prog] combinators *)

Definition If_ P Q (b : {P} + {Q}) (p1 p2 : prog) :=
  if b then p1 else p2.

Theorem if_ok:
  forall P Q (b : {P}+{Q}) p1 p2 rec,
  {{ exists pre, pre
  /\ [{{ pre /\ [P] }} p1 >> rec]
  /\ [{{ pre /\ [Q] }} p2 >> rec]
  }} If_ b p1 p2 >> rec.
Proof.
  unfold corr; destruct b; intuition pred.
Qed.

Fixpoint For_ (L : Set) (f : nat -> L -> (L -> prog) -> prog)
              (i n : nat) (l : L)
              (nocrash : nat -> L -> pred)
              (crashed : pred)
              (rx: L -> prog) : prog :=
  match n with
    | O => rx l
    | S n' => l' <- (f i l); (For_ f (S i) n' l' nocrash crashed rx)
  end.

Theorem for_ok:
  forall (L : Set) f rx rec (nocrash : nat -> L -> pred) (crashed : pred)
         n i (li : L),
  {{ nocrash i li
  /\ [forall m l, nocrash m l ==> crashed]
  /\ [forall m lm rxm,
      i <= m < n + i ->
      (forall lSm, {{ nocrash (S m) lSm }} (rxm lSm) >> rec) ->
      {{ nocrash m lm }} f m lm rxm >> rec]
  /\ [forall lfinal, {{ nocrash (n+i) lfinal }} (rx lfinal) >> rec]
  }} (For_ f i n li nocrash crashed rx) >> rec.
Proof.
  induction n.
  - intros.
    eapply pimpl_pre.
    + unfold pimpl; intuition pred.
    + unfold pimpl; pred.
  - intros.
    eapply pimpl_pre.
    + unfold pimpl; intuition pred.
      eapply H1; try omega.
      intros.
      eapply pimpl_ok.
      apply IHn.
      unfold pimpl; intuition pred.
      eapply H1; try omega; eauto.
      replace (n + S i) with (S (n + i)) by omega.
      eauto.
    + unfold pimpl; pred.
Qed.


(*
Theorem CFor:
  forall {L : Set} (f : nat -> L -> prog L)
         (nocrash : nat -> L -> pred) (crashed : pred),
  (forall m l, nocrash m l --> crashed) ->
  forall n i l,
    (forall m lx,
     i <= m < n + i ->
     {{nocrash m lx}}
     (f m lx)
     {{r, (exists lx', [r = Halted lx'] /\ nocrash (S m) lx') \/
          ([r = Crashed] /\ crashed)}}) ->
    {{nocrash i l}}
    (For_ f i n l)
    {{r, (exists l', [r = Halted l'] /\ nocrash (n + i) l') \/
         ([r = Crashed] /\ crashed)}}.
Proof.
  induction n; simpl; intros.

  eapply Conseq.
  apply CHalt.
  apply pimpl_refl.
  simpl.
  pred.

  eapply Conseq.
  econstructor.
  eapply H0.
  omega.
  simpl.
  intros.
  eapply Conseq.
  apply IHn.
  intros.
  apply H0; omega.
  pred.
  simpl.
  intros.
  apply pimpl_refl.
  apply pimpl_refl.
  pred.
  replace (S (n + i)) with (n + S i) by omega; eauto.
Qed.
*)

Lemma pimpl_exists_l:
  forall T p q,
  (forall x:T, p x ==> q) ->
  (exists x:T, p x) ==> q.
Proof.
  firstorder.
Qed.

Lemma pimpl_exists_r:
  forall T p q,
  (exists x:T, p ==> q x) ->
  (p ==> exists x:T, q x).
Proof.
  firstorder.
Qed.

Lemma pimpl_trans:
  forall a b c,
  (a ==> b) ->
  (b ==> c) ->
  (a ==> c).
Proof.
  firstorder.
Qed.

Lemma pimpl_apply:
  forall (p q:pred) m,
  p m ->
  (p ==> q) ->
  q m.
  (* XXX change level of ==> to bind more tightly than -> *)
Proof.
  firstorder.
Qed.

(*
Lemma pimpl_sep_star:
  forall a b c d,
  (a ==> c) ->
  (b ==> d) ->
  (a * b ==> c * d).
Proof.
  admit.
Qed.
*)

(*

Lemma sep_star_lift_l:
  forall (a: Prop) (b c: pred),
  (a -> (b ==> c)) ->
  [a] * b ==> c.
Proof.
*)

Lemma pimpl_star_emp: forall p, p ==> emp * p.
Proof.
  unfold sep_star, pimpl; intros.
  repeat eexists; eauto.
  unfold mem_union; eauto.
  unfold mem_disjoint; pred.
Qed.

Lemma star_emp_pimpl: forall p, emp * p ==> p.
Proof.
  unfold sep_star, pimpl; intros.
  unfold emp in *; pred.
  assert (mem_union x x0 = x0).
  apply functional_extensionality; unfold mem_union; intros.
  case_eq (x x1); intuition. rewrite H1 in H0; pred.
  pred.
Qed.

Lemma emp_star: forall p, p <==> emp * p.
Proof.
  intros; split; [ apply pimpl_star_emp | apply star_emp_pimpl ].
Qed.

Opaque sep_star.


(** * Separation logic proof automation *)

Hint Extern 1 ({{_}} progseq1 (Write _ _) _ >> _) => apply write_ok : prog.
Hint Extern 1 ({{_}} progseq2 (Read _) _ >> _) => apply read_ok : prog.

Ltac intu' :=
  match goal with
  | [ H : ex _ |- _ ] => destruct H
  | [ |- ex _ ] => eexists
  end.

Ltac intu := intuition; repeat (intu'; intuition).

Ltac pintu := unfold lift, and, or, exis, pimpl, impl; intu.

Definition stars (ps : list pred) :=
  fold_left sep_star ps emp.

Ltac sep_imply'' H := eapply pimpl_apply; [ apply H | ].

Ltac sep_imply' m :=
  match goal with
  | [ H : _ m |- _ ] => sep_imply'' H
  | [ H : _ _ m |- _ ] => sep_imply'' H
  | [ H : _ _ _ m |- _ ] => sep_imply'' H
  end.

Ltac sep_imply :=
  match goal with
  | [ |- _ ?m ] => sep_imply' m
  | [ |- _ _ ?m ] => sep_imply' m
  | [ |- _ _ _ ?m ] => sep_imply' m
  end.

Theorem start_canceling : forall p q ps qs,
  p <==> stars ps
  -> q <==> stars qs
  -> (stars ps * stars nil ==> stars qs)
  -> p ==> q.
Proof.
  unfold stars; simpl; intros.
  eapply pimpl_trans; [apply H|].
  eapply pimpl_trans; [apply pimpl_star_emp|].
  eapply pimpl_trans; [apply sep_star_comm|].
  eapply pimpl_trans; [apply H1|].
  apply H0.
Qed.

Lemma flatten_default : forall p,
  p <==> stars (p :: nil).
Proof.
  unfold stars; apply emp_star.
Qed.

Lemma flatten_emp : emp <==> stars nil.
Proof.
  firstorder.
Qed.

Lemma flatten_star : forall p q ps qs,
  p <==> stars ps
  -> q <==> stars qs
  -> p * q <==> stars (ps ++ qs).
Admitted.

Ltac flatten := repeat match goal with
                       | [ |- emp <==> _ ] => apply flatten_emp
                       | [ |- _ * _ <==> _ ] => eapply flatten_star
                       | _ => apply flatten_default
                       end.

Definition okToUnify (p1 p2 : pred) := p1 = p2.

Hint Extern 1 (okToUnify (?p |-> _) (?p |-> _)) => constructor : okToUnify.
Hint Extern 1 (okToUnify (diskIs _) (diskIs _)) => constructor : okToUnify.
(* XXX the above unification rule might help us deal with array predicates *)

Inductive pick (lhs : pred) : list pred -> list pred -> Prop :=
| PickFirst : forall p ps,
  okToUnify lhs p
  -> pick lhs (p :: ps) ps
| PickLater : forall p ps ps',
  pick lhs ps ps'
  -> pick lhs (p :: ps) (p :: ps').

Ltac pick := solve [ repeat ((apply PickFirst; solve [ auto with okToUnify ])
                               || apply PickLater) ].

Theorem cancel_one : forall qs qs' p ps F,
  pick p qs qs'
  -> (stars ps * F ==> stars qs')
  -> stars (p :: ps) * F ==> stars qs.
Admitted.

Ltac cancel_one := eapply cancel_one; [ pick | ].

Theorem delay_one : forall p ps q qs,
  (stars ps * stars (p :: qs) ==> q)
  -> stars (p :: ps) * stars qs ==> q.
Admitted.

Ltac delay_one := apply delay_one.

Lemma finish_frame : forall p,
  stars nil * p ==> stars (p :: nil).
Proof.
  unfold stars. intros. apply pimpl_refl.
Qed.

Lemma finish_easier : forall p,
  stars nil * p ==> p.
Proof.
  unfold stars. apply emp_star.
Qed.

Ltac cancel := eapply start_canceling; [ flatten | flatten | cbv beta; simpl ];
               repeat (cancel_one || delay_one);
               try (apply finish_frame || apply finish_easier).

Ltac sep := sep_imply; cancel.

Ltac step := intros;
             eapply pimpl_ok; [ solve [ eauto with prog ] | pintu ];
             try solve [ intuition sep ]; (unfold stars; simpl);
             try omega.

Ltac hoare := repeat step.

Definition do_two_writes a1 a2 v1 v2 rx :=
  Write a1 v1 ;; Write a2 v2 ;; rx.

Example two_writes: forall a1 a2 v1 v2 rx rec,
  ({{ exists v1' v2' F,
      a1 |-> v1' * a2 |-> v2' * F
   /\ [{{ a1 |-> v1 * a2 |-> v2 * F }} rx >> rec]
   /\ [{{ (a1 |-> v1' * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec] }}
   do_two_writes a1 a2 v1 v2 rx >> rec)%pred.
Proof.
  unfold do_two_writes.
  hoare.
Qed.

Hint Extern 1 ({{_}} progseq1 (do_two_writes _ _ _ _) _ >> _) => apply two_writes : prog.

Example read_write: forall a v rx rec,
  ({{ exists v' F,
      a |-> v' * F
   /\ [{{ a |-> v * F }} (rx v) >> rec]
   /\ [{{ (a |-> v' * F) \/
          (a |-> v * F) }} rec >> rec] }}
   Write a v ;; x <- Read a ; rx x >> rec)%pred.
Proof.
  hoare.
Qed.

Example four_writes: forall a1 a2 v1 v2 rx rec,
  ({{ exists v1' v2' F,
      a1 |-> v1' * a2 |-> v2' * F
   /\ [{{ a1 |-> v1 * a2 |-> v2 * F }} rx >> rec]
   /\ [{{ (a1 |-> v1' * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2' * F) \/
          (a1 |-> v1 * a2 |-> v2 * F) }} rec >> rec] }}
   do_two_writes a1 a2 v1 v2 ;; do_two_writes a1 a2 v1 v2 ;; rx >> rec)%pred.
Proof.
  hoare.
Qed.

Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).
Hint Extern 1 ({{_}} If_ _ _ _ >> _) => apply if_ok : prog.

Example inc_up_to_5: forall a rx rec,
  ({{ exists v F,
      a |-> v * F
   /\ [{{ [v < 5] --> (a |-> (S v) * F)
       /\ [v >= 5] --> (a |-> v * F) }} rx >> rec]
(*
   /\ [{{ (a |-> (S v) * F)
       \/ (a |-> v * F) }} rx >> rec]
*)
   /\ [{{ (a |-> v * F) \/
          (a |-> S v * F) }} rec >> rec] }}
   x <- !a;
   If (lt_dec x 5) {
     a <-- (S x) ;; rx
   } else {
     rx
   } >> rec)%pred.
Proof.
  hoare.
Qed.

Notation "'For' i < n 'Loopvar' l < l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        0 n l0
        (fun i l => nocrash%pred)
        (crashed%pred))
  (at level 9, i at level 0, n at level 0, lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).

Hint Extern 1 ({{_}} progseq2 (For_ _ _ _ _ _ _) _ >> _) => apply for_ok : prog.

Lemma pre_false:
  forall pre p1 p2,
  (pre ==> [False]) ->
  {{ pre }} p1 >> p2.
Proof.
  firstorder.
Qed.

Example count_up: forall (n:nat) rx rec F,
  {{ F
  /\ [{{ F }} (rx n) >> rec]
  /\ [{{ F }} rec >> rec]
  }} r <- For i < n
     Loopvar l < 0
     Continuation lrx
     Invariant
       [l=i] /\ F
       /\ [{{ F }} rx n >> rec]
       /\ [{{ F }} rec >> rec]
     OnCrash
       [True]
     Begin
       lrx (S l)
     Rof; rx r
  >> rec.
Proof.
  hoare.
  destruct (eq_nat_dec lfinal n).
  - eapply pimpl_ok.
    subst; eauto.
    firstorder.
  - eapply pre_false.
    unfold pimpl; pred.
Qed.


Notation "'Halt'" := Halt' : prog'_scope.
Notation "'Crash'" := Crash' : prog'_scope.
Notation "!" := Read' : prog'_scope.
Infix "<--" := Write' : prog'_scope.
Notation "'Call0'" := Call'0 : prog'_scope.
Notation "'Call1' f" := (Call'2 (fun _: unit => f)) (at level 9) : prog'_scope.
Notation "'Call2'" := Call'2 : prog'_scope.
Notation "p1 ;; p2" := (Seq' p1 (fun _ : unit => p2)) : prog'_scope.
Notation "x <- p1 ; p2" := (Seq' p1 (fun x => p2)) : prog'_scope.
Delimit Scope prog'_scope with prog'.
Bind Scope prog'_scope with prog'.




Notation "$( ghostT : p )" := (prog'Out (p%prog' : prog' ghostT _))
  (ghostT at level 0).


(** * A log-based transactions implementation *)

Definition disjoint (r1 : addr * nat) (r2 : addr * nat) :=
  forall a, fst r1 <= a < fst r1 + snd r1
    -> ~(fst r2 <= a < fst r2 + snd r2).

Fixpoint disjoints (rs : list (addr * nat)) :=
  match rs with
    | nil => True
    | r1 :: rs => Forall (disjoint r1) rs /\ disjoints rs
  end.

Record xparams := {
  DataStart : addr; (* The actual committed data start at this disk address. *)
    DataLen : nat;  (* Size of data region *)

  LogLength : addr; (* Store the length of the log here. *)
  LogCommit : addr; (* Store true to apply after crash. *)

   LogStart : addr; (* Start of log region on disk *)
     LogLen : nat;  (* Size of log region *)

   Disjoint : disjoints ((DataStart, DataLen)
     :: (LogLength, 1)
     :: (LogCommit, 1)
     :: (LogStart, LogLen*2)
     :: nil)
}.

Ltac disjoint' xp :=
  generalize (Disjoint xp); simpl; intuition;
    repeat match goal with
             | [ H : True |- _ ] => clear H
             | [ H : Forall _ nil |- _ ] => clear H
             | [ H : Forall _ (_ :: _) |- _ ] => inversion_clear H
           end; unfold disjoint in *; simpl in *; subst.

Ltac disjoint'' a :=
  match goal with
    | [ H : forall a', _ |- _ ] => specialize (H a); omega
  end.

Ltac disjoint xp :=
  disjoint' xp;
  match goal with
    | [ _ : _ <= ?n |- _ ] => disjoint'' n
    | [ _ : _ = ?n |- _ ] => disjoint'' n
  end.

Hint Rewrite upd_eq upd_ne using (congruence
  || match goal with
       | [ xp : xparams |- _ ] => disjoint xp
     end).

Ltac hoare' :=
  match goal with
    | [ H : Crashed = Crashed |- _ ] => clear H
    | [ H : Halted _ = Halted _ |- _ ] => injection H; clear H; intros; subst
  end.

Ltac hoare_ghost g := apply (spost_sound g); simpl; pred; repeat hoare'; intuition eauto.

Ltac hoare := intros; match goal with
                        | _ => hoare_ghost tt
                        | [ x : _ |- _ ] => hoare_ghost x
                      end.

Inductive logstate :=
| NoTransaction (cur : mem)
(* Don't touch the disk directly in this state. *)
| ActiveTxn (old_cur : mem * mem)
(* A transaction is in progress.
 * It started from the first memory and has evolved into the second.
 * It has not committed yet. *)
| CommittedTxn (cur : mem)
(* A transaction has committed but the log has not been applied yet. *).

Module Type LOG.
  (* Methods *)
  Parameter init : xparams -> prog unit.
  Parameter begin : xparams -> prog unit.
  Parameter commit : xparams -> prog unit.
  Parameter abort : xparams -> prog unit.
  Parameter recover : xparams -> prog unit.
  Parameter read : xparams -> addr -> prog valu.
  Parameter write : xparams -> addr -> valu -> prog unit.

  (* Representation invariant *)
  Parameter rep : xparams -> logstate -> pred.

  (* Specs *)
  Axiom init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ diskIs m)}}.

  Axiom begin_ok : forall xp m, {{rep xp (NoTransaction m)}} (begin xp)
    {{r, rep xp (ActiveTxn (m, m))
      \/ ([r = Crashed] /\ rep xp (NoTransaction m))}}.

  Axiom commit_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (commit xp)
    {{r, rep xp (NoTransaction m2)
      \/ ([r = Crashed] /\ (rep xp (ActiveTxn (m1, m2)) \/
                            rep xp (CommittedTxn m2)))}}.

  Axiom abort_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (abort xp)
    {{r, rep xp (NoTransaction m1)
      \/ ([r = Crashed] /\ rep xp (ActiveTxn (m1, m2)))}}.

  Axiom recover_ok : forall xp m, {{rep xp (NoTransaction m) \/
                                    (exists m', rep xp (ActiveTxn (m, m'))) \/
                                    rep xp (CommittedTxn m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (CommittedTxn m))}}.

  Axiom read_ok : forall xp a ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (read xp a)
    {{r, rep xp (ActiveTxn ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.

  Axiom write_ok : forall xp a v ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (write xp a v)
    {{r, rep xp (ActiveTxn (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (ActiveTxn ms))}}.
End LOG.

Module Log : LOG.
  (* Actually replay a log to implement redo in a memory. *)
  Fixpoint replay (a : addr) (len : nat) (m : mem) : mem :=
    match len with
      | O => m
      | S len' => upd (replay a len' m) (m (a + len'*2)) (m (a + len'*2 + 1))
    end.

  (* Check that a log is well-formed in memory. *)
  Fixpoint validLog xp (a : addr) (len : nat) (m : mem) : Prop :=
    match len with
      | O => True
      | S len' => DataStart xp <= m (a + len'*2) < DataStart xp + DataLen xp
        /\ validLog xp a len' m
    end.

  Definition rep xp (st : logstate) :=
    match st with
      | NoTransaction m =>
        (* Not committed. *)
        (LogCommit xp) |-> 0
        (* Every data address has its value from [m]. *)
        /\ foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
        --> a |-> m a

      | ActiveTxn (old, cur) =>
        (* Not committed. *)
        (LogCommit xp) |-> 0
        (* Every data address has its value from [old]. *)
        /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> old a)
        (* Look up log length. *)
        /\ exists len, (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            (* All log entries reference data addresses. *)
            /\ [validLog xp (LogStart xp) len m]
            (* We may compute the current memory by replaying the log. *)
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> cur a = replay (LogStart xp) len m a]

      | CommittedTxn cur =>
        (* Committed but not applied. *)
        (LogCommit xp) |-> 1
        (* Log produces cur. *)
        /\ exists len, (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> cur a = replay (LogStart xp) len m a]
    end%pred.

  Definition init xp := $(unit:
    (LogCommit xp) <-- 0
  ).

  Theorem init_ok : forall xp m, {{diskIs m}} (init xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ diskIs m)}}.
  Proof.
    hoare.
  Qed.

  Definition begin xp := $(unit:
    (LogLength xp) <-- 0
  ).
    
  Hint Extern 1 (_ <= _) => omega.

  Ltac t'' := intuition eauto; pred;
    try solve [ symmetry; eauto ].

  Ltac t' := t'';
    repeat (match goal with
              | [ |- ex _ ] => eexists
            end; t'').

  Ltac t := t';
    match goal with
      | [ |- _ \/ _ ] => (left; solve [t]) || (right; solve [t])
      | _ => idtac
    end.

  Theorem begin_ok : forall xp m, {{rep xp (NoTransaction m)}} (begin xp)
    {{r, rep xp (ActiveTxn (m, m))
      \/ ([r = Crashed] /\ rep xp (NoTransaction m))}}.
  Proof.
    hoare; t.
  Qed.

  Definition apply xp := $(mem:
    len <- !(LogLength xp);
    For i < len
      Ghost cur
      Loopvar _
      Invariant (exists m, diskIs m
        /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
          -> cur a = replay (LogStart xp) len m a]
        /\ (LogCommit xp) |-> 1
        /\ (LogLength xp) |-> len
        /\ [len <= LogLen xp]
        /\ [validLog xp (LogStart xp) len m]
        /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
          -> m a = replay (LogStart xp) i m a])
      OnCrash rep xp (NoTransaction cur) \/
              rep xp (CommittedTxn cur)
      Begin
      a <- !(LogStart xp + i*2);
      v <- !(LogStart xp + i*2 + 1);
      a <-- v
    Pool tt;;
    (LogCommit xp) <-- 0
  ).

  Lemma validLog_irrel : forall xp a len m1 m2,
    validLog xp a len m1
    -> (forall a', a <= a' < a + len*2
      -> m1 a' = m2 a')
    -> validLog xp a len m2.
  Proof.
    induction len; simpl; intuition eauto;
      try match goal with
            | [ H : _ |- _ ] => rewrite <- H by omega; solve [ auto ]
            | [ H : _ |- _ ] => eapply H; intuition eauto
          end.
  Qed.

  Lemma validLog_data : forall xp m len a x1,
    m < len
    -> validLog xp a len x1
    -> DataStart xp <= x1 (a + m * 2) < DataStart xp + DataLen xp.
  Proof.
    induction len; simpl; intros.
    intuition.
    destruct H0.
    destruct (eq_nat_dec m len); subst; auto.
  Qed.

  Lemma upd_same : forall m1 m2 a1 a2 v1 v2 a',
    a1 = a2
    -> v1 = v2
    -> (a' <> a1 -> m1 a' = m2 a')
    -> upd m1 a1 v1 a' = upd m2 a2 v2 a'.
  Proof.
    intros; subst; unfold upd; destruct (eq_nat_dec a' a2); auto.
  Qed.

  Hint Resolve upd_same.

  Lemma replay_irrel : forall xp a',
    DataStart xp <= a' < DataStart xp + DataLen xp
    -> forall a len m1 m2,
      (forall a', a <= a' < a + len*2
        -> m1 a' = m2 a')
      -> m1 a' = m2 a'
      -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition eauto.
    apply upd_same; eauto.
  Qed.

  Hint Rewrite plus_0_r.

  Lemma replay_redo : forall a a' len m1 m2,
    (forall a'', a <= a'' < a + len*2
      -> m1 a'' = m2 a'')
    -> (m1 a' <> m2 a'
      -> exists k, k < len
        /\ m1 (a + k*2) = a'
        /\ m2 (a + k*2) = a')
    -> ~(a <= a' < a + len*2)
    -> replay a len m1 a' = replay a len m2 a'.
  Proof.
    induction len; simpl; intuition.
    destruct (eq_nat_dec (m1 a') (m2 a')); auto.
    apply H0 in n.
    destruct n; intuition omega.

    apply upd_same; eauto; intros.
    apply IHlen; eauto; intros.
    apply H0 in H3.
    destruct H3; intuition.
    destruct (eq_nat_dec x len); subst; eauto.
    2: exists x; eauto.
    tauto.
  Qed.

  Theorem apply_ok : forall xp m, {{rep xp (CommittedTxn m)}} (apply xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (CommittedTxn m))}}.
  Proof.
    hoare.

    - eauto 10.
    - eauto 10.
    - eauto 12.
    - eauto 12.
    - eauto 12.
    - assert (DataStart xp <= x1 (LogStart xp + m0 * 2) < DataStart xp + DataLen xp) by eauto using validLog_data.
      left; exists tt; intuition eauto.
      eexists; intuition eauto.
      + rewrite H0 by auto.
        apply replay_redo.
        * pred.
        * destruct (eq_nat_dec a (x1 (LogStart xp + m0 * 2))); subst; eauto; pred.
          eexists; intuition eauto; pred.
        * pred.
          disjoint xp.
      + pred.
      + pred.
      + eapply validLog_irrel; eauto; pred.
      + apply upd_same; pred.
        rewrite H9 by auto.
        apply replay_redo.
        * pred.
        * destruct (eq_nat_dec a (x1 (LogStart xp + m0 * 2))); subst; eauto; pred.
        * pred.
          disjoint xp.
    - eauto 12.
    - left; intuition.
      pred.
      firstorder.
  Qed.

  Definition commit xp := $(unit:
    (LogCommit xp) <-- 1;;
    Call1 (apply_ok xp)
  ).

  Theorem commit_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (commit xp)
    {{r, rep xp (NoTransaction m2)
      \/ ([r = Crashed] /\ (rep xp (ActiveTxn (m1, m2)) \/
                            rep xp (CommittedTxn m2)))}}.
  Proof.
    hoare.
    destruct (H m2); pred.
    eexists; intuition eauto.
    eexists; intuition eauto.
    - eapply validLog_irrel; eauto; pred.
    - erewrite replay_irrel; eauto; pred.
  Qed.

  Definition abort xp := $(unit:
    (LogLength xp) <-- 0
  ).

  Theorem abort_ok : forall xp m1 m2, {{rep xp (ActiveTxn (m1, m2))}}
    (abort xp)
    {{r, rep xp (NoTransaction m1)
      \/ ([r = Crashed] /\ rep xp (ActiveTxn (m1, m2)))}}.
  Proof.
    hoare.
  Qed.

  Definition recover xp := $(unit:
    com <- !(LogCommit xp);
    If (eq_nat_dec com 1) {
      Call1 (apply_ok xp)
    } else {
      Halt tt
    }
  ).

  Theorem recover_ok : forall xp m, {{rep xp (NoTransaction m) \/
                                      (exists m', rep xp (ActiveTxn (m, m'))) \/
                                      rep xp (CommittedTxn m)}}
    (recover xp)
    {{r, rep xp (NoTransaction m)
      \/ ([r = Crashed] /\ rep xp (CommittedTxn m))}}.
  Proof.
    hoare.
    destruct (H0 m); pred.
  Qed.

  Definition read xp a := $((mem*mem):
    len <- !(LogLength xp);
    v <- !a;

    For i < len
      Ghost old_cur
      Loopvar v
      Invariant (
        [DataStart xp <= a < DataStart xp + DataLen xp]
        /\ (foral a, [DataStart xp <= a < DataStart xp + DataLen xp]
          --> a |-> fst old_cur a)
        /\ (LogCommit xp) |-> 0
        /\ (LogLength xp) |-> len
          /\ [len <= LogLen xp]
          /\ exists m, diskIs m
            /\ [validLog xp (LogStart xp) len m]
            /\ [forall a, DataStart xp <= a < DataStart xp + DataLen xp
              -> snd old_cur a = replay (LogStart xp) len m a]
            /\ [v = replay (LogStart xp) i m a])
      OnCrash rep xp (ActiveTxn old_cur)
      Begin
      a' <- !(LogStart xp + i*2);
      If (eq_nat_dec a' a) {
        v <- !(LogStart xp + i*2 + 1);
        Halt v
      } else {
        Halt v
      }
    Pool v
  ).

  Theorem read_ok : forall xp a ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (read xp a)
    {{r, rep xp (ActiveTxn ms)
      /\ [r = Crashed \/ r = Halted (snd ms a)]}}.
  Proof.
    hoare.

    - eauto 7.
    - eauto 20.
    - eauto 20.
    - eauto 20.

    - left; eexists; intuition.
      eexists; pred.

    - eauto 20.

    - left; eexists; intuition.
      eexists; pred.

    - eauto 10.

    - rewrite H6; pred.
  Qed.

  Definition write xp a v := $(unit:
    len <- !(LogLength xp);
    If (le_lt_dec (LogLen xp) len) {
      Crash
    } else {
      (LogStart xp + len*2) <-- a;;
      (LogStart xp + len*2 + 1) <-- v;;
      (LogLength xp) <-- (S len)
    }
  ).

  Theorem write_ok : forall xp a v ms,
    {{[DataStart xp <= a < DataStart xp + DataLen xp]
      /\ rep xp (ActiveTxn ms)}}
    (write xp a v)
    {{r, rep xp (ActiveTxn (fst ms, upd (snd ms) a v))
      \/ ([r = Crashed] /\ rep xp (ActiveTxn ms))}}.
  Proof.
    hoare.

    - right; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.

    - right; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * eapply validLog_irrel; eauto; pred.
        * erewrite replay_irrel; eauto; pred.

    - left; intuition.
      + pred.
      + eexists; intuition eauto.
        eexists; intuition eauto.
        * pred.
          eapply validLog_irrel; eauto; pred.
        * pred.
          apply upd_same; pred.
          rewrite H11 by auto.
          erewrite replay_irrel; eauto; pred.
  Qed.
End Log.


Inductive recovery_outcome (R:Set) :=
| RHalted (v : R)
| RRecovered.
Implicit Arguments RHalted [R].
Implicit Arguments RRecovered [R].

Inductive exec_tryrecover xp : mem -> mem -> outcome unit -> Prop :=
| XTROK : forall m m' r,
  exec m (Log.recover xp) m' r ->
  exec_tryrecover xp m m' r
| XTRCrash : forall m m' m'' r,
  exec_tryrecover xp m m' Crashed ->
  exec m' (Log.recover xp) m'' r ->
  exec_tryrecover xp m m'' r.

Inductive exec_recover xp : forall {R : Set}, mem -> prog R -> mem -> recovery_outcome R -> Prop :=
| XROK : forall (R:Set) m (p:prog R) m' v,
  exec m p m' (Halted v) ->
  exec_recover xp m p m' (RHalted v)
| XRCrash : forall (R:Set) m (p:prog R) m' m'',
  exec m p m' Crashed ->
  exec_tryrecover xp m' m'' (Halted tt) ->
  exec_recover xp m p m'' RRecovered.

Inductive recover_corr xp : forall {R : Set},
     pred        (* precondition *)
  -> prog R      (* program *)
  -> (R -> pred) (* postcondition if halted *)
  -> pred        (* postcondition if crashed and recovered *)
  -> Prop :=
| RCbase : forall (R:Set) pre (p:prog R) post postcrash,
  corr pre p post ->
  corr (post Crashed) (Log.recover xp) postcrash ->
  corr (postcrash Crashed) (Log.recover xp) postcrash ->
  recover_corr xp pre p (fun r => post (Halted r)) (postcrash (Halted tt))
| RCConseq : forall (R:Set) pre (p:prog R) post postcrash pre' post' postcrash',
  recover_corr xp pre p post postcrash ->
  (pre' --> pre) ->
  (forall r, post r --> post' r) ->
  (postcrash --> postcrash') ->
  recover_corr xp pre' p post' postcrash'.

Hint Constructors recover_corr.

Parameter the_xp : xparams.
Notation "{{ pre }} p {{ r , postok }} {{ postcrash }}" :=
  (recover_corr the_xp (pre)%pred p (fun r => postok)%pred (postcrash)%pred)
  (at level 0, p at level 9).

Require Import Eqdep.
Ltac deexistT :=
  match goal with
  | [ H: existT _ _ _ = existT _ _ _ |- _ ] => apply inj_pair2 in H
  end.

Ltac invert_exec :=
  match goal with
  | [ H: exec _ _ _ _ |- _ ] => apply invert_exec in H
  end.

Theorem recover_corr_sound: forall xp R pre p postok postcrash,
  @recover_corr xp R pre p postok postcrash ->
  forall m m' rr,
  exec_recover xp m p m' rr ->
  pre m ->
  ((exists v, rr = RHalted v /\ postok v m') \/
   (rr = RRecovered /\ postcrash m')).
Proof.
  induction 1.

  - intros m m' rr Hexec Hpre.
    inversion Hexec; clear Hexec; repeat deexistT.
    + left; eexists; intuition eauto; subst.
      eapply corr_sound; eauto.
    + right; intuition eauto; subst.
      match goal with
      | [ H: exec_tryrecover _ _ _ _ |- _ ] => induction H
      end.
      * eapply corr_sound with (pre:=(post Crashed)); eauto.
        eapply corr_sound; eauto.
      * eapply corr_sound with (pre:=(postcrash Crashed)); eauto.

  - intros.
    edestruct IHrecover_corr; eauto.
    + destruct H5. destruct H5.
      left; eexists; split; eauto.
      apply H1; eauto.
    + destruct H5.
      right; split; eauto.
Qed.



Definition wrappable (R:Set) (p:prog R) (fn:mem->mem) := forall m0 m,
  {{Log.rep the_xp (ActiveTxn (m0, m))}}
  p
  {{r, Log.rep the_xp (ActiveTxn (m0, fn m))
    \/ ([r = Crashed] /\ exists m', Log.rep the_xp (ActiveTxn (m0, m')))}}.

Definition txn_wrap (p:prog unit) (fn:mem->mem) (wr: wrappable p fn) := $(unit:
  Call1 (Log.begin_ok the_xp);;
  Call2 (wr);;
  Call2 (Log.commit_ok the_xp)
).

Theorem txn_wrap_ok_norecover:
  forall (p:prog unit) (fn:mem->mem) (wrappable_p: wrappable p fn) m,
  {{Log.rep the_xp (NoTransaction m)}}
  (txn_wrap wrappable_p)
  {{r, Log.rep the_xp (NoTransaction (fn m))
    \/ ([r = Crashed] /\ (Log.rep the_xp (NoTransaction m) \/
                          (exists m', Log.rep the_xp (ActiveTxn (m, m'))) \/
                          Log.rep the_xp (CommittedTxn (fn m))))}}.
Proof.
  hoare.
  - destruct (H1 m); clear H1; pred.
  - destruct (H m); clear H; pred.
    destruct (H0 m m); clear H0; pred.
    destruct (H m); clear H; pred.
  - destruct (H m); clear H; pred.
    destruct (H0 m (fn m)); clear H0; pred.
    destruct (H m); clear H; pred.
    destruct (H0 m m); clear H0; pred.
    destruct (H m); clear H; pred.
Qed.

Theorem txn_wrap_ok:
  forall (p:prog unit) (fn:mem->mem) (wrappable_p: wrappable p fn) m,
  {{Log.rep the_xp (NoTransaction m)}}
  (txn_wrap wrappable_p)
  {{r, Log.rep the_xp (NoTransaction (fn m))}}
  {{Log.rep the_xp (NoTransaction m) \/
    Log.rep the_xp (NoTransaction (fn m))}}.
Proof.
  intros.
  eapply RCConseq.
  instantiate (1:=(fun r : outcome unit =>
                     Log.rep the_xp (NoTransaction m) \/
                     Log.rep the_xp (NoTransaction (fn m)) \/
                     ([r = Crashed] /\ Log.rep the_xp (CommittedTxn m)) \/
                     ([r = Crashed] /\ Log.rep the_xp (CommittedTxn (fn m)))
                  )%pred (Halted tt)).
  instantiate (1:=fun r : unit =>
                  (fun res : outcome unit =>
                     match res with
                     | Halted _ => Log.rep the_xp (NoTransaction (fn m))
                     | Crashed => Log.rep the_xp (NoTransaction m) \/
                                  Log.rep the_xp (NoTransaction (fn m)) \/
                                  (exists m', Log.rep the_xp (ActiveTxn (m, m'))) \/
                                  Log.rep the_xp (CommittedTxn (fn m))
                     end
                   )%pred (Halted r)).
  instantiate (1:=(Log.rep the_xp (NoTransaction m))%pred).
  apply RCbase.

  (* corr 1: hoare triple for write_two_blocks *)
  eapply Conseq.
  apply txn_wrap_ok_norecover.
  pred.
  pred; destruct r; pred.

  (* corr 2: hoare triple for the first time recover runs *)
  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  (* corr 3: hoare triple for repeated recover runs *)
  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  constructor.  (* CPreOr *)
  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  eapply Conseq.
  apply Log.recover_ok.
  pred.
  pred.

  (* prove implicications from the original RCConseq *)
  pred.
  pred.
  pred.
Qed.



Definition write_two_blocks a1 a2 v1 v2 := $((mem*mem):
  Call1 (Log.write_ok the_xp a1 v1);;
  Call1 (Log.write_ok the_xp a2 v2)
(*
  Call2 (fun (z:unit) => Log.write_ok the_xp a2 v2)
*)
).

Theorem write_two_blocks_wrappable a1 a2 v1 v2
  (A1OK: DataStart the_xp <= a1 < DataStart the_xp + DataLen the_xp)
  (A2OK: DataStart the_xp <= a2 < DataStart the_xp + DataLen the_xp):
  wrappable (write_two_blocks a1 a2 v1 v2) (fun m => upd (upd m a1 v1) a2 v2).
Proof.
  unfold wrappable; intros.
  hoare_ghost (m0, m).
  - destruct (H5 (m0, m)); clear H5; pred.
  - destruct (H3 (m0, (upd m a1 v1))); clear H3; pred.
    destruct (H3 (m0, m)); clear H3; pred.
Qed.

Parameter a1 : nat.
Parameter a2 : nat.
Parameter v1 : nat.
Parameter v2 : nat.
Parameter A1OK: DataStart the_xp <= a1 < DataStart the_xp + DataLen the_xp.
Parameter A2OK: DataStart the_xp <= a2 < DataStart the_xp + DataLen the_xp.


Check (txn_wrap (write_two_blocks_wrappable v1 v2 A1OK A2OK)).
Check (txn_wrap_ok (write_two_blocks_wrappable v1 v2 A1OK A2OK)).



Definition wrappable_nd (R:Set) (p:prog R) (ok:pred) := forall m,
  {{Log.rep the_xp (ActiveTxn (m, m))}}
  p
  {{r, (exists! m', Log.rep the_xp (ActiveTxn (m, m')) /\ [ok m'])
    \/ ([r = Crashed] /\ exists m', Log.rep the_xp (ActiveTxn (m, m')))}}.

Definition txn_wrap_nd (p:prog unit) (ok:pred) (wr: wrappable_nd p ok) (m: mem) := $(unit:
  Call0 (Log.begin_ok the_xp m);;
  Call0 (wr m);;
  Call1 (fun m' => Log.commit_ok the_xp m m')
).

Theorem txn_wrap_nd_ok_norecover:
  forall (p:prog unit) (ok:pred) (wr: wrappable_nd p ok) m,
  {{Log.rep the_xp (NoTransaction m)}}
  (txn_wrap_nd wr m)
  {{r, (exists m', Log.rep the_xp (NoTransaction m') /\ [ok m'])
    \/ ([r = Crashed] (* /\ (Log.rep the_xp (NoTransaction m) \/
                          (exists m', Log.rep the_xp (ActiveTxn (m, m'))) \/
                          (exists m', Log.rep the_xp (CommittedTxn m') /\ [ok m'])) *) )}}.
Proof.
  hoare.
  destruct (H x2); clear H; pred.
  (* XXX something is still broken.. *)



  - destruct (H1 m); clear H1; pred.
  - destruct (H1 m); clear H1; pred.
    destruct (H m); clear H; pred.
    destruct (H1 m); clear H1; pred.
  - destruct (H1 m); clear H1; pred.
    destruct (H m); clear H; pred.
    + destruct (H m); clear H; pred.
    + (* we have our non-deterministic mem: x4 *)
      destruct (H0 m x4); clear H0; pred.

      destruct (H1 m); clear H1; pred.
      destruct (H0 m); clear H0; pred.
      destruct (H0 m); clear H0; pred.
      erewrite H2. apply H5. 
      erewrite H8 in H5.  apply H5.  appl
      (* XXX so close but something is broken..
       * we need to prove:
       *   Log.rep the_xp (ActiveTxn (m, x4)) m1
       * but we have:
       *   Log.rep the_xp (ActiveTxn (m, x7)) m1
       * where x7 and x4 are two possibly-different mem's, both of which satisfy ok.
       *
       * seems like the pre-/post-conditions of wr get copied to several places,
       * and when we destruct them, we end up with two possibly-different mem's,
       * since there's no constraint that they be the same..
       *)
Aborted.
