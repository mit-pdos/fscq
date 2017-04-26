Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Pred .
Require Import Hoare.
Require Import Word.
Require Import AsyncDisk.
Require Import Hashmap.
Require Import Errno.
Require Import ADestructPair DestructVarname.
Require Import VerdiTactics.
Require Import GoSemantics.
Require Import Orders PeanoNat.

Set Implicit Arguments.

(* Helpers for existential variables *)

Ltac set_evars :=
  repeat match goal with
              | [ |- context[?e] ] => is_evar e; 
                 match type of e with
                 | prod _ _ => idtac
                 | _ => let H := fresh in set (H := e)
                 end
            end.

Ltac subst_evars :=
  repeat match goal with
              | [ H := ?e |- _ ] => is_evar e; subst H
            end.

Ltac set_evars_in H :=
  repeat match type of H with
              | context[?e] => is_evar e; let E := fresh in set (E := e) in H
            end.


Ltac pred_apply' H := eapply pimpl_apply; [ | exact H ].

Ltac pred_apply := match goal with
  | [ H: _ ?m |- _ ?m ] => pred_apply' H
  | [ |- exists _, _ ] => eexists; pred_apply
  end.


(** * Separation logic proof automation *)

Definition pred_fold_left AT AEQ V (l : list (@pred AT AEQ V)) : pred :=
  match l with
  | nil => emp
  | a :: t => fold_left sep_star t a
  end.

Definition stars {AT AEQ V} (ps : list (@pred AT AEQ V)) :=
  pred_fold_left ps.
Arguments stars : simpl never.

Ltac sep_imply'' H := eapply pimpl_apply; [ | apply H ].

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

Theorem start_normalizing_left : forall AT AEQ V (p : @pred AT AEQ V) q ps,
  p <=p=> stars ps
  -> (stars ps * stars nil =p=> q)%pred
  -> p =p=> q.
Proof.
  unfold stars; simpl; intros.
  rewrite <- H0.
  rewrite <- emp_star_r. apply H.
Qed.

Theorem start_normalizing_right : forall AT AEQ V (p : @pred AT AEQ V) q qs,
  q <=p=> stars qs
  -> p =p=> stars qs
  -> p =p=> q.
Proof.
  unfold stars; simpl; intros.
  rewrite H0.
  rewrite <- H.
  apply pimpl_refl.
Qed.

Theorem start_normalizing_apply : forall AT AEQ V PT (p : @pred AT AEQ V) ps P m,
  p <=p=> (exists (x:PT), stars (ps x) * [[P x]])%pred
  -> p m
  -> (exists (x:PT), stars (ps x) * [[P x]])%pred m.
Proof.
  firstorder.
Qed.

Theorem restart_canceling:
  forall AT AEQ V p (q : @pred AT AEQ V),
  (stars p * stars nil =p=> q) ->
  (stars nil * stars p =p=> q).
Proof.
  intros; eapply pimpl_trans; [ eapply sep_star_comm | eauto ].
Qed.

Lemma stars_prepend':
  forall AT AEQ V l x,
  fold_left sep_star l x <=p=> x * fold_left sep_star l (@emp AT AEQ V).
Proof.
  induction l.
  - simpl. intros.
    eapply piff_trans.
    apply emp_star.
    apply sep_star_comm.
  - simpl. intros.
    eapply piff_trans.
    eapply IHl.
    eapply piff_trans.
    eapply sep_star_assoc.
    eapply piff_star_l.
    eapply piff_comm.
    eapply piff_trans.
    eapply IHl.
    eapply piff_comm.
    eapply piff_trans.
    eapply emp_star.
    eapply piff_comm.
    eapply piff_trans.
    eapply sep_star_assoc.
    eapply piff_refl.
Qed.

Lemma stars_prepend:
  forall AT AEQ V l (x : @pred AT AEQ V),
  stars (x :: l) <=p=> x * stars l.
Proof.
  unfold stars, pred_fold_left; simpl; intros.
  destruct l.
  - simpl; split.
    eapply pimpl_trans; [| eapply sep_star_comm ]. eapply pimpl_star_emp.
    eapply pimpl_trans; [eapply sep_star_comm |]. eapply star_emp_pimpl.
  - eapply piff_trans. apply stars_prepend'.
    eapply piff_star_l.
    simpl.
    eapply piff_trans; [ apply stars_prepend' |].
    eapply piff_trans; [| apply piff_comm; apply stars_prepend' ].
    apply piff_star_r.
    split.
    apply star_emp_pimpl.
    apply pimpl_star_emp.
Qed.

Lemma flatten_default' : forall AT AEQ V (p : @pred AT AEQ V),
  p <=p=> stars (p :: nil).
Proof.
  firstorder.
Qed.

Lemma flatten_default : forall AT AEQ V (p : @pred AT AEQ V),
  p <=p=> stars (p :: nil).
Proof.
  unfold stars; reflexivity.
Qed.

Lemma flatten_emp : forall AT AEQ V, (@emp AT AEQ V) <=p=> stars nil.
Proof.
  firstorder.
Qed.

Lemma flatten_star : forall AT AEQ V (p : @pred AT AEQ V) q ps qs,
  p <=p=> stars ps
  -> q <=p=> stars qs
  -> p * q <=p=> stars (ps ++ qs).
Proof.
  intros.
  eapply piff_trans; [eapply piff_star_r; apply H|]; clear H.
  eapply piff_trans; [eapply piff_star_l; apply H0|]; clear H0.
  induction ps.
  - eapply piff_trans; [apply piff_comm; apply emp_star|apply piff_refl].
  - apply piff_comm.
    eapply piff_trans; [apply stars_prepend|].
    eapply piff_trans; [apply piff_star_l; apply piff_comm; apply IHps|].
    eapply piff_trans; [apply piff_comm; apply sep_star_assoc|].
    apply piff_star_r.
    apply piff_comm.
    eapply piff_trans; [eapply stars_prepend|].
    apply piff_refl.
Qed.

Ltac flatten :=
  repeat match goal with
  | [ |- emp <=p=> _ ] => apply flatten_emp
  | [ |- _ * _ <=p=> _ ] =>
    eapply piff_trans; [ apply flatten_star | apply piff_refl ]
  | _ => apply flatten_default
  end.

Definition okToCancel {AT AEQ V} (p1 p2 : @pred AT AEQ V) := p1 =p=> p2.

Create HintDb okToCancel discriminated.

Hint Extern 0 (okToCancel (?p |-> _) (?p |-> _)) => reflexivity : okToCancel.
Hint Extern 0 (okToCancel ?a ?a) => reflexivity : okToCancel.


Inductive pick {AT AEQ V} (lhs : pred) : list (@pred AT AEQ V) -> list pred -> Prop :=
| PickFirst : forall p ps,
  okToCancel lhs p
  -> pick lhs (p :: ps) ps
| PickLater : forall p ps ps',
  pick lhs ps ps'
  -> pick lhs (p :: ps) (p :: ps').

Lemma pick_later_and : forall AT AEQ V (p : @pred AT AEQ V) p' ps ps' (a b : @pred AT AEQ V),
  pick p ps ps' /\ (a =p=> b)
  -> pick p (p' :: ps) (p' :: ps') /\ (a =p=> b).
Proof.
  intuition; apply PickLater; auto.
Qed.


Ltac pick := solve [ repeat 
          ((apply PickFirst;
            solve [ trivial with okToCancel ]
           ) || apply PickLater) ].


Theorem imply_one : forall AT AEQ V qs qs' (p : @pred AT AEQ V) q ps F,
  pick q qs qs'
  -> (p =p=> q)
  -> (stars ps * F =p=> stars qs')
  -> stars (p :: ps) * F =p=> stars qs.
Proof.
  intros.
  eapply pimpl_trans. eapply pimpl_sep_star. apply stars_prepend. apply pimpl_refl.
  eapply pimpl_trans. apply sep_star_assoc_1.
  eapply pimpl_trans. eapply pimpl_sep_star. eauto. eauto.
  clear dependent ps.
  induction H; intros.
  - rewrite H. apply stars_prepend.
  - eapply pimpl_trans; [|apply stars_prepend].
    eapply pimpl_trans; [|eapply pimpl_sep_star; [apply pimpl_refl|apply IHpick] ].
    eapply pimpl_trans. eapply pimpl_sep_star. eapply pimpl_refl. eapply stars_prepend.
    eapply pimpl_trans; [eapply sep_star_assoc_2|].
    eapply pimpl_trans; [|eapply sep_star_assoc_1].
    eapply pimpl_sep_star. eapply sep_star_comm. eapply pimpl_refl.
Qed.

Theorem cancel_one : forall AT AEQ V qs qs' (p : @pred AT AEQ V) ps F,
  pick p qs qs'
  -> (stars ps * F =p=> stars qs')
  -> stars (p :: ps) * F =p=> stars qs.
Proof.
  intros.
  eapply imply_one; eauto.
Qed.

Ltac cancel_one := eapply cancel_one; [ pick | ].

Theorem delay_one : forall AT AEQ V (p : @pred AT AEQ V) ps q qs,
  (stars ps * stars (p :: qs) =p=> q)
  -> stars (p :: ps) * stars qs =p=> q.
Proof.
  unfold stars; simpl; intros.
  eapply pimpl_trans; [|eauto].
  eapply pimpl_trans. eapply pimpl_sep_star; [|eapply pimpl_refl]. apply stars_prepend.
  eapply pimpl_trans; [|eapply pimpl_sep_star; [apply pimpl_refl|apply stars_prepend] ].
  eapply pimpl_trans; [|eapply sep_star_assoc_1].
  eapply pimpl_sep_star; [|eapply pimpl_refl].
  eapply sep_star_comm.
Qed.

Ltac delay_one := apply delay_one.

Lemma and_imp:
  forall (A B C:Prop),
  (A -> B)
  -> (A /\ C)
  -> (B /\ C).
Proof.
  firstorder.
Qed.

Lemma finish_frame : forall AT AEQ V (p : @pred AT AEQ V),
  stars nil * p =p=> p.
Proof.
  intros. apply star_emp_pimpl.
Qed.

Ltac cancel' := repeat (cancel_one || delay_one);
                try solve [ unfold stars at 2 3; cbv [pred_fold_left fold_left];
                  match goal with
                  | [ |- stars nil * ?P =p=> ?Q] =>
                    match P with
                    | context[sep_star] => match Q with context[sep_star] => fail 2 end
                    | _ => idtac
                    end;
                    simple apply finish_frame
                  end ].

Ltac norml := eapply start_normalizing_left; [ flatten | ].

Ltac normr := eapply start_normalizing_right; [ flatten | ].

Ltac cancel_simpl := simpl.

Ltac norm := cancel_simpl; norml; normr; cancel_simpl.

Ltac inv_option_eq' := repeat match goal with
  | [ H: None = None |- _ ] => clear H
  | [ H: None = Some _ |- _ ] => inversion H
  | [ H: Some _ = None |- _ ] => inversion H
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H
  | [ H: OK _ = OK _ |- _ ] => inversion H; clear H
  | [ H: Err _ = Err _ |- _ ] => inversion H; clear H
  | [ H: OK _ = Err _ |- _ ] => inversion H
  | [ H: Err _ = OK _ |- _ ] => inversion H
  | [ H: (_, _) = (_, _) |- _ ] => inversion H; clear H
  | [ H: isError (OK _) |- _ ] => inversion H
  end.

Ltac inv_option_eq := try ((progress inv_option_eq'); subst; eauto).

Tactic Notation "denote" open_constr(pattern) "as" ident(n) :=
  match goal with | [ H: context [ pattern ] |- _ ] => rename H into n end.

Tactic Notation "denote!" open_constr(pattern) "as" ident(n) :=
  match goal with | [ H: pattern |- _ ] => rename H into n end.

Tactic Notation "substl" :=
  subst; repeat match goal with
  | [ H : ?l = ?r |- _ ] => is_var l;
    match goal with
     | [ |- context [ r ] ] => idtac
     | _ => setoid_rewrite H
    end
  end.

Tactic Notation "substl" constr(term) "at" integer_list(pos) :=
  match goal with
  | [ H : term = _  |- _ ] => setoid_rewrite H at pos
  | [ H : _ = term  |- _ ] => setoid_rewrite <- H at pos
  end.

Tactic Notation "substl" constr(term) :=
  match goal with
  | [ H : term = _  |- _ ] => setoid_rewrite H
  | [ H : _ = term  |- _ ] => setoid_rewrite <- H
  end.

Ltac cancel :=
  intros;
  unfold stars; simpl; try subst;
  norm;
  cancel';
  try congruence;
  unfold stars; simpl;
  try match goal with
  | [ |- emp * _ =p=> _ ] => eapply pimpl_trans; [ apply star_emp_pimpl |]
  end.

Ltac find_cancellable x pred H cont :=
  lazymatch pred with
  | (?a * ?b)%pred =>
    find_cancellable x a H
      ltac:(fun y path => cont y (true ::path)) ||
    find_cancellable x b H
      ltac:(fun y path => cont y (false::path))
  | ?y =>
    assert (okToCancel y x) as H by (trivial with okToCancel);
    cont y (@nil bool)
  end.

Ltac cancel_fast_normr :=
  repeat match goal with
  |- ?pre =p=> ?post =>
    match post with
    | ((?a * ?b) * ?c)%pred =>
      eapply pimpl_trans; [| apply sep_star_assoc_2]
    end
  end.

Ltac apply_pre_path' path :=
  match path with
  | true :: ?tl =>
    eapply pimpl_trans; [ apply sep_star_assoc_1 | ];
    apply_pre_path' tl
  | false :: ?tl =>
    eapply pimpl_trans; [ apply sep_star_shuffle_1 | ];
    apply_pre_path' tl
  | nil => idtac
  end.

Ltac apply_pre_path path :=
  match path with
  | false::?tl => eapply pimpl_trans; [apply sep_star_comm | ];
    apply_pre_path' tl
  | true::?tl =>
    apply_pre_path' tl
  end.

Ltac cancel_one_fast :=
  cancel_fast_normr;
  let H := fresh in
  match goal with
  |- ?pre =p=> ?post =>
    match post with
    | (?a * _)%pred =>
      find_cancellable a pre H ltac:(fun y path =>
        apply_pre_path path;
        apply pimpl_sep_star; [exact H | clear H])
    end
  end.

Ltac cancel_go_fast :=
  simpl; intros;
  repeat (try apply pimpl_refl; cancel_one_fast).

Require Import GoHoare.
Require Import Permutation.
Import Permutation.

Local Open Scope list_scope.
Local Open Scope bool_scope.
Local Open Scope go_scope.

Section GoSepRefl.

  Inductive Var {nlocals} {l : Go.n_tuple nlocals Go.var} :=
  | Arg (a : Go.var)
  | Local (a : nat)
  .

  Variable (nlocals : nat) (locals : Go.n_tuple nlocals Go.var).

  Inductive Pts :=
  | PtsTo (a : @Var _ locals) (t : Go.type) (x : Go.type_denote t)
  | ExPtsTo (a : @Var _ locals) (t : Go.type)
  | DeclsPre (l : list Declaration) (m : nat)
  | DeclsPost (l : list Declaration) (m : nat)
  .

  Inductive Pred :=
  | P (p : Pts)
  | Star: Pred -> Pred -> Pred
  | Emp
  .

  Definition leb_addr (vl vr : @Var _ locals) : bool :=
    match (vl, vr) with
    | (Arg nl, Arg nr) => Nat.leb nl nr
    | (Arg _, _) => true
    | (Local _, Arg _) => false
    | (Local nl, Local nr) => Nat.leb nl nr
    end.

  Definition leb (pl pr : Pts) : bool :=
    match (pl, pr) with
    | (DeclsPre _ _, _) => true
    | (DeclsPost _ _, _) => true
    | (_, DeclsPre _ _) => false
    | (_, DeclsPost _ _) => false
    | (PtsTo a _ _, PtsTo b _ _) => leb_addr a b
    | (PtsTo a _ _, ExPtsTo b _) => leb_addr a b
    | (ExPtsTo a _, PtsTo b _ _) => leb_addr a b
    | (ExPtsTo a _, ExPtsTo b _) => leb_addr a b
    end.

  Definition leb_prop pl pr :=
    if leb pl pr then True else False.

  Definition var_of (a : @Var _ locals) :=
    match a with
    | Arg a => a
    | Local a => nth_var a locals
    end.

  Definition pred_of_pts (p : Pts) : pred :=
    match p with
    | PtsTo a t x => (var_of a |-> Go.Val t x)%pred
    | ExPtsTo a t => (exists x : Go.type_denote t, var_of a |-> Go.Val t x)%pred
    | DeclsPre l m => decls_pre l locals m
    | DeclsPost l m => decls_post l locals m
    end.

  Fixpoint pred_of_star (p : Pred) : pred.
    destruct p eqn:H.
    exact (pred_of_pts p0).
    refine (sep_star _ _).
    exact (pred_of_star p0_1).
    exact (pred_of_star p0_2).
    exact emp.
  Defined.

  Fixpoint list_of (p : Pred) : list Pts := match p with
    | P p0 => p0 :: nil
    | Star p1 p2 => list_of p1 ++ list_of p2
    | Emp => nil
    end.

  Fixpoint pred_of (l : list Pts) :=
    match l with
    | nil => emp
    | a :: l => (pred_of_pts a * (pred_of l))%pred
    end.

  Definition var_eq (a b : @Var _ locals) : bool.
    destruct a eqn:H, b eqn:H'.
    exact (Nat.eqb a0 a1).
    exact false.
    exact false.
    exact (Nat.eqb a0 a1).
  Defined.

  Definition cancels (l r : Pts) : bool.
    refine (match (l, r) with
    | (ExPtsTo a1 t1, ExPtsTo a2 t2) =>
      (if var_eq a1 a2 then (if Go.type_eq_dec t1 t2 then true else false) else false)
    | (PtsTo a1 t1 v1, ExPtsTo a2 t2) =>
      (if var_eq a1 a2 then (if Go.type_eq_dec t1 t2 then true else false) else false)
    | _ => false
    end).
  Defined.

  Fixpoint cancel_some (l r : list Pts) : (list Pts * list Pts)%type :=
    match l with
    | nil => (nil, r)
    | x :: l =>
      match r with
      | nil => (x :: l, nil)
      | y :: r =>
        let lr := cancel_some l r in
        if cancels x y then lr
        else (x :: fst lr, y :: snd lr)
      end
    end.

  Lemma list_of_app : forall l1 l2, pred_of l1 * pred_of l2 <=p=> pred_of (l1 ++ l2).
  Proof.
    induction l1; cbn; intros.
    rewrite <- ?emp_star; auto.
    rewrite sep_star_assoc.
    split; apply pimpl_sep_star; solve [auto | apply IHl1].
  Qed.

  Fact pred_of_list_of : forall l, pred_of (list_of l) <=p=> pred_of_star l.
  Proof.
    induction l; simpl; auto.
    rewrite sep_star_comm, <- emp_star. auto.
    rewrite <- list_of_app.
    split; eapply pimpl_sep_star; solve [apply IHl1 | apply IHl2].
  Qed.

  Lemma list_of_correct : forall l r, pred_of (list_of l) =p=> pred_of (list_of r) -> pred_of_star l =p=> pred_of_star r.
  Proof.
    intros.
    repeat rewrite pred_of_list_of in H.
    auto.
  Qed.

  Lemma pred_of_permutation : forall l1 l2, Permutation l1 l2 -> pred_of l2 =p=> pred_of l1.
  Proof.
    intros.
    induction H; eauto; cbn.
    eapply pimpl_sep_star; eauto.
    repeat rewrite <- sep_star_assoc.
    eapply pimpl_sep_star; eauto.
    eapply sep_star_comm.
  Qed.

  Fact var_eq_eq : forall a b, var_eq a b = true -> a = b.
  Proof.
    destruct a, b; cbn; intros; try congruence.
    all : eapply EqNat.beq_nat_true in H; congruence.
  Qed.

  Lemma cancels_valid : forall p q, cancels p q = true -> pred_of_pts p =p=> pred_of_pts q.
  Proof.
    unfold cancels. intros.
    repeat break_match; try congruence; subst; cbn.
    apply var_eq_eq in Heqb. subst.
    do 2 intro.
    eexists. apply H0.
    apply var_eq_eq in Heqb. subst.
    reflexivity.
  Qed.

  Lemma cancel_decls_pre_post : forall (l : list Declaration) (l1 l2 : list Pts) m,
    pred_of l1 =p=> pred_of l2 ->
    pred_of (DeclsPre l m :: l1) =p=> pred_of (DeclsPost l m :: l2).
  Proof.
    cbn. intros.
    apply pimpl_sep_star; auto.
  Qed.

   Lemma cancel_some_nil_r : forall l,
    cancel_some l nil = (l, nil).
  Proof.
    induction l; cbn; congruence.
  Qed.

  Theorem cancel_some_valid : forall l r,
    let lr' := (cancel_some l r) in
    fst lr' = snd lr' ->
    pred_of l =p=> pred_of r.
  Proof.
    induction l; cbn -[cancels];
      intros; subst; auto.
    break_match; simpl in *.
    - congruence.
    - repeat break_match; try congruence; simpl in *.
      find_eapply_lem_hyp cancels_valid.
      cancel. eauto.
      find_inversion. cancel. eauto.
  Qed.

  Section PredSort.
    Fixpoint insert (p : Pts) (l : list Pts) : list Pts.
      destruct l.
      exact (p::nil).
      refine (if leb p p0 then p :: p0 :: l else p0 :: insert p l).
    Defined.

    Lemma insert_permutation : forall x l, Permutation.Permutation (x :: l) (insert x l).
    Proof.
      induction l; simpl; auto.
      destruct leb; auto.
      eauto using perm_trans, perm_swap.
    Qed.

    (* dumb n^2 insertion sort *)
    Definition sort (l : list Pts) : list Pts :=
      List.fold_right insert nil l.

    Theorem sort_permutation : forall l, Permutation.Permutation (sort l) l.
    Proof.
      induction l; simpl; auto.
      eauto using insert_permutation, perm_trans, Permutation_sym.
    Qed.
  End PredSort.

  Theorem sep_star_sort : forall l r,
      pred_of (sort (list_of l)) =p=> pred_of (sort (list_of r)) ->
      pred_of_star l =p=> pred_of_star r.
  Proof.
    intros.
    apply list_of_correct.
    eapply pimpl_trans.
    eapply pred_of_permutation.
    eapply sort_permutation.
    eapply pimpl_trans.
    eapply H.
    eapply pred_of_permutation.
    symmetry.
    eapply sort_permutation.
  Qed.
End GoSepRefl.

Import Go.

Ltac get_locals :=
  match goal with
  |- ?a =p=> ?b =>
    match a with
    | context [ @nth_var ?nlocals _ ?locals ] =>
      constr:(pair nlocals locals)
    | context [ @decls_pre _ ?nlocals ?locals] =>
      constr:(pair nlocals locals)
    | context [ @decls_post _ ?nlocals ?locals] =>
      constr:(pair nlocals locals)
    | _ => constr:(pair 0 tt)
    end
  end.

Ltac transform_addr nlocals locals x :=
  lazymatch x with
  | nth_var ?a ?vars => constr:(@Local nlocals locals a)
  | ?x => constr:(@Arg nlocals locals x)
  end.

Ltac transform_pred nlocals locals p :=
  lazymatch p with
  | sep_star ?a ?b =>
    let a' := transform_pred nlocals locals a in
    let b' := transform_pred nlocals locals b in
    constr:(Star a' b')
  | (exists x, ?a |-> Val ?t x)%pred =>
    let a' := transform_addr nlocals locals a in
    constr:(P (@ExPtsTo nlocals locals a' t))
  | (?a |-> Val ?t ?x)%pred =>
    let a' := transform_addr nlocals locals a in
    constr:(P (@PtsTo nlocals locals a' t x))
  | emp => constr:(@Emp nlocals locals)
  | decls_pre ?decls ?vars ?m =>
    constr:(P (@DeclsPre _ vars decls m))
  | decls_post ?decls ?vars ?m =>
    constr:(P (@DeclsPost _ vars decls m))
  end.

Ltac transform_pimpl_refl :=
  match get_locals with
  | (?nlocals, ?locals) =>
    match goal with |- ?pre =p=> ?post =>
      let pre' := transform_pred nlocals locals pre in
      let post' := transform_pred nlocals locals post in
      change pre with (pred_of_star pre');
      change post with (pred_of_star post')
    end
  end.

Lemma type_eq_dec_refl : forall t, (if type_eq_dec t t then true else false) = true.
Proof.
  induction t; try reflexivity; cbn; intros.
  all : destruct sumbool_rec; try congruence.
Qed.

Ltac cancel_refl :=
  transform_pimpl_refl;
  apply sep_star_sort;
  cbv [sort fold_right insert leb leb_addr list_of app Nat.leb];
  try apply cancel_decls_pre_post;
  apply cancel_some_valid;
  repeat match goal with (* Not actually necessary for any goals I've encountered *)
         | |- context[PtsTo ?var ?t ?val] => (is_var val; fail 1)
                                           ||
                                           let V := fresh "val" in
                                           pose (V := val); change val with V
         end;
  cbv [cancel_some remove cancels var_eq Nat.eqb type_eq_dec False_ind sumbool_rec sumbool_rect
       list_rec list_rect eq_ind_r eq_ind eq_rect eq_rec type_rec type_rect Datatypes.length fst snd];
  solve [
    reflexivity |
    unfold cancels;
      repeat (try reflexivity; rewrite type_eq_dec_refl; simpl)
  ].

Example cancel_refl_one : forall v1 v2,
  (@ptsto _ Nat.eq_dec _ 0 (Val Bool v1) * 1 |-> Val Num v2 * (exists x, 2 |-> Val Num x)) =p=>
  (exists x, 1 |-> Val Num x) * 0 |-> Val Bool v1 * (exists x, 2 |-> Val Num x).
Proof.
  intros.
  cancel_refl.
Qed.

Example cancel_refl_locals : forall n (l : n_tuple n var),
  @ptsto _ Nat.eq_dec _ (nth_var 1 l) (Val Num 45) =p=> exists x, nth_var 1 l |-> Val Num x.
Proof.
  intros.
  cancel_refl.
Qed.

Example cancel_refl_decls : forall n (locals : n_tuple n var) l v1 v2,
  (@ptsto _ Nat.eq_dec _ 4 (Val Bool v1) * decls_pre l locals n * 1 |-> Val Num v2 * (exists x, 2 |-> Val Num x)) =p=>
  (exists x, 1 |-> Val Num x) * 4 |-> Val Bool v1 * (exists x, 2 |-> Val Num x) * decls_post l locals n.
Proof.
  intros.
  cancel_refl.
Qed.

Ltac get_list_of_preds stars :=
  lazymatch stars with
  | ((?a * ?b)%pred) =>
    let ll := get_list_of_preds a in
    let lr := get_list_of_preds b in
    constr:(List.app ll lr)
  | ?a => constr:(a :: nil)
end.

Ltac find_missing_preds pleft pright cont :=
  lazymatch pleft with
  | ((?a * ?b)%pred) =>
    find_missing_preds a pright
      ltac:(fun ll => find_missing_preds b pright
        ltac:(fun lr =>
          let l := constr:(List.app ll lr) in
          cont l
        )
      )
  | decls_pre ?l ?a ?b =>
    lazymatch pright with
    | context [decls_pre ?l] =>
      let l := constr:(@nil pred) in cont l
    | context [decls_post ?l] =>
      let l := constr:(@nil pred) in cont l
    | _ =>
      let l := constr:(decls_pre l a b :: nil) in cont l
    end
  | decls_post ?l ?a ?b =>
    lazymatch pright with
    | context [decls_pre ?l] =>
      let l := constr:(@nil pred) in cont l
    | context [decls_post ?l] =>
      let l := constr:(@nil pred) in cont l
    | _ =>
      let l := constr:(decls_pre l a b :: nil) in cont l
    end
  | context [ptsto ?a] =>
    match pright with
    | context [ptsto ?b] =>
      unify a b;
      let l := constr:(@nil pred) in cont l
    | _ =>
      let l := constr:(pleft :: nil) in cont l
    end
  | emp => let l := constr:(@nil pred) in cont l
  end.

Ltac star_of_preds preds :=
  match preds with
  | nil => constr:(emp)
  | ?a :: nil => a
  | ?a :: ?b :: ?l =>
    let preds' := constr:(b :: l) in
    let r := star_of_preds preds' in
    constr:(sep_star r a)
  end.

Ltac instantiate_frame F preds :=
  let star := star_of_preds preds in
  unify F star.

Ltac find_frame p cont :=
  match p with
  | (?a * ?b)%pred =>
    find_frame a cont;
    find_frame b cont
  | ?y => is_evar y; cont y
  | _ => idtac
  end.

Ltac norm_refl :=
  simpl decls_pre; simpl decls_post; simpl args_pre; simpl args_post; simpl retargs_pre; simpl retargs_post;
  match goal with
  |- ?a =p=> ?b =>
    (find_missing_preds a b ltac:(fun missing' =>
      let missing := eval simpl app in missing' in
      find_frame b ltac:(fun F =>
        instantiate_frame F missing
    )) || find_missing_preds b a ltac:(fun missing' =>
      let missing := eval simpl app in missing' in
      find_frame a ltac:(fun F =>
        instantiate_frame F missing
    )))
  end;
  unfold wrap, moved_value, default_value; cancel_simpl.


Example cancel_refl_frame : forall n (locals : n_tuple n var) l v1 v2, exists F,
  (@ptsto _ Nat.eq_dec _ 4 (Val Bool v1) * decls_pre l locals n * 1 |-> Val Num v2 * (exists x, 2 |-> Val Num x)
   * (exists x, 3 |-> Val Num x)) =p=>
  (exists x, 1 |-> Val Num x) * 4 |-> Val Bool v1 * (exists x, 2 |-> Val Num x) * F.
Proof.
  intros. eexists.
  norm_refl.
  cancel_refl.
Qed.

Ltac cancel_go_refl :=
  intros **; cbv beta; norm_refl;
  (* generalize decls so we can use abstract *)
  match goal with
  |- context [decls_pre ?decls] => generalize dependent decls; intros
  end;
  abstract cancel_refl.
