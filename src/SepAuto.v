Require Import Arith.
Require Import Omega.
Require Import List.
Require Import Prog.
Require Import Pred.
Require Import Hoare.

Set Implicit Arguments.


(** * Separation logic proof automation *)

Ltac intu' :=
  match goal with
  | [ H : ex _ |- _ ] => destruct H
  | [ |- ex _ ] => eexists
  end.

Ltac intu := intuition; repeat (intu'; intuition).

Ltac pintu := unfold lift, (* lift_empty, *) and, or, pimpl, impl; intu.

Definition stars (ps : list pred) :=
  fold_left sep_star ps emp.

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

Theorem restart_canceling:
  forall p q,
  (stars p * stars nil ==> stars q) ->
  (stars nil * stars p ==> stars q).
Proof.
  intros; eapply pimpl_trans; [ eapply sep_star_comm | eauto ].
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

Lemma stars_prepend':
  forall l x,
  fold_left sep_star l x <==> x * fold_left sep_star l emp.
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
  forall l x,
  stars (x :: l) <==> x * stars l.
Proof.
  unfold stars; simpl; intros.
  eapply piff_trans. apply stars_prepend'.
  eapply piff_trans. apply sep_star_assoc.
  apply piff_comm. apply emp_star.
Qed.

Lemma flatten_star : forall PT QT p q ps qs P Q,
  p <==> (exists (x:PT), stars (ps x) * [[P x]])%pred
  -> q <==> (exists (x:QT), stars (qs x) * [[Q x]])%pred
  -> p * q <==> exists (x:PT*QT), stars (ps (fst x) ++ qs (snd x)) * [[P (fst x) /\ Q (snd x)]].
Proof.
(*
  intros.
  eapply piff_trans.
  eapply piff_star_r with (b:=stars ps); eauto.
  eapply piff_trans.
  eapply piff_star_l with (b:=stars qs); eauto.
  clear H H0.
  induction ps.
  - simpl.
    eapply piff_trans.
    eapply piff_comm.
    eapply emp_star.
    apply piff_refl.
  - eapply piff_comm.
    eapply piff_trans.
    eapply stars_prepend.
    eapply piff_trans.
    eapply piff_star_l.
    eapply piff_comm.
    eapply IHps.
    eapply piff_trans.
    eapply piff_comm.
    eapply sep_star_assoc.
    apply piff_star_r.
    eapply piff_comm.
    eapply piff_trans.
    eapply stars_prepend.
    apply piff_star_r.
    apply piff_refl.
Qed.
*)
Admitted.

Ltac flatten := repeat match goal with
                       | [ |- emp <==> _ ] => apply flatten_emp
                       | [ |- _ * _ <==> _ ] => eapply flatten_star
                       | _ => apply flatten_default
                       end.

Definition okToUnify (p1 p2 : pred) := p1 = p2.

Hint Extern 1 (okToUnify (?p |-> _) (?p |-> _)) => constructor : okToUnify.
Hint Extern 1 (okToUnify ?a ?a) => constructor : okToUnify.

Inductive pick (lhs : pred) : list pred -> list pred -> Prop :=
| PickFirst : forall p ps,
  okToUnify lhs p
  -> pick lhs (p :: ps) ps
| PickLater : forall p ps ps',
  pick lhs ps ps'
  -> pick lhs (p :: ps) (p :: ps').

Ltac pick := solve [ repeat ((apply PickFirst; solve [ auto with okToUnify ])
                               || apply PickLater) ].

Theorem imply_one : forall qs qs' p p' ps F,
  (pick p qs qs' /\ (p' ==> p))
  -> (stars ps * F ==> stars qs')
  -> stars (p' :: ps) * F ==> stars qs.
Proof.
  intros. destruct H.
  eapply pimpl_trans. eapply pimpl_sep_star. apply stars_prepend. apply pimpl_refl.
  eapply pimpl_trans. apply sep_star_assoc_1.
  eapply pimpl_trans. eapply pimpl_sep_star. eauto. eauto.
  clear dependent ps.
  induction H; intros.
  - inversion H; subst. apply stars_prepend.
  - eapply pimpl_trans; [|apply stars_prepend].
    eapply pimpl_trans; [|eapply pimpl_sep_star; [apply pimpl_refl|apply IHpick] ].
    eapply pimpl_trans. eapply pimpl_sep_star. eapply pimpl_refl. eapply stars_prepend.
    eapply pimpl_trans; [eapply sep_star_assoc_2|].
    eapply pimpl_trans; [|eapply sep_star_assoc_1].
    eapply pimpl_sep_star. eapply sep_star_comm. eapply pimpl_refl.
Qed.

Theorem cancel_one : forall qs qs' p ps F,
  pick p qs qs'
  -> (stars ps * F ==> stars qs')
  -> stars (p :: ps) * F ==> stars qs.
Proof.
  intros.
  eapply imply_one; eauto.
Qed.

Ltac cancel_one := eapply cancel_one; [ pick | ].

Theorem delay_one : forall p ps q qs,
  (stars ps * stars (p :: qs) ==> q)
  -> stars (p :: ps) * stars qs ==> q.
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

Ltac pick_imply :=
  solve [ repeat (solve [ split; [ apply PickFirst; unfold okToUnify; auto | pintu ] ]
                  || (eapply and_imp; [apply PickLater|]) ) ].
Ltac imply_one := eapply imply_one ; [ pick_imply | ].

Lemma finish_lift_one:
  forall p q,
  (stars nil * stars q ==> stars nil) ->
  (stars nil * stars ([[p]] :: q) ==> stars nil).
Proof.
  intros.
  eapply pimpl_trans. apply pimpl_sep_star. apply pimpl_refl. apply stars_prepend.
  eapply pimpl_trans. apply sep_star_assoc.
  eapply pimpl_trans. apply pimpl_sep_star. apply sep_star_comm. apply pimpl_refl.
  eapply pimpl_trans. apply sep_star_assoc.
  apply sep_star_lift_l. eauto.
Qed.

Ltac finish_lift_one := apply finish_lift_one.

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
               eapply restart_canceling;
               repeat (imply_one || delay_one);
               repeat finish_lift_one;
               try (apply finish_frame || apply finish_easier).

(* Logic for normalizing a chain of [sep_star]s:
 * - Turn exists in the premise into forall.
 * - Turn exists in the conclusion into existential variables.
 * - Turn lift_empty in the premise into hypotheses.
 * - Turn lift_empty in the conclusion into separate subgoals.
 *)
Lemma add_stars_nil:
  forall p,
  stars p <==> stars p * stars nil.
Proof.
  intros. eapply piff_trans; [ | apply sep_star_comm ].
  eapply piff_trans. apply emp_star. firstorder.
Qed.

Lemma stars_skip_r : forall p ps qs,
  stars ps * stars (p :: qs) ==> stars (p :: ps) * stars qs.
Proof.
  intros.
  eapply pimpl_trans. eapply pimpl_sep_star; [ apply pimpl_refl | apply stars_prepend ].
  eapply pimpl_trans; [|eapply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ] ].
  eapply pimpl_trans. apply sep_star_assoc_2.
  eapply pimpl_sep_star; [|eapply pimpl_refl].
  eapply sep_star_comm.
Qed.

Lemma stars_skip_l : forall p ps qs,
  stars (p :: ps) * stars qs ==> stars ps * stars (p :: qs).
Proof.
  intros.
  eapply pimpl_trans. eapply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ].
  eapply pimpl_trans; [|eapply pimpl_sep_star; [ apply pimpl_refl | apply stars_prepend ] ].
  eapply pimpl_trans; [|apply sep_star_assoc_1].
  eapply pimpl_sep_star; [|eapply pimpl_refl].
  eapply sep_star_comm.
Qed.

(* Left-side normalization *)

Ltac kill_emp_l :=
  eapply pimpl_trans; [ apply star_emp_pimpl
                        || (eapply pimpl_trans;
                            [ apply sep_star_comm | apply star_emp_pimpl ]) |].
Ltac kill_emps_l :=
  kill_emp_l;
  ( kill_emp_l ||
    ( repeat ( eapply pimpl_trans; [ apply sep_star_assoc_1 |] );
      kill_emp_l;
      repeat ( eapply pimpl_trans; [ apply sep_star_assoc_2 |] ) ) ).

Ltac deex_stars_l_one :=
  (* Avoid destructing "exists" in an existential variable at the head of stars.. *)
  match goal with
  | [ |- (stars ((exists _, _) :: _) * stars _ ==> _)%pred ] => idtac
  | _ => fail
  end;
  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ] | ];
  eapply pimpl_trans; [ apply sep_star_assoc_1 | ];
  (* Get rid of "exists" on the left side of pimpl *)
  eapply pimpl_exists_l_star; apply pimpl_exists_l; intros;
  (* Get rid of potential leftover dummy fun's; might be worth making this a separate pass *)
  try ( eapply pimpl_trans; [ apply pimpl_sep_star; [ apply pimpl_fun_l | apply pimpl_refl ] | ] );
  eapply pimpl_trans; [ apply sep_star_assoc_2 | ];
  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ] | ].

Ltac delift_stars_l_one :=
  (* Avoid destructing "lift_empty" in an existential variable at the head of stars.. *)
  match goal with
  | [ |- (stars ([[_]] :: _) * stars _ ==> _)%pred ] => idtac
  | _ => fail
  end;
  eapply pimpl_trans; [ apply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ] | ];
  eapply pimpl_trans; [ apply sep_star_assoc_1 | ];
  eapply sep_star_lift_l; intros.

Ltac normalize_stars_l_skip :=
  eapply pimpl_trans; [ apply stars_skip_l | ].

Ltac deex_l :=
  match goal with
  | [ |- (exists _, _) ==> _ ] => apply pimpl_exists_l; intro
  end.

Ltac normalize_stars_l :=
  repeat deex_l;
  eapply piff_l; [flatten|];
  unfold app; simpl;
  eapply piff_l; [apply add_stars_nil|];
  repeat (deex_stars_l_one || delift_stars_l_one || normalize_stars_l_skip );
  unfold stars; simpl; kill_emps_l.

(* Right-side normalization *)

Ltac kill_emp_r :=
  eapply pimpl_trans; [| apply pimpl_star_emp
                         || (eapply pimpl_trans;
                             [ apply pimpl_star_emp | apply sep_star_comm ]) ].
Ltac kill_emps_r :=
  kill_emp_r;
  ( kill_emp_r ||
    ( repeat ( eapply pimpl_trans; [| apply sep_star_assoc_2 ] );
      kill_emp_r;
      repeat ( eapply pimpl_trans; [| apply sep_star_assoc_1 ] ) ) ).

Ltac deex_stars_r_one :=
  (* Avoid destructing "exists" in an existential variable at the head of stars.. *)
  match goal with
  | [ |- _ ==> (stars (exis _ :: _) * stars _)%pred ] => idtac
  | _ => fail
  end;
  eapply pimpl_trans; [| apply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ] ];
  eapply pimpl_trans; [| apply sep_star_assoc_2 ];
  eapply pimpl_trans; [| exact (@pimpl_exists_r_star _ _ _) ];
  eapply pimpl_exists_r; eexists;
  eapply pimpl_trans; [| apply sep_star_assoc_1 ];
  eapply pimpl_trans; [| apply pimpl_sep_star; [ apply stars_prepend | apply pimpl_refl ] ].

Ltac normalize_stars_r_skip :=
  eapply pimpl_trans; [ | apply stars_skip_r ].

Ltac deex_r :=
  match goal with
  | [ |- _ ==> exists _, _ ] => apply pimpl_exists_r; eexists
  end.

Ltac normalize_stars_r :=
  repeat deex_r;
  eapply piff_r; [flatten|];
  unfold app; simpl;
  eapply piff_r; [apply add_stars_nil|];
  repeat ( deex_stars_r_one || normalize_stars_r_skip );
  unfold stars; simpl; kill_emps_r.

(* Split and-like lifted conditions.  We assume they appear at the right of the
 * preconditions -- e.g., foo * bar * [[baz]] * [[quux]].  We use sep_star for
 * these conditions (instead of "and") because that makes them easier to handle
 * when they show up on the left-hand side (in assumptions).
 *)

Ltac split_trailing_lift_one :=
  match goal with
  | [ |- _ ==> _ * [[_]] ] =>
    eapply pimpl_trans; [ apply sep_star_lift_r | apply sep_star_comm ]; apply pimpl_and_split
  end.

Ltac split_trailing_lifts :=
  repeat deex_r;
  repeat split_trailing_lift_one.

Ltac sep := sep_imply; cancel.

Ltac step' t := intros;
             ((eapply pimpl_ok; [ solve [ eauto with prog ] | t ])
                || (eapply pimpl_ok_cont; [ solve [ eauto with prog ] | t | t ]));
             try solve [ intuition sep ]; (unfold stars; simpl);
             try omega.

(* XXX npintu: handle everything on the left first, including ORs, which pintu does now.. *)

Ltac npintu := normalize_stars_l; split_trailing_lifts; normalize_stars_r; pintu.

Ltac trysep := sep_imply; cancel; unfold stars; simpl; npintu.

Ltac step := step' npintu.

Ltac hoare := repeat step.
