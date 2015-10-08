Require Import EventCSL.

Ltac inv_opt :=
  match goal with
  | [ H: @eq (option _) _ _ |- _ ] =>
    inversion H; clear H; subst
  end.

Ltac econtradiction H :=
  exfalso; eapply H.

(* extract the precondition of a valid statement into the hypotheses *)
Ltac intros_pre :=
  unfold valid at 1; unfold pred_in; intros;
  repeat deex.

(* simplify the postcondition obligation to its components *)
Ltac simpl_post :=
  cbn; unfold pred_in;
  (* the intention here is to unfold /\'s and instantiate existentials
     before creating evars; something that just broke conjunctions would
     be better than [intuition]. *)
  intuition; repeat deex;
  repeat match goal with
         | [ |- exists _, _ ] =>
           eexists
         end; intuition.

Ltac step' simplifier finisher :=
  repeat (autounfold with prog);
  eapply pimpl_ok; [ now auto with prog | ];
  repeat (autounfold with prog);
  simplifier;
  finisher.

(* combinator to apply t in applied predicates *)
Ltac t_in_applied t :=
  match goal with
  | [ H: ?F _ |- _ ] =>
    match type of F with
    | pred => t H
    end
  end.

Ltac lift_this H :=
  match type of H with
  | context[lift_empty _] =>
    destruct_lift H
  end.

Ltac lift_all := repeat (t_in_applied lift_this).

Ltac unfold_pred_applications :=
  unfold pred_in; intros; repeat deex.

Ltac step_simplifier :=
  unfold_pred_applications;
  lift_all;
  simpl_post;
  try subst.

Ltac step_finisher := try (pred_apply; cancel);
    eauto.

Tactic Notation "step" := step' step_simplifier step_finisher.
Tactic Notation "step" "pre" tactic(simplifier) := step' simplifier step_finisher.
Tactic Notation "step" "pre" tactic(simplifier) "with" tactic(finisher) := step' simplifier finisher.
Tactic Notation "step" "with" tactic(finisher) := step' step_simplifier finisher.

Ltac hoare' simplifier finisher  := intros; repeat step' simplifier finisher.
Tactic Notation "hoare" := hoare' step_simplifier step_finisher.
Tactic Notation "hoare" "pre" tactic(simplifier) := hoare' simplifier step_finisher.
Tactic Notation "hoare" "pre" tactic(simplifier) "with" tactic(finisher) := hoare' simplifier finisher.
Tactic Notation "hoare" "with" tactic(finisher) := hoare' step_simplifier finisher.