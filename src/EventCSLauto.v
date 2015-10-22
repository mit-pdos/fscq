Require Import EventCSL.

Ltac inv_opt :=
  match goal with
  | [ H: None = Some _ |- _ ] =>
    now (inversion H)
  | [ H: Some _ = None |- _ ] =>
    now (inversion H)
  | [ H: Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [ H: None = None |- _ ] =>
    clear H
  end.

Ltac econtradiction H :=
  exfalso; eapply H.

(* extract the precondition of a valid statement into the hypotheses *)
Ltac intros_pre :=
  unfold valid at 1; unfold pred_in; intros;
  repeat deex.

Ltac destruct_ands :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         end.

Ltac split_ands :=
  destruct_ands; repeat (split; intros).

(* simplify the postcondition obligation to its components *)
Ltac simpl_post :=
  cbn; unfold pred_in;
  split_ands;
  repeat deex.

Ltac next_control_step :=
  eapply pimpl_ok; [ now auto with prog | ].

Ltac head_symbol e :=
  lazymatch e with
  | ?h _ _ _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ => h
  | ?h _ _ _ _ => h
  | ?h _ _ _ => h
  | ?h _ _ => h
  | ?h _ => h
  | ?h => h
  end.

Ltac unfold_prog :=
  lazymatch goal with
  | [ |- valid _ _ _ _ _ _ ?p ] =>
    let program := head_symbol p in
    unfold program
  end.

Ltac step' simplifier finisher :=
  repeat (autounfold with prog);
  next_control_step ||
                    (unfold_prog; next_control_step);
  repeat (autounfold with prog);
  simplifier;
  finisher.

Ltac unfold_pred_applications :=
  unfold pred_in; intros; repeat deex.

Ltac step_simplifier :=
  unfold_pred_applications;
  simpl_post;
  try subst.

Ltac simpl_goal :=
  repeat match goal with
         | [ |- exists _, _ ] => eexists
         | [ |- _ /\ _ ] => split
         | [ |- forall _, _ ] => intros
         end.

Ltac step_finisher :=
  simpl_goal;
  try solve [ pred_apply; cancel ];
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