Require Import Eqdep.

Ltac safe_intuition :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         | _ => progress subst
         end.

Ltac deex :=
  match goal with
  | [ H : exists (varname : _), _ |- _ ] =>
    let newvar := fresh varname in
    destruct H as [newvar ?]; safe_intuition
  end.

Ltac simpl_match :=
  let repl_match_goal d d' :=
      replace d with d';
      lazymatch goal with
      | [ |- context[match d' with _ => _ end] ] => fail
      | _ => idtac
      end in
  let repl_match_hyp H d d' :=
      replace d with d' in H;
      lazymatch type of H with
      | context[match d' with _ => _ end] => fail
      | _ => idtac
      end in
  match goal with
  | [ Heq: ?d = ?d' |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d' = ?d |- context[match ?d with _ => _ end] ] =>
    repl_match_goal d d'
  | [ Heq: ?d = ?d', H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  | [ Heq: ?d' = ?d, H: context[match ?d with _ => _ end] |- _ ] =>
    repl_match_hyp H d d'
  end.

Ltac destruct_matches_in e :=
  lazymatch e with
  | context[match ?d with | _ => _ end] =>
    destruct_matches_in d
  | _ => destruct e eqn:?; intros
  end.

Ltac destruct_all_matches :=
  repeat (try match goal with
              | [ |- context[match ?d with | _ => _ end] ] =>
                destruct_matches_in d
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_nongoal_matches :=
  repeat (try simpl_match;
          try match goal with
              | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                destruct_matches_in d
              end);
  subst;
  try congruence;
  auto.

Ltac destruct_goal_matches :=
  repeat (try simpl_match;
           match goal with
           | [ |- context[match ?d with | _ => _ end] ] =>
              destruct_matches_in d
           end);
  try congruence;
  auto.

Ltac inj_pair2 :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply inj_pair2 in H; subst
  end.

Lemma exists_tuple : forall A B P,
    (exists a b, P (a, b)) ->
    exists (a: A * B), P a.
Proof.
  intros.
  repeat deex; eauto.
Qed.

Ltac descend :=
  repeat match goal with
         | [ |- exists (_:unit), _ ] => exists tt
         | [ |- exists (_: _ * _), _ ] => apply exists_tuple
         | [ |- exists _, _ ] => eexists
         end.

Inductive Learnt {P:Prop} :=
| AlreadyLearnt (H:P).

Ltac learn_fact H :=
  let P := type of H in
  let P := eval simpl in P in
  lazymatch goal with
    (* matching the type of H with the Learnt hypotheses means the
    learning fails even when the proposition is known by a different
    but unifiable type term *)
  | [ Hlearnt: @Learnt P |- _ ] =>
    fail 0 "already knew" P "through" Hlearnt
  | _ => pose proof (H:P); pose proof (@AlreadyLearnt P H)
  end.

Tactic Notation "learn" "that" constr(H) := learn_fact H.