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

Ltac inj_pair2 :=
  match goal with
  | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
    apply inj_pair2 in H; subst
  end.

(* BUG: Coq doesn't accept this, complaining that n is not in scope, but it
works perfectly well within a proof script (and correctly bind n,m to the names
used in the pattern match) *)
(* Ltac break_tuple :=
  repeat match goal with
         | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
           let n := fresh n in
           let m := fresh m in
           destruct a as [n m]
         end. *)

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

Lemma exists_tuple : forall A B P,
    (exists a b, P (a, b)) ->
    exists (a: A * B), P a.
Proof.
  intros.
  repeat deex; eauto.
Qed.

Ltac descend :=
  repeat match goal with
         | [ |- exists (_: _ * _), _ ] => apply exists_tuple
         | [ |- exists _, _ ] => eexists
         end.
