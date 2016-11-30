Inductive Learnt {P:Prop} :=
| AlreadyLearnt (H:P).

Ltac add_learnt H :=
  let P := type of H in
  let P := eval simpl in P in
      pose proof (@AlreadyLearnt P H).

Ltac check_consistency :=
  try lazymatch goal with
  | [ H: @Learnt ?P, H': @Learnt ?P |- _ ] =>
    fail 10 "learnt" P "twice:" H H'
  end.

Local Ltac learn_tac H t :=
  let H' := fresh in
  let P := type of H in
  let P := eval simpl in P in
  pose proof (H:P) as H';
    t;
    lazymatch goal with
      | [ Hlearnt: @Learnt P |- _ ] =>
        fail 0 "already knew" P "through" Hlearnt
      | _ => pose proof (@AlreadyLearnt P H)
    end.

Local Ltac learn_fact H :=
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

Ltac is_not_learnt H :=
  lazymatch type of H with
  | Learnt => fail
  | _ => idtac
  end.

Ltac not_learnt P :=
  let P := eval simpl in P in
  lazymatch goal with
  | [ H: @Learnt P |- _ ] => fail
  | _ => idtac
  end.

Tactic Notation "learn" hyp(H) tactic(t) := learn_tac H t.
Tactic Notation "learn" "that" constr(H) := learn_fact H.
Tactic Notation "learn" "that" "simpl" constr(H) :=
  learn_fact constr:(ltac:(let P := type of H in
                           let P := eval simpl in P in
                               exact (H:P))).


Module LearnExample.

  Parameter P : nat -> Prop.
  Parameter Q R : nat -> nat -> Prop.

  Axiom P_Q : forall {x}, P x -> exists y, Q x y.
  Axiom Q_R : forall {x y}, P x -> Q x y -> R y x.

  Goal forall x, P x -> exists y, R y x.
  Proof.
    repeat match goal with
           | _ => progress intros
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: P _ |- _ ] => learn that (P_Q H)
           | [ H: P ?x, H': Q ?x _ |- _ ] => learn that (Q_R H H')
           | [ |- exists _, _ ] => eexists
           | _ => eassumption
           end.
  Qed.

  Goal forall x, P x -> exists y, R y x.
  Proof.
    repeat match goal with
           | _ => progress intros
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: P _ |- _ ] => learn H (apply P_Q in H)
           | [ H: P ?x, H': Q ?x _ |- _ ] => learn H (apply Q_R in H'; trivial)
           | [ |- exists _, _ ] => eexists
           | _ => eassumption
           end.
  Qed.

  Goal forall x, P x -> exists y, R y x.
  Proof.
    repeat match goal with
           | _ => progress intros
           | [ H: _ /\ _ |- _ ] => destruct H
           | [ H: exists _, _ |- _ ] => destruct H
           | [ H: P _ |- _ ] => learn H (apply P_Q in H)
           | [ H: P ?x, H': Q ?x _ |- _ ] => learn that simpl (Q_R H H')
           | [ |- exists _, _ ] => eexists
           | _ => eassumption
           end.
  Qed.
End LearnExample.

Ltac complete_mem_equalities :=
  try match goal with
  | [ H: ?vd ?a = Some ?vs, H': ?vd ?a = _ |- _ ] =>
    learn H' rewrite H in H'
  | [ H: ?vd ?a = Some ?vs, H': _ = ?vd ?a |- _ ] =>
    learn H' rewrite H in H'
  end.