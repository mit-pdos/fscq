Ltac learn_tac H t :=
  let H' := fresh in
  pose proof H as H';
    t;
    lazymatch type of H with
    | ?t =>
      try lazymatch goal with
        | [ Hcopy: t, H: t |- _ ] =>
          fail 1 "already know that"
        end
    end.

Ltac learn_fact H :=
  match type of H with
    | ?t =>
      match goal with
      | [ H': t |- _ ] =>
        fail 2 "already knew that" H'
      | _ => pose proof H
      end
  end.

Tactic Notation "learn" hyp(H) tactic(t) := learn_tac H t.

Ltac complete_mem_equalities :=
  try match goal with
  | [ H: ?vd ?a = Some ?vs, H': ?vd ?a = _ |- _ ] =>
    learn H' rewrite H in H'
  | [ H: ?vd ?a = Some ?vs, H': _ = ?vd ?a |- _ ] =>
    learn H' rewrite H in H'
  end.