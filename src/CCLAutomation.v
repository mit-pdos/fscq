Require Import CCLProg CCLMonadLaws CCLHoareTriples CCLPrimitives.
Require Export Automation.

Ltac destruct_st :=
  match goal with
  | [ st: Sigma _ * Sigma _, H: context[let '(a, b) := ?st in _] |- _ ] =>
    let sigma_i := fresh "sigma_i" in
    let sigma := fresh "sigma" in
    (destruct st as [a b] || destruct st as [sigma_i sigma]); cbn [precondition postcondition] in *
  end.

Ltac simplify :=
  intros; repeat deex;
  repeat destruct_st;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         | [ |- exists (_:unit), _ ] => exists tt
         | [ |- True /\ _ ] => split; [ exact I | ]
         | [ a:unit |- _ ] => clear a
         | _ => progress subst
         | _ => progress intros
         end.

Ltac monad_simpl :=
  let rewrite_equiv H := eapply cprog_ok_respects_exec_equiv;
                         [ solve [ apply H ] | ] in
  repeat match goal with
         (* TODO: apply these with pattern matching, to avoid unfolding
         definitions in order to rewrite *)
         | _ => rewrite_equiv monad_right_id
         | _ => rewrite_equiv monad_left_id
         | _ => rewrite_equiv monad_assoc
         end.

Ltac step :=
  intros;
  match goal with
  | [ |- cprog_spec _ _ _ _ ] => unfold cprog_spec; step
  | [ |- cprog_ok _ _ _ _ ] =>
    eapply cprog_ok_weaken; [
      match goal with
      | _ => monad_simpl; solve [ auto with prog ]
      | _ => apply Ret_ok
      | _ => monad_simpl;
            lazymatch goal with
            | [ |- cprog_ok _ _ _ (Bind ?p _) ] =>
              fail "no spec for" p
            | [ |- cprog_ok _ _ _ ?p ] =>
              fail "no spec for" p
            end
      end | ];
    simplify
  end.
