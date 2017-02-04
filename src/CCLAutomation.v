Require Import CCLProg CCLPrimitives.
Require Pred.

Ltac destruct_st :=
  match goal with
  | [ st: Sigma _ * Sigma _, H: context[let '(a, b) := ?st in _] |- _ ] =>
    destruct st as [a b]; cbn [precondition postcondition] in *
  end.

(* unfold ReflectDouble into primitive Hoare double statement *)
Ltac unfold_double :=
  match goal with
  | [ H: ReflectDouble _ _ _ _ _ _ |- _ ] =>
    unfold ReflectDouble in H; simpl;
    repeat Pred.deex
  | [ |- ReflectDouble _ _ _ _ _ _ ] =>
    unfold ReflectDouble; simpl
  end.

Ltac simplify :=
  intros; repeat Pred.deex;
  repeat unfold_double;
  repeat destruct_st;
  repeat match goal with
         | [ H: _ /\ _ |- _ ] => destruct H
         | _ => subst
         end.

Ltac monad_simpl :=
  let rewrite_equiv H := eapply cprog_ok_respects_exec_equiv;
                         [ solve [ apply H ] | ] in
  repeat match goal with
         | _ => rewrite_equiv monad_right_id
         | _ => rewrite_equiv monad_left_id
         | _ => rewrite_equiv monad_assoc
         end.

Ltac step :=
  match goal with
  | [ |- cprog_ok _ _ _ _ ] =>
    eapply cprog_ok_weaken; [
      monad_simpl; (solve [ auto with prog ] ||
                    match goal with
                    | [ |- cprog_ok _ _ _ (Bind ?p _) ] =>
                      fail "no spec for" p
                    end) | ];
    simplify
  end.
