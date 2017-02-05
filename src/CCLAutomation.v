Require Import CCLProg CCLPrimitives.
Require Export Automation.

Ltac destruct_st :=
  match goal with
  | [ st: Sigma _ * Sigma _, H: context[let '(a, b) := ?st in _] |- _ ] =>
    let sigma_i := fresh "sigma_i" in
    let sigma := fresh "sigma" in
    (destruct st as [a b] || destruct st as [sigma_i sigma]); cbn [precondition postcondition] in *
  end.

(* unfold ReflectDouble into primitive Hoare double statement *)
Ltac unfold_double :=
  match goal with
  | [ H: ReflectDouble _ _ _ _ _ _ |- _ ] =>
    unfold ReflectDouble in H; simpl;
    repeat deex
  | [ |- ReflectDouble _ _ _ _ _ _ ] =>
    unfold ReflectDouble; simpl
  end.

Ltac simplify :=
  intros; repeat deex;
  repeat unfold_double;
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
  match goal with
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
