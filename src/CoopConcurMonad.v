Require Import CoopConcur.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ _ _ _ |- _ ] =>
    inversion H;
    subst;
    repeat sigT_eq;
    subst
  end.

Ltac inv_fail_step :=
  match goal with
  | [ H: fail_step _ _ _ _ |- _ ] =>
    inversion H;
    subst;
    repeat sigT_eq;
    subst
  end.

Ltac inv_exec' H :=
  inversion H; subst;
  repeat sigT_eq;
  try inv_step;
  try inv_fail_step.

Ltac inv_exec :=
  lazymatch goal with
  | [ H: exec _ _ (Ret _) _ _ |- _ ] =>
    inv_exec' H
  | [ H: exec _ _ (Bind _ _) _ _ |- _ ] =>
    inv_exec' H
  | [ H: exec _ _ _ _ _ |- _ ] =>
    inv_exec' H
  end.

Section MonadLaws.
  Hint Constructors step exec.

  Infix "~=" := prog_equiv (at level 50, left associativity).

  Theorem bind_left_id : forall T T' Sigma v (p: T -> prog Sigma T'),
      Bind (Ret v) p ~= p v.
  Proof.
    split; intros.
    - inv_exec.
      inv_exec; eauto.
      inv_exec; eauto.
    - eauto.
  Qed.

  Theorem bind_right_id : forall T Sigma (p: prog Sigma T),
      Bind p Ret ~= p.
  Proof.
    split; intros.
    - inv_exec; eauto.
      inv_exec; eauto.
    - destruct out; eauto.
  Qed.

  Theorem bind_assoc : forall Sigma T T' T'' (p1: prog Sigma T) (p2: T -> prog Sigma T') (p3: T' -> prog Sigma T''),
      Bind (Bind p1 p2) p3 ~= Bind p1 (fun x => Bind (p2 x) p3).
  Proof.
    split; intros.
    - inv_exec; eauto;
        inv_exec; eauto.
    - inv_exec; eauto.
      inv_exec; eauto.
  Qed.

End MonadLaws.

Ltac monad_simpl_one :=
  match goal with
  | [ |- valid _ _ _ (Bind (Ret _) _) ] =>
    eapply valid_equiv;
    [ apply bind_left_id | ]
  | [ |- valid _ _ _ (Bind _ Ret) ] =>
    eapply valid_equiv;
    [ apply bind_right_id | ]
  | [ |- valid _ _ _ (Bind (Bind _ _) _) ] =>
    eapply valid_equiv;
    [ apply bind_assoc | ]
  end.

Ltac monad_simpl := repeat monad_simpl_one.