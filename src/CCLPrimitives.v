Require Import CCL.
Require Import Eqdep.

Section Primitives.

  Variable St:StateTypes.
  Variable G: TID -> Sigma St -> Sigma St -> Prop.

  Theorem cprog_ok_weaken : forall T tid (pre pre': _ -> _ -> Prop) (p: cprog St T),
      cprog_ok G tid pre p ->
      (forall st donecond, pre' st donecond -> pre st donecond) ->
      cprog_ok G tid pre' p.
  Proof.
    intros.
    unfold cprog_ok; intros.
    apply H0 in H1.
    eapply H; eauto.
  Qed.

  Definition exec_equiv T (p p': cprog St T) :=
    forall tid st out, exec G tid st p out <-> exec G tid st p' out.

  Hint Constructors exec.

  Ltac inj_pair2 :=
    match goal with
    | [ H: existT ?P ?a _ = existT ?P ?a _ |- _ ] =>
      apply inj_pair2 in H; subst
    end.

  Ltac inv_bind :=
    match goal with
    | [ H: exec _ _ _ (Bind _ _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ _ _ _ |- _ ] =>
            solve [ inversion H ]
          | [ H: fail_step _ _ |- _ ] =>
            solve [ inversion H ]
          end;
      clear H
    end.

  Ltac inv_ret :=
    match goal with
    | [ H: exec _ _ _ (Ret _) _ |- _ ] =>
      inversion H; subst; repeat inj_pair2;
      try match goal with
          | [ H: step _ _ (Ret _) _ _ |- _ ] =>
            solve [ inversion H ]
          | [ H: fail_step _ (Ret _) |- _ ] =>
            solve [ inversion H ]
          end;
      clear H
    end.

  Theorem monad_right_id : forall T (p: cprog _ T),
      exec_equiv (Bind p Ret) p.
  Proof.
    split; intros.
    - inv_bind; eauto.
      inv_ret; eauto.
    - destruct out, st; eauto.
  Qed.

  Theorem monad_left_id : forall T T' (p: T -> cprog _ T') v,
      exec_equiv (Bind (Ret v) p) (p v).
  Proof.
    split; intros.
    - inv_bind.
      inv_ret; eauto.
      inv_ret.
    - destruct out, st; eauto.
  Qed.

  Theorem monad_assoc : forall T T' T''
                          (p1: cprog _ T)
                          (p2: T -> cprog _ T')
                          (p3: T' -> cprog _ T''),
      exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun x => Bind (p2 x) p3)).
  Proof.
    split; intros;
      repeat (inv_bind; eauto).
  Qed.

End Primitives.