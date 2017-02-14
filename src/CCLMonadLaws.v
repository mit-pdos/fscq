Require Import CCLProg.

Import CCLTactics.

Section MonadLaws.

  Variable St:StateTypes.
  Variable G:Protocol St.

  Definition exec_equiv T (p p': cprog T) :=
    forall tid st out, exec G tid st p out <-> exec G tid st p' out.

  Hint Constructors exec.
  Hint Resolve ExecRet.

  Theorem monad_right_id : forall T (p: cprog T),
      exec_equiv (Bind p Ret) p.
  Proof.
    split; intros.
    - inv_bind; eauto.
      inv_ret; eauto.
    - destruct out, st; eauto.
  Qed.

  Theorem monad_left_id : forall T T' (p: T -> cprog T') v,
      exec_equiv (Bind (Ret v) p) (p v).
  Proof.
    split; intros.
    - inv_bind.
      inv_ret; eauto.
      inv_ret.
    - destruct out, st; eauto.
  Qed.

  Theorem monad_assoc : forall T T' T''
                          (p1: cprog T)
                          (p2: T -> cprog T')
                          (p3: T' -> cprog T''),
      exec_equiv (Bind (Bind p1 p2) p3) (Bind p1 (fun x => Bind (p2 x) p3)).
  Proof.
    split; intros;
      repeat (inv_bind; eauto).
  Qed.

  Theorem cprog_ok_respects_exec_equiv : forall T (p p': cprog T) tid pre,
      exec_equiv p p' ->
      cprog_ok G tid pre p' ->
      cprog_ok G tid pre p.
  Proof.
    unfold cprog_ok, exec_equiv; intros.
    eapply H0; eauto.
    apply H; eauto.
  Qed.

End MonadLaws.