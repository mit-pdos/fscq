Require Import CCL.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.

Section SyncRead.

  Variable G: Protocol.

  Definition SyncRead a :=
    _ <- BeginRead a;
      v <- WaitForRead a;
      Ret v.

  Ltac break_tuple a n m :=
    let n := fresh n in
    let m := fresh m in
    destruct a as [n m];
    simpl in *.

  Theorem SyncRead_ok : forall tid a,
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v0, NoReader);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           r = v0; |})
                 (SyncRead a).
  Proof.
    unfold SyncRead.
    step;
      repeat match goal with
             | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
               break_tuple a n m
             end; intuition.
    descend; simpl; intuition eauto.

    step;
      repeat match goal with
             | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
               break_tuple a n m
             end; intuition.
    descend; simpl; intuition eauto.

    replace (Sigma.disk sigma').
    autorewrite with upd; eauto.

    step;
      repeat match goal with
             | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
               break_tuple a n m
             end; intuition.
  Qed.

End SyncRead.

Hint Extern 0 {{ SyncRead _; _ }} => apply SyncRead_ok : prog.