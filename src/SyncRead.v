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
                 (fun '(F, v0) '(ExecState d_i sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock /\
                         Sigma.disk sigma a = Some (v0, NoReader);
                       postcondition :=
                         fun '(ExecState d_i' sigma') r =>
                           F (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           r = v0 /\
                           d_i' = d_i ; |})
                 (SyncRead a).
  Proof.
    unfold SyncRead.
    step;
      repeat match goal with
             | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
               break_tuple a n m
             | [ H: context[ let 'ExecState d_i sigma := ?st in _ ] |- _ ] =>
               let d_i := fresh d_i in
               let sigma := fresh sigma in
               destruct st as [d_i sigma]
             end; simpl in *; intuition.
    descend; simpl; intuition eauto.

    step;
      repeat match goal with
             | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
               break_tuple a n m
             | [ H: context[ let 'ExecState d_i sigma := ?st in _ ] |- _ ] =>
               let d_i := fresh d_i in
               let sigma := fresh sigma in
               destruct st as [d_i sigma]
             end; intuition.
    descend; simpl; intuition eauto.

    replace (Sigma.disk sigma').
    autorewrite with upd; eauto.
    congruence.

    step;
      repeat match goal with
             | [ H: context[let '(n, m) := ?a in _] |- _ ] =>
               break_tuple a n m
             | [ H: context[ let 'ExecState d_i sigma := ?st in _ ] |- _ ] =>
               let d_i := fresh d_i in
               let sigma := fresh sigma in
               destruct st as [d_i sigma]
             end; intuition; subst; try congruence.
    replace (Sigma.disk sigma'0).
    replace (Sigma.disk sigma').

    extensionality a'.
    destruct (addr_eq_dec a a'); subst;
      autorewrite with upd; auto.
  Qed.

End SyncRead.

Hint Extern 0 {{ SyncRead _; _ }} => apply SyncRead_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)