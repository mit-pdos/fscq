Require Import CCL.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.

Section SyncRead.

  Variable St:StateTypes.
  Variable G: Protocol St.

  Definition SyncRead a : @cprog St _ :=
    _ <- BeginRead a;
      v <- WaitForRead a;
      Ret v.

  Theorem SyncRead_ok : forall tid a,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         Sigma.disk sigma a = Some (v0, NoReader);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma_i' = sigma_i /\
                           sigma' = sigma /\
                           r = v0; |})
                 (SyncRead a).
  Proof.
    unfold SyncRead.
    step.

    eexists; intuition eauto.

    step.

    eexists; intuition eauto.

    (* need better way to simplify nested updates on Sigma *)
    destruct sigma; simpl in *.
    autorewrite with upd; eauto.

    step.
    intuition auto; simplify.

    destruct sigma; simpl in *.

    f_equal.
    extensionality a'.
    destruct (addr_eq_dec a a'); subst;
      autorewrite with upd; auto.
  Qed.

End SyncRead.

Hint Extern 0 {{ SyncRead _; _ }} => apply SyncRead_ok : prog.