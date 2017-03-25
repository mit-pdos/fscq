Require Import CCL.
Require Import AsyncDisk.
Require Import FunctionalExtensionality.

Section SyncRead.

  Variable G: Protocol.

  Definition SyncRead a :=
    _ <- BeginRead a;
      v <- WaitForRead a;
      Ret v.

  Hint Resolve local_locked.

  Theorem SyncRead_ok : forall tid a,
      cprog_spec G tid
                 (fun '(F, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         local_l tid (Sigma.l sigma) = Locked /\
                         Sigma.disk sigma a = Some (v0, NoReader);
                       postcondition :=
                         fun sigma' r =>
                           F (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           r = v0; |})
                 (SyncRead a).
  Proof.
    unfold SyncRead.
    step; simpl in *; safe_intuition.
    descend; simpl; intuition eauto.

    step; simpl in *; safe_intuition.
    descend; simpl; intuition eauto.

    replace (Sigma.disk st0).
    autorewrite with upd; eauto.
    replace (Sigma.l st0); eauto.

    step; simpl in *; intuition eauto.
    congruence.
    (* TODO: why the names st and not those used in the spec? what changed? *)
    replace (Sigma.disk st1).
    replace (Sigma.disk st0).

    extensionality a'.
    destruct (addr_eq_dec a a'); subst;
      autorewrite with upd; auto.

    congruence.
  Qed.

End SyncRead.

Hint Extern 0 {{ SyncRead _; _ }} => apply SyncRead_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)