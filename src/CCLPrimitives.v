Require Import CCLProg CCLMonadLaws CCLHoareTriples.
Require Import Mem Pred.
Require Import AsyncDisk.
Require Import Word.
Require Import FunctionalExtensionality.

Import CCLTactics.

Section Primitives.

  Context {St:StateTypes}.
  Variable G:Protocol St.

  Ltac begin_prim :=
    unfold cprog_spec, cprog_ok; simpl; intros;
    repeat deex.

  Theorem BeginRead_ok : forall tid a,
      cprog_spec G tid
                 (fun v '(sigma_i, sigma) =>
                    {| precondition := Sigma.disk sigma a = Some (v, NoReader);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, Pending)); |})
                 (BeginRead a).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
    (* why does congruence not solve this? *)
    assert (v0 = a0) by congruence; subst; auto.
  Qed.

  Theorem WaitForRead_ok : forall tid a,
      cprog_spec G tid
                 (fun v '(sigma_i, sigma) =>
                    {| precondition :=
                         Sigma.disk sigma a = Some (v, Pending);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, NoReader)) /\
                           r = v; |})
                 (WaitForRead a).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
    (* why does congruence not solve this? *)
    assert (v = a0) by congruence; subst; auto.
    congruence.
  Qed.

  Theorem Write_ok : forall tid a v,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         Sigma.disk sigma a = Some (v0, NoReader);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, NoReader)); |})
                 (Write a v).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Get_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := True;
                       postcondition :=
                         fun  '(sigma_i', sigma') r =>
                           sigma_i' = sigma_i /\
                           sigma' = sigma /\
                           r = Sigma.mem sigma; |})
                 Get.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Assgn_ok : forall tid m',
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := True;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.set_mem sigma m'; |})
                 (Assgn m').
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Hash_ok : forall tid sz (buf: word sz),
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := True;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           r = hash_fwd buf /\
                           hash_safe (Sigma.hm sigma) (hash_fwd buf) buf /\
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_hm sigma buf; |})
                 (Hash buf).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Ret_ok : forall tid T (v:T),
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := True;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma_i' = sigma_i /\
                           sigma' = sigma /\
                           r = v; |})
                 (Ret v).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem GhostUpdate_ok : forall tid up,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := True;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_s sigma (up tid); |})
                 (GhostUpdate up).
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Yield_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := G tid sigma_i sigma;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           Rely G tid sigma sigma' /\
                           sigma_i' = sigma'; |})
                 Yield.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto; simpl.
    intuition eauto.
    eauto.
  Qed.

End Primitives.

Hint Extern 0 {{ BeginRead _; _ }} => apply BeginRead_ok : prog.
Hint Extern 0 {{ WaitForRead _; _ }} => apply WaitForRead_ok : prog.
Hint Extern 0 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 0 {{ @Get _; _ }} => apply @Get_ok : prog.
Hint Extern 0 {{ Assgn _; _ }} => apply Assgn_ok : prog.
Hint Extern 0 {{ Hash _; _ }} => apply Hash_ok : prog.
Hint Extern 0 {{ Ret _; _ }} => apply Ret_ok : prog.
Hint Extern 0 {{ GhostUpdate _; _ }} => apply GhostUpdate_ok : prog.
Hint Extern 0 {{ @Yield _; _ }} => apply @Yield_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
