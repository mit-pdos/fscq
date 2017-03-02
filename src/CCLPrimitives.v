Require Import CCLProg CCLMonadLaws CCLHoareTriples.
Require Import Mem Pred.
Require Import AsyncDisk.
Require Import Word.
Require Import Hashmap.
Require Import FunctionalExtensionality.

Import CCLTactics.

Section Primitives.

  Context {St:StateTypes}.
  Variable G:Protocol St.

  Ltac begin_prim :=
    unfold cprog_spec, cprog_ok; simpl; intros;
    repeat deex;
    try match goal with
        | [ H: context[let (n, m) := ?a in _] |- _ ] =>
          let n := fresh n in
          let m := fresh m in
          destruct a as [m n];
          simpl in *;
          Automation.safe_intuition
        end.

  Ltac inv_opt :=
    match goal with
    | [ H: Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    end.

  Theorem BeginRead_ok : forall tid a,
      cprog_spec G tid
                 (fun v '(sigma_i, sigma) =>
                    {| precondition :=
                         Sigma.disk sigma a = Some (v, NoReader) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, Pending)); |})
                 (BeginRead a).
  Proof.
    begin_prim.
    inv_bind; inv_exec.
    inv_opt.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem WaitForRead_ok : forall tid a,
      cprog_spec G tid
                 (fun v '(sigma_i, sigma) =>
                    {| precondition :=
                         Sigma.disk sigma a = Some (v, Pending) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, NoReader)) /\
                           r = v; |})
                 (WaitForRead a).
  Proof.
    begin_prim.
    inv_bind; inv_exec.
    inv_opt.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Write_ok : forall tid a v,
      cprog_spec G tid
                 (fun v0 '(sigma_i, sigma) =>
                    {| precondition :=
                         Sigma.disk sigma a = Some (v0, NoReader) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_disk sigma (fun d => upd d a (v, NoReader)); |})
                 (Write a v).
  Proof.
    begin_prim.
    inv_bind; inv_exec.
    inv_opt.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Lemma read_permission_not_free : forall l,
      ReadPermission l ->
      l = Free ->
      False.
  Proof.
    intros; subst.
    inversion H.
  Qed.

  Hint Resolve read_permission_not_free.

  Theorem Get_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := ReadPermission (Sigma.l sigma);
                       postcondition :=
                         fun  '(sigma_i', sigma') r =>
                           sigma_i' = sigma_i /\
                           sigma' = sigma /\
                           r = Sigma.mem sigma; |})
                 Get.
  Proof.
    begin_prim.
    inv_bind; inv_exec; eauto.

    eapply H2; eauto; simpl.
    intuition eauto.
  Qed.

  Theorem Assgn_ok : forall tid m',
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := Sigma.l sigma = WriteLock;
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
                    {| precondition := Sigma.l sigma = WriteLock;
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

  Definition GetReadLock : @cprog St _ :=
    SetLock Free ReadLock.

  Definition GetWriteLock : @cprog St _ :=
    SetLock Free WriteLock.

  Definition UpgradeReadLock : @cprog St _ :=
    SetLock ReadLock WriteLock.

  Definition ReleaseReadLock : @cprog St _ :=
    SetLock ReadLock Free.

  Definition Unlock : @cprog St _ :=
    SetLock WriteLock Free.

  Theorem GetReadLock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := Sigma.l sigma = Free;
                       postcondition :=
                         fun '(sigma_i', sigma'') _ =>
                           exists sigma', Rely G tid sigma sigma' /\
                                 sigma'' = Sigma.set_l sigma' ReadLock /\
                                 hashmap_le (Sigma.hm sigma) (Sigma.hm sigma'') /\
                                 sigma_i' = sigma''; |})
                 GetReadLock.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto.
    intuition eauto.

    eexists; intuition eauto.
    destruct sigma'0; simpl; eauto.
  Qed.

  Theorem GetWriteLock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := Sigma.l sigma = Free;
                       postcondition :=
                         fun '(sigma_i', sigma'') _ =>
                           exists sigma', Rely G tid sigma sigma' /\
                                 sigma'' = Sigma.set_l sigma' WriteLock /\
                                 hashmap_le (Sigma.hm sigma) (Sigma.hm sigma'') /\
                                 sigma_i' = sigma''; |})
                 GetWriteLock.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto.
    intuition eauto.

    eexists; intuition eauto.
    destruct sigma'0; simpl; eauto.
  Qed.

  Theorem UpgradeReadLock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := Sigma.l sigma = ReadLock;
                       postcondition :=
                         fun '(sigma_i', sigma') l' =>
                           match l' with
                           | ReadLock => sigma' = sigma
                           | WriteLock => sigma' = Sigma.set_l sigma WriteLock
                           | Free => False
                           end; |})
                 UpgradeReadLock.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto.
    intuition eauto.

    eapply H2; eauto.
    intuition eauto.
  Qed.

  Theorem ReleaseReadLock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := Sigma.l sigma = ReadLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma' = Sigma.set_l sigma Free /\
                           sigma_i' = sigma_i; |})
                 ReleaseReadLock.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto.
    intuition eauto.
  Qed.

  Theorem Unlock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) '(sigma_i, sigma) =>
                    {| precondition := Sigma.l sigma = WriteLock /\
                                       G tid sigma_i sigma;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           sigma' = Sigma.set_l sigma Free /\
                           sigma_i' = sigma'; |})
                 Unlock.
  Proof.
    begin_prim.
    inv_bind; inv_exec.

    eapply H2; eauto.
    intuition eauto.
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
Hint Extern 0 {{ GetReadLock; _ }} => apply GetReadLock_ok : prog.
Hint Extern 0 {{ GetWriteLock; _ }} => apply GetWriteLock_ok : prog.
Hint Extern 0 {{ UpgradeReadLock; _ }} => apply UpgradeReadLock_ok : prog.
Hint Extern 0 {{ ReleaseReadLock; _ }} => apply ReleaseReadLock_ok : prog.
Hint Extern 0 {{ Unlock; _ }} => apply Unlock_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
