Require Import CCLProg CCLMonadLaws CCLHoareTriples.
Require Import Mem Pred.
Require Import AsyncDisk.
Require Import Word.
Require Import Hashmap.
Require Import FunctionalExtensionality.
Require Import Automation.

Import CCLTactics.

Section Primitives.

  Variable G:Protocol.

  Ltac begin_prim :=
    unfold cprog_spec, cprog_ok; simpl; intros;
    repeat deex.

  Lemma if_CanWrite : forall A (a a':A) l,
      l = WriteLock ->
      (if CanWrite l then a else a') = a.
  Proof.
    intros.
    subst; simpl; auto.
  Qed.

  Hint Rewrite if_CanWrite using (solve [ auto ]) : locks.

  Ltac simplify_step :=
    match goal with
    | [ H: context[let '(n, m) := ?a in _] |- _] =>
      destruct a; simpl in *; intuition eauto
    | [ H: precondition {| precondition := _; postcondition := _ |} |- _ ] =>
      simpl in *; intuition eauto
    | [ H: context[exec _ _ _ _ _ -> _] |-
        match ?out with
        | Finished _ _ _ => _
        | Error => _
        end ] => eapply H; eauto; simpl; intuition eauto
    | [ H: ?F (Sigma.mem ?sigma) |- ?F (Sigma.mem _) ] =>
      solve [ destruct sigma; simpl in H; apply H ]
    | [ |- Sigma.disk (Sigma.upd_disk ?sigma _) = _ ] =>
      destruct sigma; simpl in *
    | [ |- Sigma.hm _ = Sigma.hm ?sigma ] =>
      solve [ destruct sigma; simpl in *; auto ]
    | [ |- Sigma.disk _ = Sigma.disk ?sigma ] =>
      solve [ destruct sigma; simpl in *; auto ]
    | [ |- Sigma.l _ = Sigma.l ?sigma ] =>
      solve [ destruct sigma; simpl in *; auto ]
    | [ H: (_ * ?a |-> ?v)%pred _ |- _ ] =>
      learn that (ptsto_valid' H)
    | [ H: ?a = ?b, H': ?a = ?b' |- _ ] =>
      rewrite H in *; clear H
    | [ H: Some _ = Some _ |- _ ] =>
      inversion H; subst; clear H
    | _ => simpl_match
    | _ => progress autorewrite with locks in *
    | [ x := _ |- _ ] => subst x
    | _ => progress subst
    | _ => auto; congruence
    end.

  Ltac prim :=
    begin_prim;
    inv_bind; inv_exec;
    unfold ident in *;
    repeat inj_pair2;
    repeat simplify_step.

  Theorem BeginRead_ok : forall tid a,
      cprog_spec G tid
                 (fun '(F, v) '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v, NoReader) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.disk sigma' = upd (Sigma.disk sigma) a (v, Pending); |})
                 (BeginRead a).
  Proof.
    prim.
  Qed.

  Theorem WaitForRead_ok : forall tid a,
      cprog_spec G tid
                 (fun '(F, v) '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v, Pending) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.disk sigma' = upd (Sigma.disk sigma) a (v, NoReader) /\
                           r = v; |})
                 (WaitForRead a).
  Proof.
    prim.
  Qed.

  Theorem Write_ok : forall tid a v,
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v0, NoReader) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' =  upd (Sigma.disk sigma) a (v, NoReader) /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (Write a v).
  Proof.
    prim.
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

  Theorem Alloc_ok : forall tid A (v:A),
      cprog_spec G tid
                 (fun F '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') i =>
                           ((F:heappred) * i |-> val v)%pred (Sigma.mem sigma') /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           sigma_i' = sigma_i; |})
                 (Alloc v).
  Proof.
    prim.
    destruct sigma; simpl in *.
    eapply ptsto_upd_disjoint; eauto.
  Qed.

  Theorem Get_ok : forall tid A i,
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         ((F:heappred) * i |-> val (v0:A))%pred (Sigma.mem sigma) /\
                         ReadPermission (Sigma.l sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           sigma' = sigma /\
                           sigma_i' = sigma_i /\
                           r = v0; |})
                 (Get A i).
  Proof.
    prim.

    inj_pair2; auto.
    inv_exec; eauto.
  Qed.

  Theorem Assgn_ok : forall tid A i (v:A),
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         ((F:heappred) * i |-> val (v0:A))%pred (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           (F * i |-> val v)%pred (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (Assgn i v).
  Proof.
    prim.
    inj_pair2.
    destruct sigma; simpl in *; eauto.
    eauto using ptsto_upd'.
  Qed.

  Theorem Hash_ok : forall tid sz (buf: word sz),
      cprog_spec G tid
                 (fun F '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           F (Sigma.mem sigma') /\
                           r = hash_fwd buf /\
                           hash_safe (Sigma.hm sigma) (hash_fwd buf) buf /\
                           sigma_i' = sigma_i /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = upd_hashmap' (Sigma.hm sigma) (hash_fwd buf) buf /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (Hash buf).
  Proof.
    prim.
    destruct sigma; eauto.
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
    prim.
  Qed.

  Theorem GhostUpdate_ok : forall tid A i up,
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         ((F:heappred) * i |-> abs (v0:A))%pred (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           (F * i |-> abs (up tid v0))%pred (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (GhostUpdate i up).
  Proof.
    prim.
    inj_pair2.
    destruct sigma; simpl in *.
    eauto using ptsto_upd'.
  Qed.

  Theorem GhostUpdateMem_ok : forall tid A AEQ V i up,
      cprog_spec G tid
                 (fun '(F, m0) '(sigma_i, sigma) =>
                    {| precondition :=
                         ((F:heappred) * i |-> absMem (m0:@mem A AEQ V))%pred (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           (F * i |-> absMem (up tid m0))%pred (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (GhostUpdateMem i up).
  Proof.
    prim.
    repeat inj_pair2.
    destruct sigma; simpl in *.
    eauto using ptsto_upd'.
  Qed.

  Definition GetReadLock :=
    SetLock Free ReadLock.

  Definition GetWriteLock :=
    SetLock Free WriteLock.

  Definition UpgradeReadLock :=
    SetLock ReadLock WriteLock.

  Definition ReleaseReadLock :=
    SetLock ReadLock Free.

  Definition Unlock :=
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
    prim.
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
    prim.
    eexists; intuition eauto.
    destruct sigma'0; simpl; eauto.
  Qed.

  (* TODO: change these to separation logic style specs *)

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
    prim.
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
    prim.
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
    prim.
    destruct (lock_dec (Sigma.l sigma) WriteLock); try congruence.
    destruct (lock_dec (Sigma.l sigma) ReadLock); try congruence.
  Qed.

End Primitives.

Hint Extern 0 {{ BeginRead _; _ }} => apply BeginRead_ok : prog.
Hint Extern 0 {{ WaitForRead _; _ }} => apply WaitForRead_ok : prog.
Hint Extern 0 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 0 {{ Alloc _; _ }} => apply Alloc_ok : prog.
Hint Extern 0 {{ Get _ _; _ }} => apply Get_ok : prog.
Hint Extern 0 {{ Assgn _ _; _ }} => apply Assgn_ok : prog.
Hint Extern 0 {{ Hash _; _ }} => apply Hash_ok : prog.
Hint Extern 0 {{ Ret _; _ }} => apply Ret_ok : prog.
Hint Extern 0 {{ GhostUpdate _ _; _ }} => apply GhostUpdate_ok : prog.
Hint Extern 0 {{ GhostUpdateMem _ _; _ }} => apply GhostUpdateMem_ok : prog.
Hint Extern 0 {{ GetReadLock; _ }} => apply GetReadLock_ok : prog.
Hint Extern 0 {{ GetWriteLock; _ }} => apply GetWriteLock_ok : prog.
Hint Extern 0 {{ UpgradeReadLock; _ }} => apply UpgradeReadLock_ok : prog.
Hint Extern 0 {{ ReleaseReadLock; _ }} => apply ReleaseReadLock_ok : prog.
Hint Extern 0 {{ Unlock; _ }} => apply Unlock_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
