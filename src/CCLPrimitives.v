Require Import CCLProg CCLMonadLaws CCLHoareTriples.
Require Import Automation.
Require Import Mem Pred.
Require Import AsyncDisk.
Require Import Word.
Require Import FunctionalExtensionality.

Import CCLTactics.

Section Primitives.

  Variable G:Protocol.

  Ltac begin_prim :=
    unfold cprog_spec, cprog_ok; simpl; intros;
    repeat deex.

  Ltac prim :=
    begin_prim;
    inv_bind; inv_exec;
    unfold ident in *;
    repeat inj_pair2;
    repeat match goal with
           | [ H: context[let '(n, m) := ?a in _] |- _] =>
             destruct a; simpl in *; intuition eauto
           | [ H: precondition {| precondition := _; postcondition := _ |} |- _ ] =>
             simpl in *; intuition eauto
           | [ H: context[exec _ _ _ _ _ -> _] |-
               match ?out with
               | Finished _ _ => _
               | Error => _
               end ] => eapply H; eauto; simpl; intuition eauto
           | [ H: step _ _ (GhostUpdate _ _) _ _ |- _ ] => inv_step
           | [ H: step _ _ (GhostUpdateMem _ _) _ _ |- _ ] => inv_step
           | [ H: ?F (Sigma.mem ?sigma) |- ?F (Sigma.mem _) ] =>
             solve [ destruct sigma; simpl in H; apply H ]
           | [ |- Sigma.disk (Sigma.upd_disk ?sigma _) = _ ] =>
             destruct sigma; simpl in *
           | [ |- Sigma.hm _ = Sigma.hm ?sigma ] =>
             solve [ destruct sigma; simpl in *; auto ]
           | [ |- Sigma.disk _ = Sigma.disk ?sigma ] =>
             solve [ destruct sigma; simpl in *; auto ]
           | [ H: (_ * ?a |-> ?v)%pred _ |- _ ] =>
             learn that (ptsto_valid' H)
           | [ H: ?a = ?b, H': ?a = ?b' |- _ ] =>
             rewrite H in *; clear H
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           | _ => progress subst
           | _ => auto; congruence
           end.

  Ltac break_tuple a n m :=
    let n := fresh n in
    let m := fresh m in
    destruct a as [n m]; simpl in *.

  Theorem BeginRead_ok : forall tid a,
      cprog_spec G tid
                 (fun '(F, v) '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v, NoReader);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
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
                         Sigma.disk sigma a = Some (v, Pending);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
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
                         Sigma.disk sigma a = Some (v0, NoReader);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           F (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = upd (Sigma.disk sigma) a (v, NoReader); |})
                 (Write a v).
  Proof.
    prim.
  Qed.

  Hint Resolve ptsto_upd_disjoint.

  Theorem Alloc_ok : forall tid A (v0:A),
      cprog_spec G tid
                 (fun F '(sigma_i, sigma) =>
                    {| precondition :=
                         F (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') i =>
                           (F * i |-> val v0)%pred (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           sigma_i' = sigma_i; |})
                 (Alloc v0).
  Proof.
    prim.
    destruct sigma; simpl in *; eauto.
  Qed.

  Theorem Get_ok : forall tid A (i: ident),
      cprog_spec G tid
                 (fun '(F, v) '(sigma_i, sigma) =>
                    {| precondition :=
                         (F * i |-> val v)%pred (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           r = v /\
                           sigma_i' = sigma_i /\
                           sigma' = sigma; |})
                 (Get A i).
  Proof.
    prim.
    inj_pair2; auto.
  Qed.

  Hint Resolve ptsto_upd'.

  Theorem Assgn_ok : forall tid A i (v:A),
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                       (F * i |-> val (v0:A))%pred (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           (F * i |-> val v)%pred (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma; |})
                 (Assgn i v).
  Proof.
    prim.
    destruct sigma; simpl in *; eauto.
  Qed.

  Theorem Hash_ok : forall tid sz (buf: word sz),
      cprog_spec G tid
                 (fun F '(sigma_i, sigma) =>
                    {| precondition := F (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') r =>
                           F (Sigma.mem sigma') /\
                           r = hash_fwd buf /\
                           hash_safe (Sigma.hm sigma) (hash_fwd buf) buf /\
                           Sigma.hm sigma' = upd_hashmap' (Sigma.hm sigma) (hash_fwd buf) buf /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           sigma_i' = sigma_i /\
                           sigma' = Sigma.upd_hm sigma buf; |})
                 (Hash buf).
  Proof.
    prim.

    destruct sigma; simpl in *; eauto.
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

  Theorem GhostUpdate_ok : forall tid A i (up: TID -> A -> A),
      cprog_spec G tid
                 (fun '(F, v0) '(sigma_i, sigma) =>
                    {| precondition :=
                         (F * i |-> abs v0)%pred (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           (F * i |-> abs (up tid v0))%pred (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma; |})
                 (GhostUpdate i up).
  Proof.
    prim.
    repeat inj_pair2.
    destruct sigma; simpl in *; eauto.
  Qed.

  Theorem GhostUpdateMem_ok : forall tid A AEQ V i (up: TID -> @mem A AEQ V -> @mem A AEQ V),
      cprog_spec G tid
                 (fun '(F, m0) '(sigma_i, sigma) =>
                    {| precondition :=
                         (F * i |-> absMem m0)%pred (Sigma.mem sigma);
                       postcondition :=
                         fun '(sigma_i', sigma') _ =>
                           (F * i |-> absMem (up tid m0))%pred (Sigma.mem sigma') /\
                           sigma_i' = sigma_i /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma; |})
                 (GhostUpdateMem i up).
  Proof.
    prim.
    repeat inj_pair2.
    destruct sigma; simpl in *; eauto.
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
    prim.
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
Hint Extern 0 {{ @Yield _; _ }} => apply @Yield_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
