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
        | Finished _ _ => _
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
                 (fun '(F, v) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v, NoReader) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' _ =>
                           F (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.disk sigma' = upd (Sigma.disk sigma) a (v, Pending); |})
                 (BeginRead a).
  Proof.
    prim.
  Qed.

  Theorem WaitForRead_ok : forall tid a,
      cprog_spec G tid
                 (fun '(F, v) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v, Pending) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' r =>
                           F (Sigma.mem sigma') /\
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
                 (fun '(F, v0) sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.disk sigma a = Some (v0, NoReader) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' _ =>
                           F (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' =  upd (Sigma.disk sigma) a (v, NoReader) /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (Write a v).
  Proof.
    prim.
  Qed.

  Theorem Alloc_ok : forall tid A (v:A),
      cprog_spec G tid
                 (fun F sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' i =>
                           (F * i |-> val v)%pred (Sigma.mem sigma') /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (Alloc v).
  Proof.
    prim.
    destruct st; simpl in *.
    eapply ptsto_upd_disjoint; eauto.
  Qed.

  Definition Read2 A i1 B i2 : cprog (A*B) :=
    do '(a, (b, _)) <- ReadTxn (RCons A i1 (RCons B i2 RDone));
      Ret (a, b).

  Lemma rtxn_step2 : forall A B i1 i2 a a' b b' u h,
      rtxn_step (RCons A i1 (RCons B i2 RDone)) h (a, (b, u)) ->
      h i1 = Some (val a') ->
      h i2 = Some (val b') ->
      a = a' /\ b = b'.
  Proof.
    intros.
    repeat match goal with
           | [ H: rtxn_step _ _ _ |- _ ] =>
             inversion H; repeat inj_pair2; clear H
           | [ H: (_, _) = (_, _) |- _ ] =>
             inversion H; subst; clear H
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           | [ H: _ = _ |- _ ] => rewrite H in *
           | _ => inj_pair2
           end.
    auto.
  Qed.

  Theorem Read2_ok : forall tid A B i1 i2,
      cprog_spec G tid
                 (fun '(F, a0, b0) sigma =>
                    {| precondition :=
                         (F * i1 |-> val a0 * i2 |-> val b0)%pred (Sigma.mem sigma);
                       postcondition :=
                         fun sigma' '(a, b) =>
                           a = a0 /\
                           b = b0 /\
                           Rely G tid sigma sigma' /\
                           hashmap_le (Sigma.hm sigma) (Sigma.hm sigma')
                    |})
                 (Read2 A i1 B i2).
  Proof.
    prim; try inv_ret.
    apply sep_star_comm in H.
    apply sep_star_assoc_2 in H.
    pose proof (ptsto_valid' H).
    match goal with
      | [ H: exec _ _ _ (ReadTxn _) _ |- _ ] =>
        inv_exec' H
    end.
    match goal with
    | [ H: rtxn_step _ _ _ |- _ ] =>
      eapply rtxn_step2 in H; eauto
    end; intuition; subst.

    apply sep_star_comm in H.
    apply sep_star_assoc_2 in H.
    pose proof (ptsto_valid' H).
    match goal with
      | [ H: exec _ _ _ (ReadTxn _) _ |- _ ] =>
        inv_exec' H
    end.
    clear H6.
    apply (f (val a :: val b :: nil))%list.
    repeat (constructor; eauto).

    repeat match goal with
           | [ H: rtxn_error _ _ |- _ ] =>
             inversion H; repeat inj_pair2; clear H
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           | [ H: _ = _ |- _ ] =>
             rewrite H in *
           | _ => inj_pair2
           end; eauto.
  Qed.

  (* TODO: an AssgnTxn helper theorem *)

  Theorem Hash_ok : forall tid sz (buf: word sz),
      cprog_spec G tid
                 (fun F sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma);
                       postcondition :=
                         fun sigma' r =>
                           F (Sigma.mem sigma') /\
                           r = hash_fwd buf /\
                           hash_safe (Sigma.hm sigma) (hash_fwd buf) buf /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = upd_hashmap' (Sigma.hm sigma) (hash_fwd buf) buf /\
                           Sigma.l sigma' = Sigma.l sigma; |})
                 (Hash buf).
  Proof.
    prim.
    destruct st; eauto.
  Qed.

  Theorem Ret_ok : forall tid T (v:T),
      cprog_spec G tid
                 (fun (_:unit) sigma =>
                    {| precondition := True;
                       postcondition :=
                         fun sigma' r =>
                           sigma' = sigma /\
                           r = v; |})
                 (Ret v).
  Proof.
    prim.
  Qed.

  Theorem Ret_general_ok : forall tid T (v:T) A (spec: Spec A T),
      (forall a sigma, precondition (spec a sigma) -> postcondition (spec a sigma) sigma v) ->
      cprog_spec G tid spec (Ret v).
  Proof.
    unfold cprog_spec, cprog_ok; intros.
    deex.
    inv_exec' H1; inv_ret.
    match goal with
    | [ Hexec: exec _ _ _ (rx _) _ |- _ ] =>
      eapply H2 in Hexec; eauto
    end.
  Qed.

  Definition GetWriteLock :=
    SetLock Free WriteLock.

  Definition Unlock :=
    SetLock WriteLock Free.

  Theorem GetWriteLock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) sigma =>
                    {| precondition := Sigma.l sigma = Free;
                       postcondition :=
                         fun sigma'' _ =>
                           exists sigma', Rely G tid sigma sigma' /\
                                 sigma'' = Sigma.set_l sigma' WriteLock /\
                                 hashmap_le (Sigma.hm sigma) (Sigma.hm sigma''); |})
                 GetWriteLock.
  Proof.
    prim.
    eexists; intuition eauto.
    destruct sigma'0; simpl; eauto.
  Qed.

  (* TODO: change these to separation logic style specs *)

  Theorem Unlock_ok : forall tid,
      cprog_spec G tid
                 (fun (_:unit) sigma =>
                    {| precondition := Sigma.l sigma = WriteLock;
                       postcondition :=
                         fun sigma' _ =>
                           sigma' = Sigma.set_l sigma Free; |})
                 Unlock.
  Proof.
    prim.
  Qed.

End Primitives.

Hint Extern 0 {{ BeginRead _; _ }} => apply BeginRead_ok : prog.
Hint Extern 0 {{ WaitForRead _; _ }} => apply WaitForRead_ok : prog.
Hint Extern 0 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 0 {{ Alloc _; _ }} => apply Alloc_ok : prog.
Hint Extern 0 {{ Read2 _ _; _ }} => apply Read2_ok : prog.
Hint Extern 0 {{ Hash _; _ }} => apply Hash_ok : prog.
Hint Extern 0 {{ GetWriteLock; _ }} => apply GetWriteLock_ok : prog.
Hint Extern 0 {{ Unlock; _ }} => apply Unlock_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
