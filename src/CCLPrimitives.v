Require Import CCLProg CCLMonadLaws CCLHoareTriples.
Require Import Mem Pred.
Require Import SepAuto.
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
    | [ |- Sigma.init_disk _ = Sigma.init_disk ?sigma ] =>
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
                           Sigma.disk sigma' = upd (Sigma.disk sigma) a (v, Pending) /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma ; |})
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
                           r = v /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma ; |})
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
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma ; |})
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
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
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
                           (if CanWrite (Sigma.l sigma) then
                             sigma' = sigma
                           else
                             Rely G tid sigma sigma') /\
                           hashmap_le (Sigma.hm sigma) (Sigma.hm sigma') /\
                           Sigma.l sigma' = Sigma.l sigma ; |})
                 (Read2 A i1 B i2).
  Proof.
    prim; try inv_ret.
    - apply sep_star_comm in H.
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
      destruct (Sigma.l st); simpl; intuition auto.
      destruct (Sigma.l st); simpl; intuition subst.
      reflexivity.
      destruct (Sigma.l st) eqn:?; intuition (subst; eauto).
    - apply sep_star_comm in H.
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

  Definition Assgn1 (i:ident) A (v:A) :=
    AssgnTxn (WCons (NewVal i v) WDone).

  Lemma wtxn_step_assgn1 : forall i A (v:A) tid (h h':heap),
      wtxn_step tid (WCons (NewVal i v) WDone) h h' ->
      h' = upd h i (val v).
  Proof.
    intros.
    repeat match goal with
           | [ H: wtxn_step _ _ _ _ |- _ ] =>
             inversion H; subst; clear H; repeat inj_pair2
           end; auto.
  Qed.

  Theorem Assgn1_ok : forall tid i A (v:A),
      cprog_spec G tid
                 (fun '(F, v0) sigma =>
                    {| precondition :=
                         (F * i |-> val (v0: A))%pred (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock /\
                         (forall sigma',
                           (F * i |-> val v)%pred (Sigma.mem sigma') ->
                           Sigma.hm sigma' = Sigma.hm sigma ->
                           Sigma.disk sigma' = Sigma.disk sigma ->
                           Sigma.init_disk sigma' = Sigma.init_disk sigma ->
                           Sigma.l sigma' = Sigma.l sigma ->
                           G tid sigma sigma');
                       postcondition :=
                         fun sigma' _ =>
                           (F * i |-> val v)%pred (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (Assgn1 i v).
  Proof.
    begin_prim; inv_bind.
    inv_exec; unfold ident in *; repeat inj_pair2.
    repeat match goal with
           | [ u: unit |- _ ] =>
             destruct u
           | [ x := _ |- _ ] => subst x
           end.
    - destruct a as (F & v0); simpl in *; intuition eauto.
      match goal with
        | [ H: wtxn_step _ _ _ _ |- _ ] =>
          apply wtxn_step_assgn1 in H
      end; subst.
      destruct st; simpl in *.
      eapply H1; eauto; simpl; intuition.
      eapply ptsto_upd'; eauto.
    - destruct a as (F & v0); simpl in *; intuition eauto.
      pose proof (ptsto_valid' H0).
      inv_exec.
      clear H4.
      apply f.
      econstructor; eauto.
      constructor.

      match goal with
        | [ H: wtxn_step _ _ _ _ |- _ ] =>
          apply wtxn_step_assgn1 in H
      end; subst.
      subst sigma'.
      destruct st; simpl in *; subst.
      match goal with
      | [ H: ~G _ _ _ |- _ ] =>
        apply H
      end.
      eapply H3; eauto; simpl.
      eapply ptsto_upd'; eauto.

      repeat match goal with
             | [ H: wtxn_error _ _ |- _ ] =>
               inversion H; subst; clear H; repeat inj_pair2
             end.
      repeat match goal with
             | [ H: _ = _ |- _ ] =>
               progress rewrite H in *
             | [ H: Some _ = Some _ |- _ ] =>
               inversion H; subst; clear H
             | _ => inj_pair2
             end.
      eauto.
  Qed.

  Record Assgn2_txn :=
    Make_assgn2 {
        var1: ident;
        var1T: Type;
        val1: var1T;

        var2: ident;
        var2T: Type;
        val2: var2T;

        abs1: ident;
        abs1T: Type;
        abs1Up: TID->
                abs1T -> abs1T
      }.

  Definition Assgn2_abs (txn:Assgn2_txn) :=
    let vars := WCons (NewVal (var1 txn) (val1 txn))
                      (WCons (NewVal (var2 txn) (val2 txn)) WDone) in
    let txn := WCons (AbsUpd (abs1 txn) (abs1Up txn)) vars in
    AssgnTxn txn.

  Lemma wtxn_step_assgn2 : forall i__g G1 (g0:G1) (up: TID -> G1 -> G1) i__a A (a: A) i__b B (b: B) tid (h h':heap),
      h i__g = Some (abs g0) ->
      wtxn_step tid (WCons (AbsUpd i__g up)
                           (WCons (NewVal i__a a)
                                  (WCons (NewVal i__b b) WDone))) h h' ->
      h' = upd (upd (upd h i__g (abs (up tid g0))) i__a (val a)) i__b (val b) .
  Proof.
    intros.
    repeat match goal with
           | [ H: wtxn_step _ _ _ _ |- _ ] =>
             inversion H; subst; clear H; repeat inj_pair2
           | [ H: Some _ = Some _ |- _ ] =>
             inversion H; subst; clear H
           | [ H: _ = _ |- _ ] =>
             progress rewrite H in *
           | _ => inj_pair2
           | _ => congruence
           end.
  Qed.

  Ltac rotate1 :=
    apply sep_star_comm;
    repeat (rewrite <- sep_star_assoc || apply sep_star_assoc_2).

  Theorem Assgn2_abs_ok : forall tid txn,
      cprog_spec G tid
                 (fun '(F, a0, b0, g) sigma =>
                    {| precondition :=
                         (F *
                          var1 txn |-> val (a0: var1T txn) *
                          var2 txn |-> val (b0: var2T txn) *
                          abs1 txn |-> abs g)%pred (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock /\
                         (forall sigma',
                           (F *
                            var1 txn |-> val (val1 txn) *
                            var2 txn |-> val (val2 txn) *
                            abs1 txn |-> abs (abs1Up txn tid g))%pred (Sigma.mem sigma') ->
                           Sigma.hm sigma' = Sigma.hm sigma ->
                           Sigma.disk sigma' = Sigma.disk sigma ->
                           Sigma.l sigma' = Sigma.l sigma ->
                           G tid sigma sigma');
                       postcondition :=
                         fun sigma' _ =>
                           (F *
                            var1 txn |-> val (val1 txn) *
                            var2 txn |-> val (val2 txn) *
                            abs1 txn |-> abs (abs1Up txn tid g))%pred (Sigma.mem sigma') /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
                 (Assgn2_abs txn).
  Proof.
    begin_prim; inv_bind.
    inv_exec; unfold ident in *; repeat inj_pair2.
    destruct a as (((F & a0) & b0) & g); simpl in *;
      intuition.
    assert (Sigma.mem st (abs1 txn) = Some (abs g)).
    eapply ptsto_valid'; eauto.
    match goal with
      | [ H: wtxn_step _ _ _ _ |- _ ] =>
        eapply wtxn_step_assgn2 in H; eauto; subst
    end.
    subst sigma'.
    eapply H1; eauto.
    destruct st; simpl in *; intuition eauto.
    repeat (match goal with
            | _ => solve [ pred_apply; cancel ]
            | _ => eapply ptsto_upd
            | _ => rotate1
            end).

    destruct a as (((F & a0) & b0) & g); simpl in *;
      intuition.
    inv_exec.
    clear H4.
    apply f.
    repeat econstructor.
    eapply ptsto_valid; pred_apply; cancel.
    eapply ptsto_valid; pred_apply; cancel.
    eapply ptsto_valid; pred_apply; cancel.

    match goal with
    | [ H: ~ G _ _ _ |- _ ] =>
      apply H
    end.
    assert (Sigma.mem st (abs1 txn) = Some (abs g)).
    eapply ptsto_valid'; eauto.
    subst sigma'.
    destruct st; simpl in *.
    eapply H3; eauto.
    match goal with
      | [ H: wtxn_step _ _ _ _ |- _ ] =>
        eapply wtxn_step_assgn2 in H; eauto; subst
    end.
    repeat (match goal with
            | _ => solve [ pred_apply; cancel ]
            | _ => eapply ptsto_upd
            | _ => rotate1
            end).

    repeat match goal with
           | [ H: wtxn_error _ _ |- _ ] =>
             inversion H; subst; clear H; repeat inj_pair2
           end.
    assert (Sigma.mem st (var1 txn) = Some (val a0)).
    eapply ptsto_valid'; pred_apply; cancel.
    congruence.
    assert (Sigma.mem st (var2 txn) = Some (val b0)).
    eapply ptsto_valid'; pred_apply; cancel.
    congruence.
  Qed.

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
                           Sigma.l sigma' = Sigma.l sigma /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
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
                           r = v /\
                           Sigma.init_disk sigma' = Sigma.init_disk sigma; |})
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
                                 sigma'' = Sigma.set_init_disk (Sigma.set_l sigma' WriteLock) (Sigma.disk sigma') /\
                                 hashmap_le (Sigma.hm sigma) (Sigma.hm sigma''); |})
                 GetWriteLock.
  Proof.
    prim.
    eexists; intuition eauto.
    destruct sigma'; simpl; eauto.
    destruct sigma'; simpl; eauto.
  Qed.

  Theorem Unlock_ok : forall tid,
      cprog_spec G tid
                 (fun F sigma =>
                    {| precondition :=
                         F (Sigma.mem sigma) /\
                         Sigma.l sigma = WriteLock /\
                         (forall sigma',
                             F (Sigma.mem sigma') ->
                             Sigma.disk sigma' = Sigma.disk sigma ->
                             Sigma.init_disk sigma' = Sigma.disk sigma ->
                             Sigma.hm sigma' = Sigma.hm sigma ->
                             Sigma.l sigma' = Free ->
                             G tid sigma sigma');
                       postcondition :=
                         fun sigma' _ =>
                           F (Sigma.mem sigma') /\
                           Sigma.disk sigma' = Sigma.disk sigma /\
                           Sigma.hm sigma' = Sigma.hm sigma /\
                           Sigma.l sigma' = Free /\
                           Sigma.init_disk sigma' = Sigma.disk sigma'; |})
                 Unlock.
  Proof.
    prim.
    destruct st; simpl; auto.
    destruct st; simpl; auto.
    destruct st; simpl in *; eauto.
  Qed.

End Primitives.

Hint Extern 0 {{ BeginRead _; _ }} => apply BeginRead_ok : prog.
Hint Extern 0 {{ WaitForRead _; _ }} => apply WaitForRead_ok : prog.
Hint Extern 0 {{ Write _ _; _ }} => apply Write_ok : prog.
Hint Extern 0 {{ Alloc _; _ }} => apply Alloc_ok : prog.
Hint Extern 0 {{ Read2 _ _ _ _; _ }} => apply Read2_ok : prog.
Hint Extern 0 {{ Assgn1 _ _; _ }} => apply Assgn1_ok : prog.
Hint Extern 0 {{ Assgn2_abs _; _ }} => apply Assgn2_abs_ok : prog.
Hint Extern 0 {{ Hash _; _ }} => apply Hash_ok : prog.
Hint Extern 0 {{ GetWriteLock; _ }} => apply GetWriteLock_ok : prog.
Hint Extern 0 {{ Unlock; _ }} => apply Unlock_ok : prog.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
