Require Import CCLProg.
Require Import CCLHoareTriples.
Require Import CCLAutomation.
Require Import Automation.

Section RetryLoop.

  Variable G:Protocol.

  Fixpoint retry_n {T P Q} (guard: forall (v:T), {P v}+{Q v}) (v0: T) (p: cprog T) n :=
    match n with
    | 0 => Ret v0
    | S n' => v <- p;
               if guard v then
                 Ret v
               else
                 retry_n guard v0 p n'
    end.

  CoFixpoint retry {T P Q} (guard: forall (v:T), {P v}+{Q v}) (p: cprog T) :=
    v <- p; if guard v then Ret v else retry guard p.

  Definition prog_id T (p: cprog T) : cprog T.
    remember p as p'.
    destruct p; match type of Heqp' with
                | _ = ?p => exact p
                end.
  Defined.

  Lemma prog_id_eq : forall T (p: cprog T),
      p = prog_id p.
  Proof.
    destruct p; auto.
  Qed.

  Lemma retry_unfold : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p,
      retry guard p =
      v <- p; if guard v then Ret v else retry guard p.
  Proof.
    intros.
    match goal with
    | [ |- ?p = _ ] =>
      rewrite (prog_id_eq p) at 1; simpl
    end.
    auto.
  Qed.

  Theorem retry_exec : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p,
      forall tid st out, exec G tid st (retry guard p) out ->
                    (exists n, forall v0, exec G tid st (retry_n guard v0 p n) out) /\
                    match out with
                    | Finished _ v => exists H, guard v = left H
                    | Error => True
                    end.
  Proof.
    intros.
    remember (retry guard p); rewrite retry_unfold in *.
    induction H; simpl; subst;
      try (rewrite retry_unfold in *;
           solve [ congruence ||
                              CCLTactics.inv_step ]).
    inversion Heqc; repeat inj_pair2.
    - case_eq (guard v); intros; replace (guard v) in *.
      + CCLTactics.inv_ret.
        intuition eauto.
        exists 1; intros; simpl.
        eapply ExecBindFinish; eauto.
        replace (guard v0).
        eapply ExecRet; eauto.
      + rewrite retry_unfold in IHexec2.
        specialize (IHexec2 _ _ guard p); intuition.
        deex.
        exists (S n); intros; simpl.
        eapply ExecBindFinish; eauto.
        simpl_match; eauto.
    - inversion Heqc; repeat inj_pair2.
      intuition.
      exists 1; simpl; intros.
      eapply ExecBindFail; eauto.
  Qed.

  Theorem retry_triple : forall T P Q (guard: forall (v:T), {P v}+{Q v}) v0 p
                         A (spec: Spec A T) tid,
      (forall n, cprog_triple G tid spec (retry_n guard v0 p n)) ->
      cprog_triple G tid (fun a st =>
                            {| precondition := precondition (spec a st);
                               postcondition :=
                                 fun st' v =>
                                   postcondition (spec a st) st' v /\
                                   exists H, guard v = left H |})
                   (retry guard p).
  Proof.
    unfold cprog_triple; intros; simpl in *.
    apply retry_exec in H1; intuition; repeat deex.
    specialize (H1 v0).
    eapply H in H1; eauto.
    destruct out; intuition eauto.
  Qed.

  Theorem retry_triple' : forall T P Q (guard: forall (v:T), {P v}+{Q v}) v0 p
                         A (spec: Spec A T) tid,
      (forall n, cprog_triple G tid spec (retry_n guard v0 p n)) ->
      cprog_triple G tid spec (retry guard p).
  Proof.
    intros.
    unfold cprog_triple; intros; simpl in *.
    apply retry_exec in H1; intuition; repeat deex.
    specialize (H1 v0).
    eapply H in H1; eauto.
  Qed.

  Definition invariant A T {P Q} (guard: forall (v:T), {P v}+{Q v})
             (spec: Spec A T) :=
    forall a st st' r,
      postcondition (spec a st) st' r ->
      (exists H, guard r = right H) ->
      precondition (spec a st').

  Definition postcondition_trans A T {P Q} (guard: forall (v:T), {P v}+{Q v})
             (spec: Spec A T) :=
    forall a st st' st'' r r',
      postcondition (spec a st) st' r ->
      (exists H, guard r = right H) ->
      postcondition (spec a st') st'' r' ->
      postcondition (spec a st) st'' r'.

  Theorem retry_invariant_triple : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p
                              A (spec: Spec A T) tid,
      invariant guard spec ->
      postcondition_trans guard spec ->
      cprog_triple G tid spec p ->
      cprog_triple G tid spec (retry guard p).
  Proof.
    unfold invariant, postcondition_trans; intros;
      unfold cprog_triple; intros.
    generalize dependent a.
    remember (retry guard p); rewrite retry_unfold in *.
    induction H3; intros; simpl; subst;
      try (rewrite retry_unfold in *;
           solve [ congruence ||
                              CCLTactics.inv_step ]).
    - inversion Heqc; repeat inj_pair2.
      case_eq (guard v); intros; replace (guard v) in *.
      + CCLTactics.inv_ret.
        match goal with
        | [ Hexec: exec _ _ _ p _ |- _ ] =>
          eapply H1 in Hexec; eauto
        end.
      + rewrite retry_unfold in IHexec2.
        specialize (IHexec2 _ _ guard p spec); intuition.
        match goal with
        | [ Hexec: exec _ _ _ p _ |- _ ] =>
          eapply H1 in Hexec; eauto
        end.
        destruct out; eauto 10.
    - inversion Heqc; repeat inj_pair2.
      match goal with
      | [ Hexec: exec _ _ _ p _ |- _ ] =>
        eapply H1 in Hexec; eauto
      end.
  Qed.

  Theorem retry_invariant_spec : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p
                              A (spec: Spec A T) tid,
      invariant guard spec ->
      postcondition_trans guard spec ->
      cprog_spec G tid spec p ->
      cprog_spec G tid spec (retry guard p).
  Proof.
    intros.
    apply triple_spec_equiv.
    apply triple_spec_equiv in H1.
    auto using retry_invariant_triple.
  Qed.

  Corollary retry_spec : forall T P Q (guard: forall (v:T), {P v}+{Q v}) v0 p
                         A (spec: Spec A T) tid,
      (forall n, cprog_spec G tid spec (retry_n guard v0 p n)) ->
      cprog_spec G tid (fun a st =>
                            {| precondition := precondition (spec a st);
                               postcondition :=
                                 fun st' v =>
                                   postcondition (spec a st) st' v /\
                                   exists H, guard v = left H |})
                 (retry guard p).
  Proof.
    intros.
    apply triple_spec_equiv.
    eapply retry_triple; intros.
    apply triple_spec_equiv.
    auto.
  Qed.

  Theorem retry_upgrade_spec : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p
                                 A (spec: Spec A T) tid,
      cprog_spec G tid spec (retry guard p) ->
      cprog_spec G tid (fun a sigma =>
                          {| precondition := precondition (spec a sigma);
                             postcondition :=
                               fun sigma' v =>
                                 postcondition (spec a sigma) sigma' v /\
                                 exists H, guard v = left H |})
                 (retry guard p).
  Proof.
    intros.
    apply triple_spec_equiv in H.
    apply triple_spec_equiv.
    unfold cprog_triple in *; simpl; intros.
    match goal with
      | [ Hexec: exec _ _ _ (retry _ _) _ |- _ ] =>
        pose proof Hexec;
          eapply retry_exec in Hexec; intuition eauto
    end.
    match goal with
      | [ Hexec: exec _ _ _ (retry _ _) _ |- _ ] =>
        eapply H in Hexec; eauto
    end.
    destruct out; eauto.
  Qed.

  Corollary retry_spec' : forall T P Q (guard: forall (v:T), {P v}+{Q v}) v0 p
                         A (spec: Spec A T) tid,
      (forall n, cprog_spec G tid spec (retry_n guard v0 p n)) ->
      cprog_spec G tid spec (retry guard p).
  Proof.
    intros.
    intros.
    apply triple_spec_equiv.
    eapply retry_triple'; intros.
    apply triple_spec_equiv.
    auto.
  Qed.

  Theorem retry_n_induction : forall T P Q (guard : forall (v:T), {P v}+{Q v}) v0 p
                                A (spec: Spec A T) tid,
      cprog_spec G tid spec (Ret v0) ->
      cprog_spec G tid spec p ->
      (forall a sigma r sigma' H, postcondition (spec a sigma) sigma' r ->
                     guard r = right H ->
                     precondition (spec a sigma')) ->
      (forall a sigma0 sigma r sigma' r' H, postcondition (spec a sigma0) sigma r ->
                               guard r = right H ->
                               postcondition (spec a sigma) sigma' r' ->
                               postcondition (spec a sigma0) sigma' r') ->
      (forall n, cprog_spec G tid spec (retry_n guard v0 p n)).
  Proof.
    intros.
    induction n; simpl; eauto.
    unfold cprog_spec; intros.
    eapply cprog_ok_weaken; [ monad_simpl; now eauto | ].
    intros; deex.
    descend; intuition eauto.
    destruct (guard r) eqn:?.
    - eapply cprog_ok_weaken; [ monad_simpl; now eauto | ].
      intuition subst.
    - eapply cprog_ok_weaken; [ monad_simpl; now eauto | ].
      intuition subst.
      descend; intuition eauto.

      eapply cprog_ok_weaken; [ monad_simpl; now eauto | ].
      intuition eauto.
  Qed.

End RetryLoop.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
