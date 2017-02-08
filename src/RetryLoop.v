Require Import CCLProg.
Require Import CCLHoareTriples.
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

  Definition prog_id T (p: cprog T) : cprog T :=
    match p with
    | Alloc v0 => Alloc v0
    | Get A i => Get A i
    | Assgn i v => Assgn i v
    | GhostUpdate i update => GhostUpdate i update
    | BeginRead a => BeginRead a
    | WaitForRead a => WaitForRead a
    | Write a v => Write a v
    | Hash buf => Hash buf
    | Yield => Yield
    | Ret v => Ret v
    | Bind p p' => Bind p p'
    end.

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
                              CCLTactics.inv_step ||
                              CCLTactics.inv_fail_step ]).
    inversion Heqc; repeat inj_pair2.
    - case_eq (guard v); intros; replace (guard v) in *.
      + CCLTactics.inv_ret.
        intuition eauto.
        exists 1; intros; simpl.
        eapply ExecBindFinish; eauto.
        replace (guard v).
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

End RetryLoop.