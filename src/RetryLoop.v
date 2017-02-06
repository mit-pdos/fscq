Require Import CCLProg.
Require Import CCLHoareTriples.
Require Import Automation.

Section RetryLoop.

  Context {St:StateTypes}.
  Variable G:Protocol St.

  Fixpoint retry_n {T P Q} (guard: forall (v:T), {P v}+{Q v}) (p: @cprog St T) n :=
    match n with
    | 0 => p
    | S n' => v <- p;
               if guard v then
                 Ret v
               else
                 retry_n guard p n'
    end.

  CoFixpoint retry {T P Q} (guard: forall (v:T), {P v}+{Q v}) (p: @cprog St T) :=
    v <- p; if guard v then Ret v else retry guard p.

  Definition prog_id T (p: @cprog St T) : cprog T :=
    match p with
    | Get => Get
    | Assgn m => Assgn m
    | GhostUpdate update => GhostUpdate update
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
                    (exists n, exec G tid st (retry_n guard p n) out) /\
                    match out with
                    | Finished _ _ v => exists H, guard v = left H
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
        exists 0; simpl; eauto.
      + rewrite retry_unfold in IHexec2.
        specialize (IHexec2 _ _ guard p); intuition.
        deex.
        exists (S n); simpl.
        eapply ExecBindFinish; eauto.
        simpl_match; eauto.
    - inversion Heqc; repeat inj_pair2.
      intuition.
      exists 0; eauto.
  Qed.

  Theorem retry_triple : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p
                         A (spec: Spec A T) tid,
      (forall n, cprog_triple G tid spec (retry_n guard p n)) ->
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
    eapply H in H1; eauto.
    destruct out; intuition eauto.
  Qed.

  Corollary retry_spec : forall T P Q (guard: forall (v:T), {P v}+{Q v}) p
                         A (spec: Spec A T) tid,
      (forall n, cprog_spec G tid spec (retry_n guard p n)) ->
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
    apply retry_triple; intros.
    apply triple_spec_equiv.
    auto.
  Qed.

End RetryLoop.