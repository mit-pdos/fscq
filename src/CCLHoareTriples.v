Require Import CCLProg CCLMonadLaws Automation.

Import CCLTactics.

Section HoareTriples.

  Variables G:Protocol.

  Record SpecParams T :=
    { precondition :  Prop;
      postcondition : (Sigma * Sigma) ->
                      T -> Prop }.

  Definition Spec A T := A -> (Sigma * Sigma) -> SpecParams T.

  Definition cprog_spec tid A T' (spec: Spec A T') (p: cprog T') :=
    forall T (rx: _ -> cprog T),
      cprog_ok G tid
               (fun st donecond =>
                  exists a, precondition (spec a st) /\
                       forall r, cprog_ok G tid
                                     (fun st' donecond_rx =>
                                        postcondition (spec a st) st' r /\
                                        donecond_rx = donecond) (rx r))
               (Bind p rx).

  Theorem cprog_ok_weaken : forall T tid (pre pre': _ -> _ -> Prop) (p: cprog T),
      cprog_ok G tid pre p ->
      (forall st donecond, pre' st donecond -> pre st donecond) ->
      cprog_ok G tid pre' p.
  Proof.
    intros.
    unfold cprog_ok; intros.
    apply H0 in H1.
    eapply H; eauto.
  Qed.

  (* this is really the natural interpretation of a triple, directly as a
  correctness statement - [cprog_spec] instead unquotes triple into a double
  (with an arbitrary continuation) and then uses the double-based correctness
  statement *)
  Definition cprog_triple A T tid (spec: Spec A T) (p: @cprog T) :=
    forall a st out,
      precondition (spec a st) ->
      exec G tid st p out ->
      match out with
      | Finished sigma_i' sigma' v => postcondition (spec a st) (sigma_i', sigma') v
      | Error => False
      end.

  Theorem triple_spec_equiv : forall A T tid (spec: Spec A T) (p: @cprog T),
      cprog_spec tid spec p <->
      cprog_triple tid spec p.
  Proof.
    unfold cprog_spec, cprog_triple.
    split; intros.
    - unfold cprog_ok at 1 in H.
      specialize (H _ Ret st).
      specialize (H (fun st' v => postcondition (spec a st) st' v)).
      specialize (H out).

      apply H.

      exists a; intuition eauto.
      unfold cprog_ok; intros.
      CCLTactics.inv_ret; intuition (subst; eauto).

      apply monad_right_id; auto.
    - unfold cprog_ok at 1; intros; repeat deex.
      CCLTactics.inv_bind.
      match goal with
      | [ Hexec: exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; intuition eauto
      end.
      match goal with
      | [ Hexec: exec _ _ _ (rx _) _ |- _ ] =>
        eapply H2 in Hexec; intuition eauto
      end.

      match goal with
      | [ Hexec: exec _ _ _ p _ |- _ ] =>
        eapply H in Hexec; intuition eauto
      end.
  Qed.

  Corollary spec_to_exec : forall tid A T (spec: Spec A T) a p,
      cprog_spec tid spec p ->
      forall st out,
      exec G tid st p out ->
      precondition (spec a st) ->
      match out with
        | Finished sigma_i' sigma' v =>
          postcondition (spec a st) (sigma_i', sigma') v
        | Error => False
      end.
  Proof.
    intros.
    destruct (triple_spec_equiv tid spec p); intuition.
    match goal with
    | [ H: cprog_triple _ _ _ |- _ ] => eapply H; eauto
    end.
  Qed.

End HoareTriples.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)