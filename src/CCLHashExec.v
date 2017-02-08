Require Import CCLProg.
Require Import Hashmap.
Require Import Automation.

Theorem exec_hashmap_le : forall St T (p: @cprog St T)
                            G tid sigma_i sigma out,
    exec G tid (sigma_i, sigma) p out ->
    match out with
    | Finished _ sigma' _ => hashmap_le (Sigma.hm sigma) (Sigma.hm sigma')
    | Error => True
    end.
Proof.
  intros.
  remember (sigma_i, sigma).
  generalize dependent sigma.
  generalize dependent sigma_i.
  induction H; intros;
    match goal with
    | [ H: (_,_) = (_,_) |- _ ] =>
      inversion H; subst; clear H
    end; auto.
  - reflexivity.
  - CCLTactics.inv_step; subst; repeat inj_pair2;
      repeat match goal with
             | [ sigma: Sigma St |- _ ] => destruct sigma; simpl
             end;
      try reflexivity.
    unfold hashmap_le.
    eexists.
    econstructor; eauto.
    constructor.
  - destruct out; eauto.
    etransitivity; eauto.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)