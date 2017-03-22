Require Import CCLProg.
Require Import Hashmap.
Require Import Automation.

Local Lemma hm_upd : forall sigma up, Sigma.hm (Sigma.upd_disk sigma up) = Sigma.hm sigma.
Proof.
  destruct sigma; reflexivity.
Qed.

Theorem exec_hashmap_le : forall T (p: cprog T)
                            G tid d_i sigma out,
    exec G tid (ExecState d_i sigma) p out ->
    match out with
    | Finished (ExecState d_i' sigma') _ => hashmap_le (Sigma.hm sigma) (Sigma.hm sigma')
    | Error => True
    end.
Proof.
  intros.
  match goal with
  | [ H: exec _ _ ?st _ _ |- _ ] => remember st
  end.
  generalize dependent sigma.
  generalize dependent d_i.
  induction H; intros; auto; subst;
    repeat match goal with
           | [ x := _ |- _ ] => subst x
           | [ H: ExecState _ _ = ExecState _ _ |- _ ] =>
             inversion H; subst; clear H
           | [ |- hashmap_le (Sigma.hm _) (Sigma.hm _) ] =>
             repeat match goal with
                    | [ sigma: Sigma |- _ ] => destruct sigma
                    end; simpl in *; reflexivity
           end.
  - destruct sigma0.
    destruct p;
      repeat match goal with
             | [ H: context[match ?d with | _ => _ end] |- _ ] =>
               destruct d
             | [ H: StepTo _ _ = StepTo _ _ |- _ ] =>
               inversion H; subst; clear H
             | [ |- hashmap_le ?a ?a ] => reflexivity
             | _ => progress simpl in *
             | _ => progress rewrite hm_upd
             | _ => congruence
             end.
  - repeat match goal with
           | [ sigma: Sigma |- _ ] => destruct sigma; simpl in *
           end;
      try reflexivity;
      eauto.
    unfold hashmap_le.
    eexists.
    econstructor; eauto.
    constructor.
  - destruct out; eauto.
    specialize (IHexec1 _ _ ltac:(eauto)).
    destruct st'.
    specialize (IHexec2 _ _ ltac:(eauto)).
    destruct sigma0.
    etransitivity; eauto.
  - destruct sigma'; simpl in *.
    eauto.
  - inversion H0; subst; eauto.
    destruct sigma0; reflexivity.
  - destruct (Sigma.l sigma0); intuition eauto.
    subst; reflexivity.
  - inversion H1; subst; eauto.
    destruct sigma0; reflexivity.
Qed.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)