Require Import CCLProg.
Require Import Hashmap.
Require Import Automation.

Section HashExec.

  Hint Resolve hashmap_le_refl.

  Theorem hashmap_le_upd : forall sigma sz (w: Word.word sz),
      AsyncDisk.hash_safe (Sigma.hm sigma) (AsyncDisk.hash_fwd w) w ->
      hashmap_le (Sigma.hm sigma) (Sigma.hm (Sigma.upd_hm sigma w)).
  Proof.
    destruct sigma; simpl; intros.
    unfold AsyncDisk.upd_hashmap'.
    unfold hashmap_le.
    eexists; eauto.
    econstructor.
    constructor.
    eauto.
  Qed.

  Hint Resolve hashmap_le_upd.

  Theorem exec_hashmap_le : forall T (p: cprog T)
                              G tid sigma out,
      exec G tid sigma p out ->
      match out with
      | Finished sigma' _ => hashmap_le (Sigma.hm sigma) (Sigma.hm sigma')
      | Error => True
      end.
  Proof.
    intros.
    generalize dependent sigma.
    induction 1; intros; auto;
      repeat match goal with
             | [ x := _ |- _ ] => subst x
             | [ |- hashmap_le (Sigma.hm _) (Sigma.hm _) ] =>
               repeat match goal with
                      | [ sigma: Sigma |- _ ] => destruct sigma
                      end; simpl in *; reflexivity
             | _ => progress CCLTactics.inv_guarantee
             | _ => solve [ auto ]
             end.
    - destruct sigma.
      destruct p;
        repeat match goal with
               | [ H: context[match ?d with | _ => _ end] |- _ ] =>
                 destruct d
               | [ H: StepTo _ _ = StepTo _ _ |- _ ] =>
                 inversion H; subst; clear H
               | _ => progress simpl in *
               | _ => auto; congruence
               end.
    - destruct out; eauto.
      etransitivity; eauto.
    - destruct sigma'; simpl in *.
      eauto.
    - destruct (local_l tid (Sigma.l sigma)); intuition (subst; eauto).
  Qed.

End HashExec.

(* Local Variables: *)
(* company-coq-local-symbols: (("Sigma" . ?Σ) ("sigma" . ?σ) ("sigma'" . (?σ (Br . Bl) ?'))) *)
(* End: *)
