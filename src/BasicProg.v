Require Import Prog.
Require Import Pred.
Require Import Hoare.
Require Import SepAuto.

Set Implicit Arguments.


(** * Some helpful [prog] combinators and proofs *)

Ltac inv_option :=
  match goal with
  | [ H: Some _ = Some _ |- _ ] => inversion H; clear H; subst
  | [ H: ?a = Some ?b |- _ ] =>
    match goal with
    | [ H': a = Some ?c |- _ ] =>
      match b with
      | c => fail 1
      | _ => rewrite H in H'
      end
    end
  end.

Ltac inv_exec_recover :=
  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Ltac inv_exec :=
  match goal with
  | [ H: exec _ _ _ _ |- _ ] => inversion H; clear H; subst
  end.

Theorem read_ok:
  forall (a:addr) (rx:valu->prog) (rec:prog),
  {{ exists v F, a |-> v * F
   * [[{{ a |-> v * F }} (rx v) >> rec]]
   * [[{{ a |-> v * F }} rec >> rec]]
  }} Read a rx >> rec.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec_recover; auto; inv_exec.
  - apply ptsto_valid in H. congruence.
  - eapply H2. eauto.
    apply ptsto_valid in H. repeat inv_option.
    eauto.
  - eapply H2. eauto.
    apply ptsto_valid in H. repeat inv_option.
    eauto.
  - eapply H1; eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Read _) _ >> _) => apply read_ok : prog.

Theorem write_ok:
  forall (a:addr) (v:valu) (rx:unit->prog) (rec:prog),
  {{ exists v0 F, a |-> v0 * F
   * [[{{ a |-> v * F }} rx tt >> rec]]
   * [[{{ a |-> v * F \/ a |-> v0 * F }} rec >> rec]]
  }} Write a v rx >> rec.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  unfold lift in *; simpl in *.
  inv_exec_recover; auto; inv_exec.
  - apply ptsto_valid in H. congruence.
  - eapply H2. instantiate (1:=upd m a v).
    eapply ptsto_upd; eauto.
    eauto.
  - eapply H2. instantiate (1:=upd m a v).
    eapply ptsto_upd; eauto.
    eauto.
  - eapply H1; unfold or; eauto.
Qed.

Hint Extern 1 ({{_}} progseq (Write _ _) _ >> _) => apply write_ok : prog.

Definition If_ P Q (b : {P} + {Q}) (p1 p2 : prog) :=
  if b then p1 else p2.

Theorem if_ok:
  forall P Q (b : {P}+{Q}) p1 p2 rec,
  {{ exists pre, pre
   * [[{{ pre /\ [P] }} p1 >> rec]]
   * [[{{ pre /\ [Q] }} p2 >> rec]]
  }} If_ b p1 p2 >> rec.
Proof.
  unfold corr, exis; intros; repeat deex.
  repeat ( apply sep_star_lift2and in H; destruct H ).
  destruct b; intuition pred.
Qed.

Hint Extern 1 ({{_}} If_ _ _ _ >> _) => apply if_ok : prog.
Notation "'If' b { p1 } 'else' { p2 }" := (If_ b p1 p2) (at level 9, b at level 0).

Fixpoint For_ (L : Set) (f : nat -> L -> (L -> prog) -> prog)
              (i n : nat) (l : L)
              (nocrash : nat -> L -> pred)
              (crashed : pred)
              (rx: L -> prog) : prog :=
  match n with
    | O => rx l
    | S n' => l' <- (f i l); (For_ f (S i) n' l' nocrash crashed rx)
  end.

Theorem for_ok:
  forall (L : Set) f rx rec (nocrash : nat -> L -> pred) (crashed : pred)
         n i (li : L),
  {{ nocrash i li
   * [[forall m l, nocrash m l ==> crashed]]
   * [[forall m lm rxm,
      i <= m < n + i ->
      (forall lSm, {{ nocrash (S m) lSm }} (rxm lSm) >> rec) ->
      {{ nocrash m lm }} f m lm rxm >> rec]]
   * [[forall lfinal, {{ nocrash (n+i) lfinal }} (rx lfinal) >> rec]]
  }} (For_ f i n li nocrash crashed rx) >> rec.
Proof.
(*
  induction n.
  - intros.
    eapply pimpl_pre.
    + unfold pimpl; intuition pred.
    + unfold pimpl; pred.
  - intros.
    eapply pimpl_pre.
    + unfold pimpl; intuition pred.
      eapply H1; try omega.
      intros.
      eapply pimpl_ok.
      apply IHn.
      unfold pimpl; intuition pred.
      eapply H1; try omega; eauto.
      replace (n + S i) with (S (n + i)) by omega.
      eauto.
    + unfold pimpl; pred.
*)
  admit.
Qed.

Hint Extern 1 ({{_}} progseq (For_ _ _ _ _ _ _) _ >> _) => apply for_ok : prog.
Notation "'For' i < n 'Loopvar' l < l0 'Continuation' lrx 'Invariant' nocrash 'OnCrash' crashed 'Begin' body 'Rof'" :=
  (For_ (fun i l lrx => body)
        0 n l0
        (fun i l => nocrash%pred)
        (crashed%pred))
  (at level 9, i at level 0, n at level 0, lrx at level 0, l at level 0, l0 at level 0,
   body at level 9).
