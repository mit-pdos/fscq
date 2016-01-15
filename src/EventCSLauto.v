Require Import EventCSL.
Require Import FunctionalExtensionality.
Require Import Automation.

Ltac inv_opt :=
  match goal with
  | [ H: None = Some _ |- _ ] =>
    now (inversion H)
  | [ H: Some _ = None |- _ ] =>
    now (inversion H)
  | [ H: Some _ = Some _ |- _ ] =>
    inversion H; subst; clear H
  | [ H: None = None |- _ ] =>
    clear H
  end.

Ltac econtradiction H :=
  exfalso; eapply H.

(* extract the precondition of a valid statement into the hypotheses *)
Ltac intros_pre :=
  unfold valid at 1; unfold pred_in; intros;
  repeat deex.

Ltac destruct_ands :=
  repeat match goal with
         | [ H: _ /\ _ |- _ ] =>
           destruct H
         end.

Ltac split_ands :=
  destruct_ands; repeat (split; intros).

(* simplify the postcondition obligation to its components *)
Ltac simpl_post :=
  cbn; unfold pred_in;
  split_ands;
  repeat deex.

(* Captures a program in a type so the hypotheses can give the program that
  produced each proof obligation. *)
Inductive CurrentProg {Mcontents} {Scontents} {T}
  (p: prog Mcontents Scontents T) :=
| SomeProg.

Local Ltac set_prog p :=
  repeat match goal with
  | [ H: CurrentProg _ |- _ ] => clear H
  end;
  let H := fresh "PreOf" in
  pose proof (SomeProg p) as H.

Ltac next_control_step :=
    match goal with
    | [ |- valid _ _ _ _ ?p ] =>
      eapply pimpl_ok; [ now (auto with prog) | set_prog p  ]
    end.

Ltac head_symbol e :=
  lazymatch e with
  | ?h _ _ _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ _ => h
  | ?h _ _ _ _ _ => h
  | ?h _ _ _ _ => h
  | ?h _ _ _ => h
  | ?h _ _ => h
  | ?h _ => h
  | ?h => h
  end.

Ltac unfold_prog :=
  lazymatch goal with
  | [ |- valid _ _ _ _ ?p ] =>
    let program := head_symbol p in
    unfold program
  end.

Ltac valid_match_ok :=
  match goal with
  | [ |- valid _ _ _ _ (match ?d with | _ => _ end) ] =>
    case_eq d; intros
  end.

Ltac step' simplifier finisher :=
  repeat (autounfold with prog);
  next_control_step ||
                    (unfold_prog; next_control_step) ||
                    valid_match_ok;
  repeat (autounfold with prog);
  simplifier;
  finisher.

Ltac unfold_pred_applications :=
  unfold pred_in; intros; repeat deex.

Ltac step_simplifier :=
  unfold_pred_applications;
  simpl_post;
  try subst.

Ltac simpl_goal :=
  repeat match goal with
         | [ |- _ /\ _ ] => split
         | [ |- forall _, _ ] => intros
         end.

Ltac step_finisher :=
  simpl_goal;
  try solve [ pred_apply; cancel ];
  eauto.

Tactic Notation "step" := step' step_simplifier step_finisher.
Tactic Notation "step" "pre" tactic(simplifier) := step' simplifier step_finisher.
Tactic Notation "step" "pre" tactic(simplifier) "with" tactic(finisher) := step' simplifier finisher.
Tactic Notation "step" "with" tactic(finisher) := step' step_simplifier finisher.

Ltac hoare' simplifier finisher  := intros; repeat step' simplifier finisher.
Tactic Notation "hoare" := hoare' step_simplifier step_finisher.
Tactic Notation "hoare" "pre" tactic(simplifier) := hoare' simplifier step_finisher.
Tactic Notation "hoare" "pre" tactic(simplifier) "with" tactic(finisher) := hoare' simplifier finisher.
Tactic Notation "hoare" "with" tactic(finisher) := hoare' step_simplifier finisher.

Definition Read {Mcontents} {Scontents} {T} a rx : prog Mcontents Scontents T :=
  StartRead a;;
            v <- FinishRead a;
  rx v.

Section ReadTheorems.

  Lemma diskIs_combine_same'_applied
     : forall AT AEQ V a v (m d : @mem AT AEQ V),
      m a = Some v ->
      diskIs m d ->
      (diskIs (mem_except m a) * a |-> v)%pred d.
  Proof.
    intros.
    apply diskIs_combine_same'; auto.
  Qed.

  Lemma diskIs_same : forall AT AEQ V (d: @mem AT AEQ V),
      diskIs d d.
  Proof.
    unfold diskIs; auto.
  Qed.

  Hint Resolve
       diskIs_combine_same'_applied
       diskIs_combine_upd
       diskIs_same.

  Hint Resolve ptsto_valid ptsto_valid'.

  Lemma clean_readers_upd : forall m a v0 reader reader',
      m a = Some (v0, reader) ->
      clean_readers (upd m a (v0, reader')) = clean_readers m.
  Proof.
    intros.
    unfold clean_readers, upd; extensionality a'.
    destruct matches.
  Qed.

  Lemma clean_readers_upd' : forall m a v0 reader reader',
      m a = Some (v0, reader) ->
      clean_readers m = clean_readers (upd m a (v0, reader')).
  Proof.
    intros.
    erewrite clean_readers_upd; eauto.
  Qed.

  Hint Resolve clean_readers_upd.

  Theorem Read_ok : forall Mcontents Scontents Inv R a,
      (@Build_transitions Mcontents Scontents Inv R) TID: tid |-
      {{ F vs0,
       | PRE d m s0 s: d |= F * a |-> (vs0, None)
       | POST d' m' s0' s' r: d' = d /\
                              s0' = s0 /\
                              s' = s /\
                              m' = m /\
                              r = latest_valu vs0
       | CRASH d'c : clean_readers d'c = clean_readers d
      }} Read a.
  Proof.
    intros.
    step.
    exists (diskIs (mem_except d a)).
    repeat eexists; intuition; subst; eauto.

    step.
    repeat eexists; intuition eauto.

    step.
    apply diskIs_combine_same in H3.
    unfold diskIs in H3; auto.
    eexists.
    pred_apply; cancel.

    eapply diskIs_combine_upd in H1.
    unfold diskIs in H1; subst.
    eauto.
  Qed.


Definition StartRead_upd {Mcontents} {Scontents} {T} a rx : prog Mcontents Scontents T :=
  StartRead a;;
            rx tt.

Theorem StartRead_upd_ok : forall Mcontents Scontents Inv R a,
    (@Build_transitions Mcontents Scontents Inv R) TID: tid |-
    {{ vs0,
     | PRE d m s0 s: d a = Some (vs0, None)
     | POST d' m' s0' s' _: d' = upd d a (vs0, Some tid) /\
                            s0' = s0 /\
                            s' = s /\
                            m' = m
     | CRASH d'c : d'c = d
    }} StartRead_upd a.
Proof.
  intros.
  step.
  exists (diskIs (mem_except d a)).
  eexists; intuition eauto.

  step.
  eapply diskIs_combine_upd in H1; unfold diskIs in H1.
  auto.
Qed.

End ReadTheorems.

Hint Extern 1 {{Read _; _}} => apply Read_ok : prog.
Hint Extern 1 {{StartRead_upd _; _}} => apply StartRead_upd_ok : prog.