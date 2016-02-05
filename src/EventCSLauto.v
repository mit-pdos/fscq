Require Import EventCSL.
Require Import FunctionalExtensionality.
Require Import Automation.
Require Import Star.
Import Bool.

Set Implicit Arguments.

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
      }} Read a.
  Proof.
    intros.
    step.
    exists (diskIs (mem_except d a)).
    eexists; intuition; subst; eauto.

    step.
    repeat match goal with
           | [ |- exists _, _ ] => eexists
           end; intuition eauto.

    step.
    apply diskIs_combine_same in H2.
    unfold diskIs in H2; auto.
    eexists.
    pred_apply; cancel.
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
    }} StartRead_upd a.
Proof.
  intros.
  step.
  exists (diskIs (mem_except d a)).
  eexists; intuition eauto.

  step.
  eapply diskIs_combine_upd in H; unfold diskIs in H.
  auto.
Qed.

End ReadTheorems.

Hint Extern 1 {{Read _; _}} => apply Read_ok : prog.
Hint Extern 1 {{StartRead_upd _; _}} => apply StartRead_upd_ok : prog.

Section WaitForCombinator.

CoFixpoint wait_for {T} {Mcontents} {Scontents}
           tv (v: var Mcontents tv) (test: tv -> bool)
  rx : prog Mcontents Scontents T :=
  val <- Get v;
  If (bool_dec (test val) true) {
    rx tt
  } else {
    Yield;;
    wait_for v test rx
  }.

(* dummy function that will trigger computation of cofix *)
Definition prog_frob Mcontents Scontents T (p: prog Mcontents Scontents T) :=
  match p with
  | StartRead a rx => StartRead a rx
  | FinishRead a rx => FinishRead a rx
  | Write a v rx => Write a v rx
  | Sync a rx => Sync a rx
  | Get v rx => Get v rx
  | Assgn v val rx => Assgn v val rx
  | GetTID rx => GetTID rx
  | AcquireLock l update rx => AcquireLock l update rx
  | Yield rx => Yield rx
  | GhostUpdate update rx => GhostUpdate update rx
  | Done _ _ v => Done _ _ v
  end.

Theorem prog_frob_eq : forall Mcontents Scontents T (p: prog Mcontents Scontents T),
    p = prog_frob p.
Proof.
  destruct p; reflexivity.
Qed.

Theorem wait_for_expand : forall Mcontents Scontents T
                               tv (v: var Mcontents tv) test
                               (rx : _ -> prog Mcontents Scontents T),
    wait_for v test rx =
    val <- Get v;
    If (bool_dec (test val) true) {
         rx tt
       } else {
    Yield;;
         wait_for v test rx
  }.
Proof.
  intros.
  match goal with
  | [ |- ?p1 = ?p2 ] =>
    rewrite (prog_frob_eq p1) at 1;
    rewrite (prog_frob_eq p2) at 1
  end; cbn.
  auto.
Qed.

Ltac sigT_eq :=
  match goal with
  | [ H: @eq (sigT _) _ _ |- _ ] =>
    apply ProofIrrelevance.ProofIrrelevanceTheory.EqdepTheory.inj_pair2 in H;
      subst
  end.

Ltac inv_step :=
  match goal with
  | [ H: step _ _ _ _ _ _ _ |- _ ] =>
    inversion H; subst; repeat sigT_eq
  end.

Ltac inv_st :=
  match goal with
  | [ H : @eq state _ _ |- _ ] =>
    inversion H
  end.

Ltac inv_tuple :=
  match goal with
  | [ H : (_, _, _, _) = (_, _, _, _) |- _ ] =>
    inversion H; subst
  end.

Ltac inv_prog :=
  match goal with
  | [ H: @eq (prog _ _ _) _ _ |- _ ] =>
    inversion H
  end.

Ltac inv_fail_step :=
  match goal with
  | [ H: context[fail_step] |- _ ] =>
    inversion H; subst;
    (* produce equalities from dependent equalities using proof
      irrelevance *)
    repeat sigT_eq;
    (* get rid of local definitions in context *)
    repeat match goal with
           | [ v := _ : _ |- _ ] => subst v
           end
  end.

Ltac ind_exec :=
  match goal with
  | [ H : exec _ _ _ ?st ?p _ |- _ ] =>
    remember st; remember p;
    induction H; subst;
    try (destruct st; inv_st);
    try inv_tuple;
    try inv_step;
    try inv_prog;
    intuition (subst; eauto)
  end.

Hint Constructors exec.

Theorem wait_for_ok : forall Mcontents Scontents
                        (R: ID -> Relation Scontents)
                        (Inv: Invariant Mcontents Scontents)
                        tv (v: var Mcontents tv) test
                        (R_stutter: forall tid s, R tid s s),
  (Build_transitions R Inv) TID: tid |-
    {{ (_:unit),
     | PRE d m s0 s:
       Inv m s d /\
       R tid s0 s
     | POST d' m' s0' s' r:
       Inv m' s' d' /\
       test (get v m') = true /\
       ((s0 = s0' /\ s' = s) \/
        (star (StateR' R tid) s s0' /\ s' = s0'))
    }} wait_for v test.
Proof.
  intros; cbn.
  unfold valid.
  intros.
  rewrite wait_for_expand in H0.
  repeat deex; intuition.

  match goal with
  | [ H: exec _ _ _ ?st ?p _ |- _ ] =>
    remember p
  end.

  remember (d, m, s0, s) as st.
  generalize dependent d.
  generalize dependent m.
  generalize dependent s0.
  generalize dependent s.
  generalize dependent st.
  induction 1 using exec_ind2; intros; subst.

  - inv_step.

    intuition.
    deex.
    unfold If_ in *.
    destruct (bool_dec (test (get v m)) true); try solve [ inv_prog ].
    eapply H2; [| eauto ]. intuition.
    unfold If_ in *.
    destruct (bool_dec (test (get v m)) true); try solve [ inv_prog ].
    eapply H2; [| eauto ]. intuition.
    inv_fail_step; congruence.

  - inv_step.
    unfold If_ in *.
    match goal with
    | [ H: step _ _ _ _ (if ?d then _ else _) _ _ |- _ ] =>
      destruct d
    end.
    eapply H2; [| eauto ]. intuition.
    inversion H0; repeat sigT_eq; subst.

    eapply IHexec.
    apply wait_for_expand.
    3: eauto.
    all: eauto.
    intros; intuition.
    eapply H2; [| eauto ]. subst. intuition.
    eapply H2; [| eauto ]. subst. intuition.

    right; intuition.
    eapply star_trans; eauto.

  - inv_fail_step.
  - inv_prog.
Qed.

End WaitForCombinator.

Hint Extern 1 {{ wait_for _ _; _ }} => apply wait_for_ok : prog.
