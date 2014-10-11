Require Import Hoare.
Require Import Prog.
Require Import Pred.
Require Import SepAuto.
Require Import Classical_Prop.

Definition preserves_precondition (pre : pred) p :=
  forall m m' out, pre m -> exec m p m' out -> pre m' /\ out <> Failed.

Theorem pp_exists : forall p T pre, (forall (x:T), preserves_precondition (pre x) p)
  -> preserves_precondition (exists (x:T), pre x) p.
Proof.
  unfold preserves_precondition; intros.
  destruct H0.
  edestruct H; eauto.
  split; eauto.
  eexists; eauto.
Qed.

Theorem pp_add_lift : forall pre P p, preserves_precondition pre p
  -> preserves_precondition (pre * [[ P ]]) p.
Proof.
  unfold preserves_precondition; intros.
  apply sep_star_lift2and in H0; destruct H0.
  edestruct H; clear H; eauto.
  intuition.
  apply sep_star_and2lift.
  split; eauto.
Qed.

Theorem pp_drop_lift : forall pre (P : Prop) p, P
  -> preserves_precondition (pre * [[ P ]]) p
  -> preserves_precondition pre p.
Proof.
  unfold preserves_precondition; intros.
  edestruct H0; clear H0; eauto.
  apply sep_star_and2lift. split; eauto.
  apply sep_star_lift2and in H3; destruct H3.
  eauto.
Qed.

Theorem idempotent_ok' : forall p p1 p2 pre, preserves_precondition pre p
  -> p1 = Check pre ;; p
  -> p2 = Check pre ;; p
  -> {{ pre }} p1 >> p2.
Proof.
  unfold corr at 1.
  intros.

  match goal with
  | [ H: exec_recover _ _ _ _ _ |- _ ] => induction H; subst; auto
  end.

  - inversion H3; subst.
    edestruct H; eauto; congruence.
    rewrite check_id_ok in *; congruence.
  - inversion H3; subst; eauto.
    edestruct H; eauto.
Qed.

Theorem idempotent_ok : forall p pre, preserves_precondition pre p
  -> {{ pre }} Check pre ;; p >> Check pre ;; p.
Proof.
  intros.
  eapply idempotent_ok'; eauto.
Qed.

Theorem check_to_post : forall p1 p2 pre id, {{ pre }} p1 >> CheckID id ;; p2
  -> forall m m' out, pre m -> exec m p1 m' out -> check_cond id m'.
Proof.
  unfold corr; intros.
  destruct out.
  - assert (Failed = Finished); eauto. discriminate.
  - assert (exec m p1 m' Crashed) by (eapply prog_can_crash; eauto); clear H1.
    assert (exists p, p = CheckID id ;; p2) as Hp by eauto. destruct Hp.
    assert (exists p, p = CheckID id ;; p2) as Hp by eauto. destruct Hp.
    destruct (exec_recover_can_terminate x x0 m').
    destruct H4.
    induction H4; subst.
    + assert (Failed = Finished); eauto. discriminate.
    + inversion H4; eauto.
    + inversion H4; subst; eauto.
  - assert (exists p, p = CheckID id ;; p2) as Hp by eauto. destruct Hp.
    assert (exists p, p = CheckID id ;; p2) as Hp by eauto. destruct Hp.
    destruct (exec_recover_can_terminate x x0 m').
    destruct H4.
    induction H4; subst.
    + assert (Failed = Finished); eauto. discriminate.
    + inversion H4; eauto.
    + inversion H4; subst; eauto.
Qed.

Hint Resolve check_to_post.

Theorem corr_to_pp : forall p1 p2 pre1 pre2id, {{ pre1 }} p1 >> CheckID pre2id ;; p2
  -> (pre1 ==> pre1 * [[ check_cond pre2id ==> pre1 ]])
  -> preserves_precondition pre1 p1.
Proof.
  unfold preserves_precondition.
  intros.
  unfold corr in H.
  apply H0 in H1 as Hcheck.
  apply sep_star_lift2and in Hcheck.
  unfold lift in *; destruct Hcheck.
  destruct out.
  - assert (Failed = Finished); [| discriminate ].
    eapply H; eauto.
  - split; try discriminate; eauto.
  - split; try discriminate; eauto.
Qed.

Theorem corr_drop_check1 : forall pre p1 p2 id, {{ pre }} CheckID id ;; p1 >> p2
  -> {{ pre }} p1 >> p2.
Proof.
  unfold corr; intros.
  eapply H; eauto.
  destruct (classic (check_cond id m)).
  - inversion H1; subst.
    + constructor.
      apply XCheckOK; eauto.
    + constructor.
      apply XCheckOK; eauto.
    + eapply XRCrashed.
      apply XCheckOK; eauto.
      eauto.
  - assert (Failed=Finished); try discriminate.
    eapply H; eauto.
    constructor.
    apply XCheckFail with (m':=m); eauto.
Qed.

Theorem corr_drop_check2 : forall pre p1 p2 id, {{ pre }} p1 >> CheckID id ;; p2
  -> {{ pre }} p1 >> p2.
Proof.
  unfold corr; intros.
  assert (forall m' out, exec_recover m p1 (CheckID id ;; p2) m' out -> out = Finished) by eauto.
  clear H H0.
  induction H1; eauto.
  apply IHexec_recover; clear IHexec_recover.
  intros.
  inversion H0; subst; eauto.
  - eapply H2.
    eapply XRCrashed; [eassumption|constructor].
    destruct (classic (check_cond id m')).
    apply XCheckOK; eauto.
    apply XCheckFail; eauto.
  - eapply H2.
    eapply XRCrashed; [eassumption|].
    econstructor; [|eauto].
    destruct (classic (check_cond id m')).
    apply XCheckOK; eauto.
    assert (Failed=Finished); try discriminate.
    eapply H2.
    eapply XRCrashed; [eassumption|].
    constructor.
    apply XCheckFail with (m':=m'); eauto.
Qed.

Theorem idempotent_nocheck_ok : forall p pre, preserves_precondition pre p
  -> {{ pre }} p >> p.
Proof.
  intros.
  eapply corr_drop_check2.
  eapply corr_drop_check1.
  apply idempotent_ok.
  eauto.
Qed.

(* Sketch of how we might prove recover's idempotence *)
Module RECOVER_SKETCH.

  Parameter recover : prog -> prog.
  Parameter log_intact : mem -> pred.
  Parameter recovered : mem -> pred.

  Axiom recover_base_ok : forall rx id rec,
    {{ exists m, log_intact m
     * [[ {{ log_intact m }} rec >> CheckID id ;; rec ]]
     * [[ {{ recovered m }} rx >> CheckID id ;; rec ]]
     * [[ check_cond id = log_intact m ]]
    }} recover rx >> CheckID id ;; rec.

  Theorem recover_preserves_1 : forall rx,
    preserves_precondition
      (exists m id rec, log_intact m
       * [[ check_cond id = log_intact m ]]
       * [[ {{ log_intact m }} rec >> CheckID id ;; rec ]]
       * [[ {{ recovered m }} rx >> CheckID id ;; rec ]])%pred
      (recover rx).
  Proof.
    intros.
    do 3 ( eapply pp_exists; intros ).
    eapply corr_to_pp.
    eapply pimpl_ok. apply recover_base_ok. cancel; try eassumption.
    cancel.
    cancel.
  Qed.

  Theorem recover_preserves_2 : forall rx,
    preserves_precondition
      (exists m rec, log_intact m
       * [[ {{ log_intact m }} rec >> Check (log_intact m) ;; rec ]]
       * [[ {{ recovered m }} rx >> Check (log_intact m) ;; rec ]])%pred
      (recover rx).
  Proof.
    intros.
    do 2 ( eapply pp_exists; intros ).
    unfold Check.
    eapply corr_to_pp.
    eapply pimpl_ok. apply recover_base_ok.
    cancel; try eassumption.
    rewrite check_id_ok; eauto.
    cancel.
    rewrite check_id_ok; cancel.
  Qed.

  Theorem recover_idempotent_ok_1 : forall rx,
    {{ exists m rec, log_intact m
     * [[ {{ log_intact m }} rec >> Check (log_intact m) ;; rec ]]
     * [[ {{ recovered m }} rx >> Check (log_intact m) ;; rec ]]
    }} recover rx >> recover rx.
  Proof.
    intros.
    apply idempotent_nocheck_ok.
    apply recover_preserves_2.
  Qed.

End RECOVER_SKETCH.
