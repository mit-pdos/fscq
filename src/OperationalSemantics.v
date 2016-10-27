Require Import Prog.
Require Import AsyncDisk.
Require Import Mem Pred PredCrash.
Require Import Automation.

Require Import FunctionalExtensionality.
Require Import List.
Require Import Arith.PeanoNat.
Require Import RelationClasses.

Set Implicit Arguments.

Arguments possible_sync {AT AEQ} _ _.
Hint Resolve possible_sync_refl.
Hint Resolve possible_sync_trans.

Section StepPreSync.
Arguments possible_sync {AT AEQ} _ _.
  Hint Constructors step.
  Hint Resolve ListUtils.incl_cons2.

  Theorem possible_sync_after_sync : forall A AEQ (m m': @mem A AEQ _),
      possible_sync (sync_mem m) m' ->
      m' = sync_mem m.
  Proof.
    unfold possible_sync, sync_mem; intros.
    extensionality a.
    specialize (H a).
    destruct matches in *; intuition eauto;
      repeat deex;
      try congruence.
    inversion H1; subst; eauto.
    apply ListUtils.incl_in_nil in H3; subst; eauto.
  Qed.

  Lemma possible_sync_respects_upd : forall A AEQ (m m': @mem A AEQ _)
                                       a v l l',
      possible_sync m m' ->
      incl l' l ->
      possible_sync (upd m a (v, l)) (upd m' a (v,l')).
  Proof.
    unfold possible_sync; intros.
    destruct (AEQ a a0); subst; autorewrite with upd;
      intuition eauto.
    specialize (H a0); intuition auto.
    right; repeat eexists; eauto.
    repeat deex.
    right; repeat eexists; eauto.
  Qed.

  Hint Resolve incl_refl.

  Lemma possible_sync_respects_sync_mem : forall A AEQ (m m': @mem A AEQ _),
      possible_sync m m' ->
      possible_sync (sync_mem m) (sync_mem m').
  Proof.
    unfold possible_sync, sync_mem; intros.
    specialize (H a).
    destruct matches; subst; intuition eauto;
      try congruence;
      repeat deex;
      right;
      cleanup.
    do 3 eexists; intuition eauto.
  Qed.

  Hint Resolve possible_sync_respects_upd.
  Hint Resolve possible_sync_respects_sync_mem.

  Theorem step_presync : forall T (m m' m'' m''': rawdisk) hm (p: prog T) hm' v,
      possible_sync (AEQ:=Nat.eq_dec) m m' ->
      step m' hm p m'' hm' v ->
      possible_sync (AEQ:=Nat.eq_dec) m'' m''' ->
      exists (m'2: rawdisk),
        step m hm p m'2 hm' v /\
        possible_sync (AEQ:=Nat.eq_dec) m'2 m'''.
  Proof.
    intros.
    inversion H0; subst; repeat sigT_eq; cleanup.
    - exists m; intuition eauto.
      specialize (H a); intuition auto; repeat deex; try congruence.
      assert (v = v0) by congruence; subst.
      eauto.
    - pose proof (H a); intuition auto; try congruence.
      repeat deex.
      cleanup.
      exists (upd m a (v0, v::l)).
      intuition eauto.
    - exists (sync_mem m).
      intuition eauto.
    - pose proof (H a); intuition auto; try congruence.
      repeat deex.
      cleanup.
      exists (upd m a vs').
      destruct vs'.
      intuition eauto.
    - exists m; intuition eauto.
  Qed.
End StepPreSync.

Module Exec.

  Inductive R {sync_R: rawdisk -> rawdisk -> Prop} : forall T, rawdisk -> hashmap -> prog T -> outcome T -> Prop :=
  | XRet : forall T m hm (v: T),
      R m hm (Ret v) (Finished m hm v)
  | XStep : forall T m hm (p: prog T) m' m'' hm' v,
      step m hm p m' hm' v ->
      sync_R m' m'' ->
      R m hm p (Finished m'' hm' v)
  | XBindFinish : forall m hm T (p1: prog T) m' hm' (v: T)
                    T' (p2: T -> prog T') out,
      R m hm p1 (Finished m' hm' v) ->
      R m' hm' (p2 v) out ->
      R m hm (Bind p1 p2) out
  | XBindFail : forall m hm T (p1: prog T)
                  T' (p2: T -> prog T'),
      R m hm p1 (Failed T) ->
      R m hm (Bind p1 p2) (Failed T')
  | XBindCrash : forall m hm T (p1: prog T) m' hm'
                   T' (p2: T -> prog T'),
      R m hm p1 (Crashed T m' hm') ->
      R m hm (Bind p1 p2) (Crashed T' m' hm')
  | XFail : forall m hm T (p: prog T),
      fail_step m p ->
      R m hm p (Failed T)
  | XCrash : forall m hm T (p: prog T),
      crash_step p ->
      R m hm p (Crashed T m hm).

  Arguments R sync_R {T} _ _ _ _.
End Exec.

Hint Constructors Exec.R.
Hint Constructors exec.

Theorem exec_is_exec_possible_sync : forall T (p: prog T) m hm out,
    exec m hm p out <->
    Exec.R possible_sync m hm p out.
Proof.
  split; induction 1; eauto.
Qed.

(* if out is ok, out' is at least as ok *)
Definition outcome_obs_le T (out out': outcome T) : Prop :=
  match out with
  | Failed _ => out' = Failed T
  | Finished d hm v => exists d', out' = Finished d' hm v /\
                            possible_sync (AEQ:=addr_eq_dec) d d'
  | Crashed _ d hm => exists d', out' = Crashed T d' hm /\
                         possible_sync (AEQ:=addr_eq_dec) d d'
  end.

Definition outcome_obs_ge T (out' out: outcome T) : Prop :=
  match out' with
  | Failed _ => out = Failed T
  | Finished d' hm v => exists d, out = Finished d hm v /\
                             possible_sync (AEQ:=addr_eq_dec) d d'
  | Crashed _ d' hm => exists d, out = Crashed T d hm /\
                           possible_sync (AEQ:=addr_eq_dec) d d'
  end.

Theorem outcome_obs_ge_ok : forall T (out out': outcome T),
    outcome_obs_le out out' <->
    outcome_obs_ge out' out.
Proof.
  destruct out, out'; simpl; intuition idtac;
    repeat deex;
    match goal with
    | [ H: @eq (outcome _) _ _ |- _ ] => inversion H; subst
    end; eauto.
Qed.

Theorem outcome_obs_le_refl : forall T (out: outcome T),
    outcome_obs_le out out.
Proof.
  destruct out; simpl; eauto.
Qed.

Theorem outcome_obs_le_trans : forall T (out out' out'': outcome T),
    outcome_obs_le out out' ->
    outcome_obs_le out' out'' ->
    outcome_obs_le out out''.
Proof.
  destruct out, out'; intros; simpl in *; repeat deex; try congruence; eauto.
  inversion H0; subst; eauto.
  inversion H0; subst; eauto.
Qed.

Instance outcome_obs_le_preorder {T} : PreOrder (outcome_obs_le (T:=T)).
Proof.
  constructor; hnf; intros; eauto using outcome_obs_le_refl, outcome_obs_le_trans.
Qed.

Hint Resolve outcome_obs_le_refl outcome_obs_le_trans.

Lemma possible_sync_in_domain : forall AT AEQ (d d': @mem AT AEQ _) a v vs',
    possible_sync d d' ->
    d' a = Some (v, vs') ->
    exists vs, d a = Some (v, vs) /\
          incl vs' vs.
Proof.
  unfold possible_sync; intros.
  specialize (H a); intuition eauto; try congruence.
  repeat deex.
  assert (v = v0) by congruence; subst.
  assert (l' = vs') by congruence; subst.
  eauto.
Qed.

Hint Resolve ListUtils.incl_cons2.
Hint Resolve incl_refl.
Hint Resolve possible_sync_respects_sync_mem.

Lemma step_sync_later : forall T (p: prog T) d d' d'' hm hm' v,
    possible_sync d d' ->
    step d' hm p d'' hm' v ->
    exists d'2, step d hm p d'2 hm' v /\
           possible_sync (AEQ:=addr_eq_dec) d'2 d''.
Proof.
  intros.
  inversion H0; subst; repeat sigT_eq.
  - (* Read *)
    eapply possible_sync_in_domain in H8; eauto; deex.
    eauto.
  - eapply possible_sync_in_domain in H8; eauto; deex.
    eexists; split.
    constructor; eauto.
    eapply possible_sync_respects_upd; eauto.
  - eauto.
  - destruct vs, vs'.
    eapply possible_sync_in_domain in H8; eauto; deex.
    eexists; split.
    econstructor; eauto.
    eapply possible_sync_respects_upd; eauto.
  - eauto.
Qed.

Lemma possible_sync_not_in_domain : forall AT AEQ (d d': @mem AT AEQ _) a,
    possible_sync d d' ->
    d' a = None ->
    d a = None.
Proof.
  unfold possible_sync; intros.
  specialize (H a); intuition eauto;
    repeat deex; congruence.
Qed.

Hint Resolve possible_sync_not_in_domain.
Hint Constructors fail_step.

Lemma fail_step_sync_later  : forall T (p: prog T) d d',
    fail_step d' p ->
    possible_sync d d' ->
    fail_step d p.
Proof.
  inversion 1; intros; subst; repeat sigT_eq; eauto.
Qed.

Theorem exec_eq_sync_later : forall T (p: prog T) d d' hm out,
    Exec.R eq d' hm p out ->
    possible_sync d d' ->
    exists out', Exec.R eq d hm p out' /\
            outcome_obs_ge out out'.
Proof.
  intros.
  generalize dependent d.
  induction H; subst; intros; simpl.
  - eexists; intuition eauto; simpl; eauto.
  - eapply step_sync_later in H0; eauto; deex.
    eexists; intuition eauto.
  - specialize (IHR1 _ H1); deex.
    simpl in *; deex.
    specialize (IHR2 _ H5); deex.
    eauto 10.
  - specialize (IHR _ H0); deex.
    simpl in *; subst.
    eauto 10.
  - specialize (IHR _ H0); deex.
    simpl in *; deex.
    eauto 10.
  - eapply fail_step_sync_later in H; eauto.
  - inversion H; subst; repeat sigT_eq; eauto 10.
Qed.

Theorem exec_sync_obs_irrelevant : forall T (p: prog T) d hm out,
    Exec.R possible_sync d hm p out ->
    exists out', Exec.R eq d hm p out' /\
            outcome_obs_le out' out.
Proof.
  induction 1; intros; repeat deex; eauto.
  - eexists; intuition eauto.
    simpl.
    eauto.
  - destruct out'0; simpl in *; repeat deex; try congruence.
    inversion H5; subst.
    (* m ---> m0, m0 ~~> d', d' ---> out' <= out *)
    eapply exec_eq_sync_later in H4; eauto; deex.
    simpl in *; deex.
    assert (possible_sync (AEQ:=addr_eq_dec) d d') by eauto.
    eapply exec_eq_sync_later in H1; eauto; deex.
    apply outcome_obs_ge_ok in H9.
    eauto.
  - destruct out'; simpl in *; repeat deex; try congruence.
    eauto.
  - destruct out'; simpl in *; repeat deex; try congruence.
    inversion H2; subst.
    eexists; intuition eauto.
    simpl; eauto.
Qed.