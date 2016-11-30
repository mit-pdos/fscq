Require Import Prog.
Require Import Word AsyncDisk.
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
      repeat deex; intuition idtac;
        try congruence.
    inversion H; subst; eauto.
    apply ListUtils.incl_in_nil in H2; subst; eauto.
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
  destruct out, out'; intros; simpl in *; repeat deex; try congruence; eauto;
    match goal with
    | [ H: @eq (outcome _) _ _ |- _ ] =>
      inversion H; subst; eauto
    end.
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
    specialize (IHR2 _ ltac:(eauto)); deex.
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
    inversion H4; subst.
    (* m ---> m0, m0 ~~> d', d' ---> out' <= out *)
    eapply exec_eq_sync_later in H3; eauto; deex.
    simpl in *; deex.
    assert (possible_sync (AEQ:=addr_eq_dec) d d') by eauto.
    eapply exec_eq_sync_later in H1; eauto; deex.
    apply outcome_obs_ge_ok in H8.
    eauto.
  - destruct out'; simpl in *; repeat deex; try congruence.
    eauto.
  - destruct out'; simpl in *; repeat deex; try congruence.
    inversion H1; subst.
    eexists; intuition eauto.
    simpl; eauto.
Qed.

Module ExecRecover.

  Inductive R
            {exec: forall T, rawdisk -> hashmap -> prog T -> outcome T -> Prop}
            {possible_crash: rawdisk -> rawdisk -> Prop}
            (TF TR: Type)
  : rawdisk -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m hm p1 p2,
      exec _ m hm p1 (Failed TF)
      -> R m hm p1 p2 (RFailed TF TR)
  | XRFinished : forall m hm p1 p2 m' hm' (v: TF),
      exec _ m hm p1 (Finished m' hm' v)
      -> R m hm p1 p2 (RFinished TR m' hm' v)
  | XRCrashedFailed : forall m hm p1 p2 m' hm' m'r,
      exec _ m hm p1 (Crashed TF m' hm')
      -> possible_crash m' m'r
      -> R (TF:=TR) m'r hm' p2 p2 (RFailed TR TR)
      -> R m hm p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR),
      exec _ m hm p1 (Crashed TF m' hm')
      -> possible_crash m' m'r
      -> R (TF:=TR) m'r hm' p2 p2 (RFinished TR m'' hm'' v)
      -> R m hm p1 p2 (RRecovered TF m'' hm'' v)
  | XRCrashedRecovered : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR),
      exec _ m hm p1 (Crashed TF m' hm')
      -> possible_crash m' m'r
      -> R (TF:=TR) m'r hm' p2 p2 (RRecovered TR m'' hm'' v)
      -> R m hm p1 p2 (RRecovered TF m'' hm'' v).

End ExecRecover.

Arguments ExecRecover.R exec possible_crash {TF TR} _ _ _ _ _.

Definition routcome_disk_R (R: rawdisk -> rawdisk -> Prop)
           TF TR (out out': recover_outcome TF TR) :=
  match out with
  | RFinished _ d hm v => exists d', out' = RFinished _ d' hm v /\
                               R d d'
  | RRecovered _ d hm v => exists d', out' = RRecovered _ d' hm v /\
                                R d d'
  | RFailed _ _ => out' = RFailed _ _
  end.

Definition routcome_disk_R_conv (R: rawdisk -> rawdisk -> Prop)
           TF TR (out' out: recover_outcome TF TR) :=
  match out' with
  | RFinished _ d hm v => exists d', out = RFinished _ d' hm v /\
                               R d' d
  | RRecovered _ d hm v => exists d', out = RRecovered _ d' hm v /\
                                R d' d
  | RFailed _ _ => out = RFailed _ _
  end.

Theorem routcome_disk_R_conv_ok : forall R TF TR (out out': recover_outcome TF TR),
    routcome_disk_R R out out' <->
    routcome_disk_R_conv R out' out.
Proof.
  split;
    destruct out, out'; simpl; intros;
      repeat deex;
      match goal with
      | [ H: @eq (recover_outcome _ _) _ _ |- _ ] =>
        inversion H; subst
      end; eauto.
Qed.

Hint Constructors ExecRecover.R exec_recover.

Theorem exec_recover_is_R : forall TF TR d hm (p: prog TF) (r: prog TR) out,
    exec_recover d hm p r out <->
    ExecRecover.R exec possible_crash d hm p r out.
Proof.
  split; induction 1; eauto.
Qed.

Theorem exec_recover_without_sync : forall TF TR d hm (p: prog TF) (r: prog TR) out,
    ExecRecover.R (@Exec.R possible_sync) possible_crash d hm p r out ->
    exists out', ExecRecover.R (@Exec.R eq) possible_crash d hm p r out' /\
            routcome_disk_R possible_sync out' out.
Proof.
  induction 1; simpl;
    repeat match goal with
           | [ H: Exec.R possible_sync _ _ _ _ |- _ ] =>
             apply exec_sync_obs_irrelevant in H; simpl in H
           | [ H: outcome_obs_le _ _ |- _ ] =>
             apply outcome_obs_ge_ok in H; progress simpl in H
           | [ H: routcome_disk_R _ _ _ |- _ ] =>
             apply routcome_disk_R_conv_ok in H; progress simpl in H
           | [ H: possible_sync ?m ?m',
                  H': possible_crash ?m' ?m'' |- _ ] =>
             learn that (possible_crash_possible_sync_trans H H')
           | _ => progress subst
           | _ => deex
           end;
    try solve [ eexists; intuition eauto; simpl; eauto ].
Qed.

Module PhysicalSemantics.

  (* we will now _re-interpret_ a valubuf as the following:

     a |-> (v, vs) means v is the current value while the disk contains the
     sequence of values vs, where the last value is on disk and the earlier
     values are buffered. *)

  (* partially flush each address by removing some old values and leaving a new
  value on disk *)
  Definition flush_disk (d d': rawdisk) :=
    forall a,
      match d a with
      | None => d' a = None
      | Some (v, vs) => exists n, d' a = Some (v, firstn n vs)
      end.

  Theorem flush_disk_refl : forall d, flush_disk d d.
  Proof.
    unfold flush_disk; intros.
    destruct matches.
    exists (length l).
    rewrite firstn_all.
    eauto.
  Qed.

  Theorem flush_disk_trans : forall d d' d'',
      flush_disk d d' ->
      flush_disk d' d'' ->
      flush_disk d d''.
  Proof.
    unfold flush_disk; intros.
    specialize (H a).
    specialize (H0 a).
    destruct matches in *; repeat deex; try congruence.
    rewrite H3 in H.
    inversion H.
    subst.
    replace (d'' a).
    rewrite firstn_firstn.
    eauto.
  Qed.

  Lemma firstn_incl : forall A (l: list A) n,
      incl (firstn n l) l.
  Proof.
    unfold incl.
    apply ListUtils.in_firstn_in.
  Qed.

  Hint Resolve firstn_incl.

  Theorem flush_disk_is_sync : forall d d',
      flush_disk d d' ->
      possible_sync (AEQ:=addr_eq_dec) d d'.
  Proof.
    unfold flush_disk, possible_sync; intros.
    specialize (H a).
    destruct (d a); eauto.
    right.
    destruct p; deex; eauto 10.
  Qed.

  Hint Resolve flush_disk_is_sync.

  (* with the new interpretation of valusets, the last value in (v, vs),
  organized as v::vs, is the on-disk value *)
  Fixpoint diskval (v: valu) (vs: list valu) :=
    match vs with
    | nil => v
    | v'::vs' => diskval v' vs'
    end.

  (* discard buffers is actually a function  *)
  Definition discard_buffers (d d': rawdisk) :=
    forall a, match d a with
         | None => d' a = None
         | Some (v, vs) =>
           d' a = Some (diskval v vs, nil)
         end.

  Lemma discard_buffers_f (d: rawdisk) : {d':rawdisk | discard_buffers d d'}.
  Proof.
    unfold discard_buffers.
    exists (fun a =>
         match d a with
         | None => None
         | Some (v, vs) =>
           Some (diskval v vs, nil)
         end).
    intros.
    destruct (d a); auto.
    destruct p; auto.
  Qed.

  Remark discard_buffers_deterministic : forall d d' d'',
      discard_buffers d d' ->
      discard_buffers d d'' ->
      d' = d''.
  Proof.
    unfold discard_buffers; intros.
    extensionality a.
    specialize (H a).
    specialize (H0 a).
    destruct matches in *; eauto.
  Qed.

  Definition outcome_disk_R (R: rawdisk -> rawdisk -> Prop) T (out out':outcome T) :=
    match out with
    | Finished d hm v => exists d', out' = Finished d' hm v /\
                              R d d'
    | Crashed _ d hm => exists d', out' = Crashed _ d' hm /\
                           R d d'
    | Failed _ => out' = Failed _
    end.

  Definition pexec T d hm (p: prog T) out :=
    exists out', Exec.R flush_disk d hm p out' /\
          outcome_disk_R flush_disk out' out.
  Definition pexec_recover := @ExecRecover.R pexec discard_buffers.

  Hint Resolve flush_disk_refl flush_disk_trans.
  Hint Resolve flush_disk_is_sync.

  Lemma flush_disk_in_domain : forall d d' a v vs,
      d a = Some (v, vs)  ->
      flush_disk d d' ->
      exists n, d' a = Some (v, firstn n vs).
  Proof.
    unfold flush_disk; intros.
    specialize (H0 a).
    simpl_match; eauto.
  Qed.

  Theorem outcome_obs_le_to_R : forall T (out out': outcome T),
      outcome_obs_le out out' <->
      outcome_disk_R possible_sync out out'.
  Proof.
    unfold outcome_obs_le, outcome_disk_R; split; intros;
      destruct matches in *; eauto.
  Qed.

  (* We want to prove that using the non-deterministic crash (our actual
  semantics) is sufficient for safety under the real, deterministic crash +
  non-deterministic flush (the above semantics). This is guaranteed by proving
  if exec_real -> (exists out, exec_fake to out) -> exec_real's out is
  similar *)

  (* similarity is vague - want all the values to match for correctness, and to
  get proof to go through need the write buffers in the real execution to be
  sensible *)

  Lemma exec_flush_to_exec : forall T (p: prog T) d hm out,
      Exec.R flush_disk d hm p out ->
      exec d hm p out.
  Proof.
    induction 1; simpl; intros; destruct_ands;
      repeat deex; intuition eauto 10.
  Qed.

  Corollary pexec_to_exec : forall T (p: prog T) d hm out,
      pexec d hm p out ->
      exists out', exec d hm p out' /\
              outcome_disk_R flush_disk out' out.
  Proof.
    unfold pexec; intros; deex.
    eauto using exec_flush_to_exec.
  Qed.

  Definition outcome_disk_R_conv (R: rawdisk -> rawdisk -> Prop)
             T (out' out: outcome T) :=
   match out' with
   | Finished m hm v => exists m', out = Finished m' hm v /\
                               R m' m
   | Crashed _ m hm => exists m', out = Crashed _ m' hm /\
                            R m' m
   | Failed _ => out = Failed  _
   end.

  Theorem outcome_disk_R_conv_ok : forall R T (out out': outcome T),
      outcome_disk_R R out out' <->
      outcome_disk_R_conv R out' out.
  Proof.
    unfold outcome_disk_R, outcome_disk_R_conv; split; intros;
      destruct out, out'; repeat deex; try congruence.
    inversion H; eauto.
    inversion H; eauto.
    inversion H; eauto.
    inversion H; eauto.
  Qed.


  Lemma diskval_firstn_in_list : forall l n v,
      In (diskval v (firstn n l)) (v::l).
  Proof.
    induction l; simpl; intros.
    rewrite firstn_nil; eauto.
    destruct n; simpl; eauto.
    destruct (IHl n a); simpl; eauto.
  Qed.

  Theorem discard_flush_is_crash : forall d d' d'',
      flush_disk d d' ->
      discard_buffers d' d'' ->
      possible_crash d d''.
  Proof.
    unfold flush_disk, discard_buffers, possible_crash; intros.
    specialize (H a).
    specialize (H0 a).
    destruct matches in *; repeat deex; try congruence.
    right.
    rewrite H1 in H.
    inversion H; subst.
    repeat eexists; intuition eauto.
    apply diskval_firstn_in_list.
  Qed.

  Hint Constructors exec_recover.

  Theorem pexec_recover_to_exec_recover : forall TF TR (p: prog TF) (r: prog TR) d hm out,
      pexec_recover d hm p r out ->
      exists out', exec_recover d hm p r out' /\
              routcome_disk_R possible_sync out' out.
  Proof.
    induction 1; simpl;
      repeat match goal with
             | [ H: pexec _ _ _ _ |- _ ] =>
               apply pexec_to_exec in H; simpl in H; deex
             | [ H: outcome_disk_R _ _ _ |- _ ] =>
               apply outcome_disk_R_conv_ok in H; progress simpl in H
             | [ H: routcome_disk_R _ _ _ |- _ ] =>
               apply routcome_disk_R_conv_ok in H; progress simpl in H
             | [ H: flush_disk ?d ?d',
                    H' : discard_buffers ?d' ?d'' |- _ ] =>
               learn that (discard_flush_is_crash H H')
             | _ => progress subst
             | _ => deex
             end;
      try solve [ eexists; intuition eauto; simpl; eauto ].
  Qed.

End PhysicalSemantics.