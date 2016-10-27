Require Import FunctionalExtensionality.
Require Import Structures.OrderedType.
Require Import Structures.OrderedTypeEx.
Require Import Omega.
Require Import List.
Require Import Mem.
Require Import PredCrash.
Require Import AsyncDisk.
Require Import Word.
Require Automation.

Import ListNotations.

Set Implicit Arguments.

(** * The programming language *)

(** single program *)
Inductive prog : Type -> Type :=
  | Ret T (v: T) : prog T
  | Read (a: addr) : prog valu
  | Write (a: addr) (v: valu) : prog unit
  | Sync : prog unit
  | Trim (a: addr) : prog unit
  | Hash (sz: nat) (buf: word sz) : prog (word hashlen)
  | Bind T T' (p1: prog T) (p2: T -> prog T') : prog T'.

Arguments Ret {T} v.

Inductive outcome (T : Type) :=
  | Failed
  | Finished (m: rawdisk) (hm: hashmap) (v: T)
  | Crashed (m: rawdisk) (hm: hashmap).

Inductive step : forall T,
    rawdisk -> hashmap -> prog T ->
    rawdisk -> hashmap -> T -> Prop :=
| StepRead : forall m a v x hm,
    m a = Some (v, x) ->
    step m hm (Read a) m hm v
| StepWrite : forall m a v v0 x hm,
    m a = Some (v0, x) ->
    step m hm (Write a v) (upd m a (v, v0 :: x)) hm tt
| StepSync : forall m hm,
    step m hm (Sync) (sync_mem m) hm tt
| StepTrim : forall m a vs vs' hm,
    m a = Some vs ->
    step m hm (Trim a) (upd m a vs') hm tt
| StepHash : forall m sz (buf : word sz) h hm,
    hash_safe hm h buf ->
    hash_fwd buf = h ->
    step m hm (Hash buf) m (upd_hashmap' hm h buf) h.

Inductive fail_step : forall T,
    rawdisk -> prog T -> Prop :=
| FailRead : forall m a,
    m a = None ->
    fail_step m (Read a)
| FailWrite : forall m a v,
    m a = None ->
    fail_step m (Write a v).

Inductive crash_step : forall T, prog T -> Prop :=
| CrashRead : forall a,
    crash_step (Read a)
| CrashWrite : forall a v,
    crash_step (Write a v).

Module StepPresync.

  Import Automation.

  Hint Constructors step.
  Hint Resolve possible_sync_trans.
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
      intuition eauto.
      eapply possible_sync_trans; eauto.
      destruct vs'.
      eapply possible_sync_respects_upd; eauto.
    - exists m; intuition eauto.
  Qed.
End StepPresync.

Module ExecSync.

  Inductive exec {sync_R: rawdisk -> rawdisk -> Prop} : forall T, rawdisk -> hashmap -> prog T -> outcome T -> Prop :=
  | XRet : forall T m hm (v: T),
      exec m hm (Ret v) (Finished m hm v)
  | XStep : forall T m hm (p: prog T) m' m'' hm' v,
      step m hm p m' hm' v ->
      sync_R m' m'' ->
      exec m hm p (Finished m'' hm' v)
  | XBindFinish : forall m hm T (p1: prog T) m' hm' (v: T)
                    T' (p2: T -> prog T') out,
      exec m hm p1 (Finished m' hm' v) ->
      exec m' hm' (p2 v) out ->
      exec m hm (Bind p1 p2) out
  | XBindFail : forall m hm T (p1: prog T)
                  T' (p2: T -> prog T'),
      exec m hm p1 (Failed T) ->
      exec m hm (Bind p1 p2) (Failed T')
  | XBindCrash : forall m hm T (p1: prog T) m' hm'
                   T' (p2: T -> prog T'),
      exec m hm p1 (Crashed T m' hm') ->
      exec m hm (Bind p1 p2) (Crashed T' m' hm')
  | XFail : forall m hm T (p: prog T),
      fail_step m p ->
      exec m hm p (Failed T)
  | XCrash : forall m hm T (p: prog T),
      crash_step p ->
      exec m hm p (Crashed T m hm).

  Arguments exec sync_R {T} _ _ _ _.

End ExecSync.

Require Import Automation.

Arguments possible_sync {AT AEQ} _ _.

Definition exec := @ExecSync.exec possible_sync.

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

Hint Resolve possible_sync_refl possible_sync_trans.

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

Hint Constructors ExecSync.exec.

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
    ExecSync.exec eq d' hm p out ->
    possible_sync d d' ->
    exists out', ExecSync.exec eq d hm p out' /\
            outcome_obs_ge out out'.
Proof.
  intros.
  generalize dependent d.
  induction H; subst; intros; simpl.
  - eexists; intuition eauto; simpl; eauto.
  - eapply step_sync_later in H0; eauto; deex.
    eexists; intuition eauto.
  - specialize (IHexec1 _ H1); deex.
    simpl in *; deex.
    specialize (IHexec2 _ H5); deex.
    eauto 10.
  - specialize (IHexec _ H0); deex.
    simpl in *; subst.
    eauto 10.
  - specialize (IHexec _ H0); deex.
    simpl in *; deex.
    eauto 10.
  - eapply fail_step_sync_later in H; eauto.
  - inversion H; subst; repeat sigT_eq; eauto 10.
Qed.

Theorem exec_sync_obs_irrelevant : forall T (p: prog T) d hm out,
    ExecSync.exec possible_sync d hm p out ->
    exists out', ExecSync.exec eq d hm p out' /\
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

(** program with recovery *)
Inductive recover_outcome (TF TR: Type) :=
  | RFailed
  | RFinished (m: rawdisk) (hm: hashmap) (v: TF)
  | RRecovered (m: rawdisk) (hm: hashmap) (v: TR).

Module ExecRecover.

Inductive exec_recover {exec: forall T, rawdisk -> hashmap -> prog T -> outcome T -> Prop} (TF TR: Type)
    : rawdisk -> hashmap -> prog TF -> prog TR -> recover_outcome TF TR -> Prop :=
  | XRFail : forall m hm p1 p2, exec _ m hm p1 (Failed TF)
    -> exec_recover m hm p1 p2 (RFailed TF TR)
  | XRFinished : forall m hm p1 p2 m' hm' (v: TF), exec _ m hm p1 (Finished m' hm' v)
    -> exec_recover m hm p1 p2 (RFinished TR m' hm' v)
  | XRCrashedFailed : forall m hm p1 p2 m' hm' m'r, exec _ m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover exec TR TR m'r hm' p2 p2 (RFailed TR TR)
    -> exec_recover m hm p1 p2 (RFailed TF TR)
  | XRCrashedFinished : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR), exec _ m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover exec TR TR m'r hm' p2 p2 (RFinished TR m'' hm'' v)
    -> exec_recover m hm p1 p2 (RRecovered TF m'' hm'' v)
  | XRCrashedRecovered : forall m hm p1 p2 m' hm' m'r m'' hm'' (v: TR), exec _ m hm p1 (Crashed TF m' hm')
    -> possible_crash m' m'r
    -> @exec_recover exec TR TR m'r hm' p2 p2 (RRecovered TR m'' hm'' v)
    -> exec_recover m hm p1 p2 (RRecovered TF m'' hm'' v).

Arguments exec_recover exec {TF TR} _ _ _ _ _.

End ExecRecover.

Definition exec_recover := @ExecRecover.exec_recover exec.

Hint Constructors ExecRecover.exec_recover.

Definition rout_obs_le TF TR (out out': recover_outcome TF TR) :=
 match out with
 | RFailed _ _ => out' = RFailed _ _
 | RFinished _ m hm v => exists m', out' = RFinished _ m' hm v /\
                            possible_sync (AEQ:=addr_eq_dec) m m'
 | RRecovered _ m hm v => exists m', out' = RRecovered _ m' hm v /\
                             possible_sync (AEQ:=addr_eq_dec) m m'
 end.

Theorem exec_recover_obs_refinement : forall TF TR (p: prog TF) (r: prog TR)
                                        d hm (P: recover_outcome TF TR -> Prop),
    (forall d hm v d' hm' v', P (RFinished TR d hm v) ->
                         outcome_obs_le (Finished d hm v) (Finished d' hm' v') ->
                         P (RFinished TR d' hm' v')) ->
    (forall out, ExecRecover.exec_recover (@ExecSync.exec eq) d hm p r out -> P out) ->
    (forall out, ExecRecover.exec_recover (@ExecSync.exec possible_sync) d hm p r out -> P out).
Proof.
  intros.
  induction H1; subst;
  repeat match goal with
         | [ H: ExecSync.exec possible_sync _ _ _ _ |- _ ] =>
           apply exec_sync_obs_irrelevant in H; deex
         | [ H: outcome_obs_le _ _ |- _ ] =>
           apply outcome_obs_ge_ok in H; simpl in H
         | _ => progress subst
         | _ => deex
         end.
  - eauto.
  - eapply H; eauto.
    simpl; eauto.
  - apply H0; eauto.
    econstructor 3; eauto.
    eapply possible_crash_possible_sync_trans; eauto.
    admit. (* not clear if induction hypothesis can prove this *)
  - apply H0; eauto.
    econstructor 4; eauto.
    eapply possible_crash_possible_sync_trans; eauto.
    admit. (* similar induction hypothesis-based goal *)
  - apply H0; eauto.
    econstructor 5; eauto.
    eapply possible_crash_possible_sync_trans; eauto.
    admit. (* again same *)
Abort.

Hint Constructors GeneralExec.exec.
Hint Constructors step.
Hint Constructors exec_recover.

(** program notations *)

Definition pair_args_helper (A B C:Type) (f: A->B->C) (x: A*B) := f (fst x) (snd x).
Notation "^( a )" := (pair a tt).
Notation "^( a , .. , b )" := (pair a .. (pair b tt) .. ).

Notation "p1 ;; p2" := (Bind p1 (fun _: unit => p2)) (at level 60, right associativity).
Notation "x <- p1 ; p2" := (Bind p1 (fun x => p2)) (at level 60, right associativity,
                                                 format "'[v' x  <-  p1 ; '/' p2 ']'").
Notation "'let^' ( a ) <- p1 ; p2" :=
  (Bind p1
    (pair_args_helper (fun a (_:unit) => p2))
  )
  (at level 60, right associativity, a ident,
   format "'[v' let^ ( a )  <-  p1 ; '/' p2 ']'").

Notation "'let^' ( a , .. , b ) <- p1 ; p2" :=
  (Bind p1
    (pair_args_helper (fun a => ..
      (pair_args_helper (fun b (_:unit) => p2))
    ..))
  )
    (at level 60, right associativity, a closed binder, b closed binder,
     format "'[v' let^ ( a , .. , b )  <-  p1 ; '/' p2 ']'").