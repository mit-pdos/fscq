Require Import Prog.
Require Import Mem Pred.
Require Import Word.
Require Import PredCrash.
Require Import AsyncDisk.

Set Implicit Arguments.

Hint Constructors fail_step step exec.

Definition buf_ne sz1 (buf1: word sz1) sz2 (buf2: word sz2)
  := forall (H: sz1 = sz2), eq_rect _ _ buf1 _ H <> buf2.

Lemma buf_ne_sz_same : forall sz (buf1 buf2: word sz),
    buf1 <> buf2 ->
    buf_ne buf1 buf2.
Proof.
  unfold buf_ne; intros.
  rewrite <- Eqdep_dec.eq_rect_eq_dec; auto.
  apply addr_eq_dec.
Qed.

Lemma buf_ne_sz_neq : forall sz1 sz2 (buf1: word sz1) (buf2: word sz2),
    sz1 <> sz2 ->
    buf_ne buf1 buf2.
Proof.
  unfold buf_ne; intros.
  congruence.
Qed.

Hint Resolve buf_ne_sz_same buf_ne_sz_neq.

Lemma possible_sync_refl : forall A AEQ (m: @mem A AEQ valuset),
    possible_sync m m.
Proof.
  unfold possible_sync; intros.
  destruct (m a).
  - right.
    destruct p.
    exists w, l, l; intuition auto.
    apply List.incl_refl.
  - left; auto.
Qed.

Hint Resolve possible_sync_refl.

Definition hash_safe_dec hm h sz (buf: word sz) : {hash_safe hm h buf} + {~hash_safe hm h buf}.
Proof.
  unfold hash_safe.
  case_eq (hashmap_get hm h); intros.
  destruct s.
  destruct (addr_eq_dec sz x); subst.
  destruct (weq buf w); subst.
  - (* hash is in hm with correct buffer *)
    eauto.
  - (* hash is in hm and buffers are same size, but unequal *)
    right; intro.
    intuition (try congruence).
    inversion H1.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; eauto.
    apply addr_eq_dec.
  - (* hash is in hm but buffers are not same size *)
    right; intro.
    intuition (try congruence).
  - (* new hash *)
    left; eauto.
Defined.

Inductive hashmap_wf : hashmap -> Prop :=
| empty_hashmap_wf : hashmap_wf empty_hashmap
| upd_hashmap_wf : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    hashmap_wf (upd_hashmap hm (hash_fwd buf) (existT _ _ buf)).

Lemma hashmap_wf_get : forall hm sz1 (buf1: word sz1) sz2 (buf2: word sz2),
    hashmap_wf hm ->
    hashmap_get hm (hash_fwd buf1) = Some (existT _ _ buf2) ->
    hash_fwd buf1 = hash_fwd buf2.
Proof.
  induction hm; intros.
  - unfold hashmap_get in H0.
    destruct (weq (hash_fwd buf1) default_hash); subst.
    inversion H0; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; subst.
    eauto.
    apply addr_eq_dec.
    congruence.
  - unfold hashmap_get in H0.
    destruct (weq (hash_fwd buf1) default_hash); subst.
    inversion H0; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H3; subst.
    eauto.
    apply addr_eq_dec.
    fold (hashmap_get hm (hash_fwd buf1)) in H0.
    inversion H; subst.
    destruct (weq (hash_fwd buf) (hash_fwd buf1)); eauto.
    inversion H0; subst.
    apply Eqdep_dec.inj_pair2_eq_dec in H4; subst.
    eauto.
    apply addr_eq_dec.
Qed.

Lemma de_morgan : forall (P Q:Prop),
    ~(P \/ Q) ->
    ~P /\ ~Q.
Proof.
  tauto.
Qed.

Theorem not_hash_safe_conflict : forall hm sz (buf: word sz),
    hashmap_wf hm ->
    ~hash_safe hm (hash_fwd buf) buf ->
    exists sz' (buf': word sz'),
      buf_ne buf buf' /\
      hash_fwd buf = hash_fwd buf'.
Proof.
  unfold hash_safe; intros.
  apply de_morgan in H0; intuition.
  case_eq (hashmap_get hm (hash_fwd buf)); intros;
    try solve [ exfalso; eauto ].
  destruct s.
  destruct (addr_eq_dec sz x); subst.
  destruct (weq buf w); subst.
  exfalso; eauto.
  exists _, w.
  apply hashmap_wf_get in H0; auto.
  exists _,  w.
  apply hashmap_wf_get in H0; eauto.
Qed.

Hint Constructors hashmap_wf.

Theorem exec_preserves_hashmap_wf : forall T (p: prog T) d vm hm d' vm' hm' v,
    hashmap_wf hm ->
    exec d vm hm p (Finished d' vm' hm' v) ->
    hashmap_wf hm'.
Proof.
  intros.
  remember (Finished d' vm' hm' v).
  generalize dependent d'.
  generalize dependent vm'.
  generalize dependent hm'.
  generalize dependent v.
  induction H0; intros;
    repeat match goal with
        | [ H: @eq (outcome _) _ _ |- _ ] =>
          inversion H; subst; clear H
           end; eauto.
  match goal with
  | [ H: step _ _ _ _ _ _ _ _ |- _ ] =>
    inversion H; subst; eauto
  end.
  unfold upd_hashmap'; eauto.
  unfold upd_hashmap'; eauto.
Qed.

Hint Resolve exec_preserves_hashmap_wf.
Hint Resolve tt.

(**
 * XXX [exec_progress] is no longer true because type equality is not
 * decidable for [VarGet].
 *)

(*
Theorem exec_progress : forall T (p: prog T) d hm,
    hashmap_wf hm ->
    (exists d' hm' v', exec d hm p (Finished d' hm' v')) \/
    (exec d hm p (Failed T)) \/
    (exists sz1 (buf1: word sz1) sz2 (buf2: word sz2),
        buf_ne buf1 buf2 /\
        hash_fwd buf1 = hash_fwd buf2).
Proof.
  induction p; intros.
  - eauto.
  - case_eq (d a); intros; eauto.
    destruct p.
    eauto 10.
  - case_eq (d a); intros; eauto.
    destruct p.
    left.
    eexists.
    exists hm, tt.
    econstructor; eauto.
    eapply StepWrite; eauto.
  - left.
    eauto 10.
  - case_eq (d a); intros; eauto.
    left.
    eexists.
    exists hm, tt.
    econstructor; eauto.
    eapply StepTrim with (vs':=p); eauto.
  - destruct (hash_safe_dec hm (hash_fwd buf) buf).
    eauto 10.
    apply not_hash_safe_conflict in n; eauto.
  - specialize (IHp d hm).
    intuition eauto.
    repeat deex.
    specialize (H v' d' hm').
    assert (hashmap_wf hm') by eauto.
    intuition eauto.
    repeat deex.
    eauto 10.
Qed.
*)
