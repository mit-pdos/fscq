Require Import Mem Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Pred.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import WordAuto.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import DiskLogPadded DiskLog DiskLogPaddedRecovery.

Set Implicit Arguments.

Import ListNotations.

Hint Resolve sync_invariant_rep.
Local Hint Unfold rep rep_common : hoare_unfold.
Hint Resolve DescDefs.items_per_val_gt_0 DescDefs.items_per_val_not_0.

Lemma xform_rep_synced : forall xp na l hm,
    crash_xform (rep xp (Synced na l) hm) =p=> rep xp (Synced na l) hm.
Proof.
  unfold rep, rep_common; intros.
  xform; cancel.
  apply xform_rep_synced.
Qed.

Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=> exists na,
                                              rep xp (Synced na l) hm \/ rep xp (Synced (LogLen xp) nil) hm.
Proof.
  unfold rep, rep_common; intros.
  xform; cancel.
  rewrite xform_rep_truncated.
  cancel.
  or_r; cancel.
  rewrite roundup_0; auto.
Qed.

Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
(exists na, rep xp (Synced na old) hm) \/
(exists na, rep xp (Synced na (old ++ new)) hm).
Proof.
  unfold rep, rep_common; intros.
  xform.
  rewrite rep_extended_facts.
  xform; cancel.
  rewrite xform_rep_extended.
  cancel.
  rewrite rep_synced_app_pimpl.
  or_r; cancel.
  rewrite log_nonzero_app.
  repeat rewrite log_nonzero_padded_log; eauto.
  rewrite entry_valid_vals_nonzero with (l:=new); auto.
  unfold padded_log; rewrite <- padded_log_app.
  repeat rewrite padded_log_length.
  unfold roundup.
  rewrite divup_divup; eauto.
Qed.

  Definition recover_ok :
    forall xp cs pr,
    {< F nr l d,
    PERM:pr   
    PRE:bm, hm,
          CacheDef.rep cs d bm * (
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]) *
          [[ bm = empty_mem ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET:cs'
          CacheDef.rep cs' d bm' *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]]           
    XCRASH:bm'', hm'', exists cs',
          CacheDef.rep cs' d bm'' * (
          [[ (F * rep xp (Synced nr l) hm'')%pred d ]])
    >} recover xp cs.
  Proof.
    unfold recover.
    prestep. norm. cancel.
    intuition simpl.
    pred_apply.
    eassign F; cancel.
    eauto.

    step.
    step.

    rewrite <- H1; cancel.
    xcrash.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (recover _ _) _) => apply recover_ok : prog.
  