Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Mem Pred.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import WordAuto.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Import DiskLogPadded.

Hint Resolve Desc.Defs.items_per_val_not_0 Desc.Defs.items_per_val_gt_0.


Lemma xform_rep_synced : forall xp l hm,
  crash_xform (rep xp (Synced l) hm) =p=> rep xp (Synced l) hm.
Proof.
  unfold rep; simpl; unfold rep_contents; intros.
  xform.
  norm'l. unfold stars; cbn.
  xform.
  norm'l. unfold stars; cbn.
  xform.
  rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
  rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
  rewrite DiskLogHdr.xform_rep_synced.
  cancel.
Qed.


Lemma xform_rep_truncated : forall xp l hm,
crash_xform (rep xp (Truncated l) hm) =p=>
rep xp (Synced l) hm \/ rep xp (Synced nil) hm.
Proof.
  unfold rep; simpl; unfold rep_contents; intros.
  xform; cancel.
  xform; cancel.
  rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
  rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
  rewrite DiskLogHdr.xform_rep_unsync.
  norm; auto.

  or_r; cancel.
  cancel_by helper_trunc_ok.
  apply Forall_nil.
  auto.
  or_l; cancel.
Qed.


  Lemma recover_desc_avail_helper : forall B T xp (old: @generic_contents B) (new : list T) ndata,
    loglen_valid xp (ndesc_log old + ndesc_list new) ndata ->
    (Desc.avail_rep xp (ndesc_log old) (ndesc_list new)
     * Desc.avail_rep xp (ndesc_log old + ndesc_list new)
         (LogDescLen xp - ndesc_log old - ndesc_list new))
    =p=> Desc.avail_rep xp (ndesc_log old) (LogDescLen xp - ndesc_log old).
  Proof.
    intros.
    rewrite Desc.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    omega.
  Qed.

  Lemma recover_data_avail_helper : forall B T xp (old: @generic_contents B) (new : list T) ndesc,
    loglen_valid xp ndesc (ndata_log old + length new) ->
    Data.avail_rep xp (ndata_log old)
          (divup (length new) DataSig.items_per_val)
    * Data.avail_rep xp (ndata_log old + length new)
        (LogLen xp - ndata_log old - length new)
    =p=> Data.avail_rep xp (nonzero_addrs (map fst old))
           (LogLen xp - nonzero_addrs (map fst old)).
  Proof.
    intros.
    replace DataSig.items_per_val with 1 by (cbv; auto); try omega.
    rewrite divup_1, Data.avail_rep_merge;
    eauto.
    rewrite le_plus_minus_r;
    auto.
    unfold loglen_valid in *;
    omega.
  Qed.

  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       rep xp (Synced old) hm \/
       rep xp (Synced (padded_log old ++ new)) hm.
  Proof. 
    intros; rewrite rep_extended_facts.
    unfold rep; simpl; unfold rep_contents; intros.
    xform; cancel.
    xform; cancel.
    rewrite DiskLogHdr.xform_rep_unsync; cancel.

    - or_r.
      cancel.
      rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
      rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
      cancel.
      rewrite ndesc_log_app, ndata_log_app.
      unfold padded_log; rewrite ndesc_log_padded_log, ndata_log_padded_log; cancel.
      unfold padded_log; repeat rewrite padded_log_length.
      unfold roundup; rewrite divup_mul; eauto.

    - or_l.
      rewrite Data.xform_avail_rep, Desc.xform_avail_rep.
      rewrite Data.xform_synced_rep, Desc.xform_synced_rep.
      rewrite ndesc_log_app, ndata_log_app.
      rewrite addr_tags_app, map_app.
      rewrite tags_nonzero_app, vals_nonzero_app.
      rewrite vals_nonzero_padded_log, tags_nonzero_padded_log.
      rewrite Data.array_rep_synced_app_rev, Desc.array_rep_synced_app_rev.
      cancel.
      rewrite <- desc_padding_synced_piff.
      unfold padded_log.
      repeat rewrite ndesc_log_padded_log, ndata_log_padded_log.
      cancel.
      rewrite <- Data.avail_rep_merge with (n1:=ndata_log new)(start :=ndata_log old).
      rewrite <- Desc.avail_rep_merge with (n1:=ndesc_log new)(start:=ndesc_log old).
      cancel.
      rewrite Data.array_rep_avail, Desc.array_rep_avail.
      unfold Data.nr_blocks, Desc.nr_blocks.
      unfold ndesc_log, ndata_log.
      repeat rewrite divup_1.
      repeat rewrite map_length.
      rewrite padded_log_length;
      unfold roundup; rewrite divup_divup.
      cancel.
      repeat rewrite vals_nonzero_addrs. cancel.
      all: eauto; try omega.
      all: try apply helper_add_sub_add; eauto.
      eapply padded_addr_valid; eapply forall_app_r; eauto.
      unfold padded_log; rewrite map_length, padded_log_length; unfold roundup; eauto.
      unfold addr_tags; rewrite repeat_length.
      erewrite ndesc_log_ndesc_list.
      unfold padded_log, ndesc_list.
      rewrite DescDefs.ipack_length; eauto.
      rewrite padded_log_idem; eauto.
      rewrite Nat.mul_1_r; eauto.
      rewrite ipack_noop.
      rewrite vals_nonzero_addrs; apply tags_nonzero_addrs.
      unfold padded_log; repeat rewrite padded_log_length.
      unfold roundup; rewrite divup_divup; eauto.
      Unshelve.
      exact tagged_block0.
  Qed.

  
Definition recover_ok :
  forall xp cs pr,
    {< F l d,
     PERM:pr
     PRE:bm, hm,
         CacheDef.rep cs d bm *
         [[ bm = empty_mem ]] *
         [[ (F * rep xp (Synced l) hm)%pred d ]]
    POST:bm', hm', RET:cs'
          CacheDef.rep cs' d bm' *
          [[ (F * rep xp (Synced l) hm')%pred d ]]       
    CRASH:bm'', hm_crash, exists cs',
          CacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced l) hm_crash)%pred d ]]
    >} recover xp cs.
  Proof. 
    unfold recover, rep, rep_contents.
    step.
    safestep.
    eassign (map ent_addr (padded_log l)).
    unfold padded_log.
    rewrite map_length, padded_log_length.
    all: eauto.
    eassign (addr_tags (ndesc_log l)).
    unfold addr_tags; rewrite repeat_length; auto.
    unfold xparams_ok  in *; intuition.
    unfold padded_log; rewrite desc_padding_synced_piff.
    unfold rep_contents.
    cancel.

    safestep.
    rewrite vals_nonzero_addrs.
    replace DataSig.items_per_val with 1 by (cbv; auto).
    unfold ndata_log; omega.
    rewrite tags_nonzero_addrs.
    replace DataSig.items_per_val with 1 by (cbv; auto).
    unfold ndata_log; omega.
    unfold xparams_ok  in *; intuition.
    
    step.
    step.
    unfold rep_contents; cancel. apply desc_padding_synced_piff.
    unfold rep_contents in H0; destruct_lift H0; eauto.
    
    all: rewrite <- H1; cancel; unfold padded_log; solve_blockmem_subset.
    unfold rep_contents; cancel; try apply desc_padding_synced_piff.
    unfold rep_contents in H0; destruct_lift H0; eauto.

    Unshelve.
    all: unfold Mem.EqDec; apply handle_eq_dec.
  Qed.

  
  Hint Extern 1 ({{_ | _}} Bind (recover _ _) _) => apply recover_ok : prog.
