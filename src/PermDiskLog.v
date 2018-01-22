Require Import Arith.
Require Import Bool.
Require Import Eqdep_dec.
Require Import Classes.SetoidTactics.
Require Import Pred PermPredCrash.
Require Import Omega.
Require Import Word.
Require Import Rec.
Require Import WordAuto.
Require Import FSLayout.
Require Import Rounding.
Require Import List ListUtils.
Require Import Psatz.
Require Export PermDiskLogPadded.

Set Implicit Arguments.

Import ListNotations.

Inductive state :=
(* The log is synced on disk *)
| Synced (navail : nat) (l: contents)
(* The log has been truncated; but the length (0) is unsynced *)
| Truncated  (old: contents)
(* The log is being extended; only the content has been updated (unsynced) *)
| ExtendedUnsync (old: contents)
(* The log has been extended; the new contents are synced but the length is unsynced *)
| Extended  (old: contents) (new: contents)
(* The log will roll back to these contents during recovery. *)
| Rollback (l: contents)
(* In the process of recovering. Recovery will definitely end with these
  contents on disk. *)
| Recovering (l: contents).

Definition rep_common l (padded: contents) : rawpred :=
  ([[ l = log_nonzero padded /\
      length padded = roundup (length padded) DescSig.items_per_val ]])%pred.

Definition rep xp st hm :=
  (match st with
   | Synced navail l =>
     exists padded, rep_common l padded *
     [[ navail = (LogLen xp) - (length padded) ]] *
     PermDiskLogPadded.rep xp (PermDiskLogPadded.Synced padded) hm
   | Truncated l =>
     exists padded, rep_common l padded *
     PermDiskLogPadded.rep xp (PermDiskLogPadded.Truncated padded) hm
   | ExtendedUnsync l =>
     exists padded, rep_common l padded *
     PermDiskLogPadded.rep xp (PermDiskLogPadded.Synced padded) hm
   | Extended l new =>
     exists padded, rep_common l padded *
     PermDiskLogPadded.rep xp (PermDiskLogPadded.Extended padded new) hm
   | Rollback l =>
     exists padded, rep_common l padded *
     PermDiskLogPadded.rep xp (PermDiskLogPadded.Rollback padded) hm
   | Recovering l =>
     exists padded, rep_common l padded *
     PermDiskLogPadded.would_recover' xp padded hm
   end)%pred.

  Theorem sync_invariant_rep : forall xp st hm,
    sync_invariant (rep xp st hm).
  Proof.
    unfold rep, rep_common; destruct st; intros; eauto.
  Qed.

  Hint Resolve sync_invariant_rep.
  Local Hint Unfold rep rep_common : hoare_unfold.

  Section UnifyProof.
  Hint Extern 0 (okToUnify (PermDiskLogPadded.rep _ _) (PermDiskLogPadded.rep _ _)) => constructor : okToUnify.

  Definition read xp cs :=
    r <- PermDiskLogPadded.read xp cs;;
    Ret r.

  Definition read_ok :
    forall xp cs pr,
    {< F l d nr,
     PERM:pr  
     PRE:bm, hm,
         PermCacheDef.rep cs d bm * 
         [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:bm', hm',   RET: ^(cs, r)
              PermCacheDef.rep cs d bm' *
              [[ combine_nonzero (fst r) (extract_blocks bm' (snd r)) = l /\
              (F * rep xp (Synced nr l) hm')%pred d ]]
    CRASH:bm'', hm'', exists cs',
              PermCacheDef.rep cs' d bm''*
              [[ (F * rep xp (Synced nr l) hm'')%pred d ]]
    >} read xp cs.
  Proof.
    unfold read.
    hoare.
    apply rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    rewrite <- H1; cancel; eauto.
  Qed.

  Definition init xp cs :=
    cs <- PermDiskLogPadded.init xp cs;;
    Ret cs.

  Definition trunc xp cs :=
    cs <- PermDiskLogPadded.trunc xp cs;;
    Ret cs.

Hint Resolve rep_hashmap_subset.
  
  Definition trunc_ok :
    forall xp cs pr,
    {< F l d nr,
    PERM:pr   
    PRE:bm, hm,
     PermCacheDef.rep cs d bm *
     [[ (F * rep xp (Synced nr l) hm)%pred d ]] * 
     [[  sync_invariant F ]]
    POST:bm', hm', RET: cs exists d',
              PermCacheDef.rep cs d' bm' *
              [[ (F * rep xp (Synced (LogLen xp) nil) hm')%pred d' ]]
    XCRASH:bm'', hm'', exists cs d',
              PermCacheDef.rep cs d' bm'' * (
              [[ (F * rep xp (Synced nr l) hm'')%pred d' ]] \/
              [[ (F * rep xp (Truncated l) hm'')%pred d' ]])
    >} trunc xp cs.
  Proof.
    unfold trunc.
    safestep.
    eassign F; cancel.
    eauto.
    step.
    safestep.
    apply rep_hashmap_subset; eauto.
    eauto.
    simpl; unfold roundup; rewrite divup_0; omega.
    simpl; omega.
    solve_hashmap_subset.

    (* crashes *)
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    xcrash;
    eassign x; eassign x0; cancel.
    or_l; cancel.
    or_r; cancel.
  Qed.


  Definition avail xp cs :=
    r <- PermDiskLogPadded.avail xp cs;;
    Ret r.

  Definition avail_ok :
    forall xp cs pr,
    {< F l d nr,
    PERM:pr   
    PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:bm', hm', RET: ^(cs, r)
          PermCacheDef.rep cs d bm' *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]] *
          [[ r = nr ]]
    CRASH:bm'', hm'', exists cs',
          PermCacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced nr l) hm'')%pred d ]]
    >} avail xp cs.
  Proof.
    unfold avail.
    step.
    step.
    step.
    solve_hashmap_subset.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
  Qed.

  End UnifyProof.

  Definition init_ok :
    forall xp cs pr,
    {< F l d,
    PERM:pr   
    PRE:bm, hm,
          PermCacheDef.rep cs d bm *
          [[ (F * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d' nr,
          PermCacheDef.rep cs d' bm' *
          [[ (F * rep xp (Synced nr nil) hm')%pred d' ]]
    XCRASH:bm'', hm_crash, any
    >} init xp cs.
  Proof.
    unfold init, rep.
    step.
    unfold xparams_ok, DescSig.xparams_ok, DataSig.xparams_ok; intuition.
    substl (LogDescriptor xp); unfold DescSig.RALen.
    eapply goodSize_trans; [ | eauto ]; omega.
    substl (LogData xp); substl (LogDescriptor xp); unfold DataSig.RALen.
    eapply goodSize_trans; [ | eauto ]; omega.
    rewrite Nat.mul_comm; auto.
    step.
    step.
    eapply rep_hashmap_subset; eauto.
    eauto.    
    rewrite roundup_0; auto.
    solve_hashmap_subset.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (init _ _) _) => apply init_ok : prog.

  Local Hint Resolve DescDefs.items_per_val_gt_0.

  Lemma extend_length_ok' : forall B (l new: @generic_contents B) def,
    length l = roundup (length l) DescSig.items_per_val ->
    length (l ++ padded_log_gen def new)
      = roundup (length (l ++ padded_log_gen def new)) DescSig.items_per_val.
  Proof.
    intros.
    repeat rewrite app_length.
    repeat rewrite padded_log_length.
    rewrite H.
    rewrite roundup_roundup_add, roundup_roundup; auto.
  Qed.

  Lemma extend_length_ok : forall B (l new: @generic_contents B) def1 def2,
    length l = roundup (length l) DescSig.items_per_val ->
    length (padded_log_gen def1 l ++ padded_log_gen def2 new)
      = roundup (length (padded_log_gen def1 l ++ padded_log_gen def2 new)) DescSig.items_per_val.
  Proof.
    intros.
    apply extend_length_ok'.
    rewrite padded_log_length.
    rewrite roundup_roundup; auto.
  Qed.

  Lemma helper_extend_length_ok :
    forall xp padded new F d bm hm,
      length padded = roundup (length padded) DescSig.items_per_val
      -> handles_valid bm (map snd new)
    -> length (padded_log padded ++ combine (map fst new)(extract_blocks bm (map snd new)))  > LogLen xp
    -> (F * PermDiskLogPadded.rep xp (PermDiskLogPadded.Synced padded) hm)%pred d
    -> length new > LogLen xp - length padded.
  Proof.
    intros.
    rewrite app_length in H1.
    pose proof (rep_synced_length_ok H2).
    generalize H3.
    rewrite H.
    unfold padded_log in *; rewrite <- padded_log_length with (def:= tagged_block0).
    setoid_rewrite combine_length_eq in H1.
    rewrite map_length in H1.
    intro; omega.
    apply length_map_fst_extract_blocks_eq; auto.
  Qed.

  Local Hint Resolve extend_length_ok helper_extend_length_ok log_nonzero_padded_app.

  Definition extend xp new cs :=
    r <- PermDiskLogPadded.extend xp new cs;;
    Ret r.

  Definition rounded n := roundup n DescSig.items_per_val.

  Definition entries_valid {B} (l: @generic_contents B) := Forall entry_valid l.

  Lemma extend_navail_ok : forall B xp (padded new: @generic_contents B) def1 def2, 
    length padded = roundup (length padded) DescSig.items_per_val ->
    LogLen xp - length padded - rounded (length new)
    = LogLen xp - length (padded_log_gen def1 padded ++ padded_log_gen def2 new).
  Proof.
    unfold rounded; intros.
    rewrite extend_length_ok by auto.
    rewrite app_length.
    rewrite H.
    repeat rewrite padded_log_length.
    rewrite roundup_roundup_add by auto.
    rewrite roundup_roundup by auto.
    omega.
  Qed.

  
  Local Hint Resolve extend_navail_ok rep_synced_app_pimpl.  

  Definition extend_ok :
    forall xp (new: input_contents) cs pr,
    {< F old d nr blocks,
    PERM:pr   
    PRE:bm, hm,
              PermCacheDef.rep cs d bm *
              [[ (F * rep xp (Synced nr old) hm)%pred d ]] *
              [[ handles_valid bm (map ent_handle new) ]] *
              [[ blocks = extract_blocks bm (map ent_handle new) ]] *
              [[ entries_valid new /\ sync_invariant F ]]
    POST:bm', hm', RET: ^(cs, r) exists d',
              PermCacheDef.rep cs d' bm' * (
              [[ r = true /\
                (F * rep xp (Synced (nr - (rounded (length new))) (old ++ (combine (map fst new) blocks))) hm')%pred d' ]] \/
              [[ r = false /\ length new > nr /\
                (F * rep xp (Synced nr old) hm')%pred d' ]])
    XCRASH:bm'', hm'', exists cs' d',
              PermCacheDef.rep cs' d' bm'' * (
              [[ (F * rep xp (Synced nr old) hm'')%pred d' ]] \/
              [[ (F * rep xp (Extended old (combine (map fst new) blocks)) hm'')%pred d' ]])
    >} extend xp new cs.
  Proof.
    unfold extend.

    prestep.
    safecancel.
    eassign F; cancel. auto.
    auto.
    step.
    step.

    or_l. norm; [ cancel | intuition; pred_apply; norm ].
    eassign (padded_log dummy ++
             padded_log(combine (map fst new)
                 (extract_blocks bm (map ent_handle new)))).
    cancel; auto.
    rewrite rep_synced_app_pimpl.
    eapply rep_hashmap_subset; eauto.
    intuition.
    rewrite log_nonzero_app;
    repeat rewrite log_nonzero_padded_log.
    unfold entries_valid in *;
    rewrite entry_valid_vals_nonzero with (l:= combine _ _); auto.
    apply Forall_entry_valid_combine; auto.
    all: unfold padded_log in *; auto.
    rewrite app_length;
    repeat rewrite padded_log_length.
    unfold rounded.
    setoid_rewrite combine_length_eq.
    rewrite map_length;
    setoid_rewrite <- H13.
    rewrite Nat.sub_add_distr; auto.
    apply length_map_fst_extract_blocks_eq; auto.
    solve_hashmap_subset.

    step.
    or_r; cancel.
    eapply helper_extend_length_ok with (padded:= dummy)(new:=new); eauto.
    eapply rep_hashmap_subset; eauto.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    eauto.
    xcrash; eassign x; eassign x0; cancel.
    or_l; cancel.
    or_r; cancel.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (extend _ _ _) _) => apply extend_ok : prog.

  Definition recover xp cs :=
    cs <- PermDiskLogPadded.recover xp cs;;
    Ret cs.

  Definition recover_ok :
    forall xp cs pr,
    {< F nr l,
    PERM:pr   
    PRE:bm, hm,
      exists d, PermCacheDef.rep cs d bm * (
          [[ (F * rep xp (Synced nr l) hm)%pred d ]] \/
          [[ (F * rep xp (Rollback l) hm)%pred d ]]) *
          [[ sync_invariant F ]]
    POST:bm', hm', RET:cs' exists d',
          PermCacheDef.rep cs' d' bm' *
          [[ (F * exists nr', rep xp (Synced nr' l) hm')%pred d' ]]
    XCRASH:bm'', hm'', exists cs' d',
          PermCacheDef.rep cs' d' bm'' * (
          [[ (F * rep xp (Recovering l) hm'')%pred d' ]])
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
    eapply rep_hashmap_subset; eauto.
    solve_hashmap_subset.

    unfold would_recover in *.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    
    xcrash.
    cancel.

    eassign (PermDiskLogPadded.Rollback dummy).
    intuition simpl.
    pred_apply; cancel.
    auto.

    step.
    step.
    eapply rep_hashmap_subset; eauto.
    solve_hashmap_subset.
    
    unfold would_recover in *.
    rewrite <- H1; cancel.
    solve_hashmap_subset.
    
    xcrash.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (recover _ _) _) => apply recover_ok : prog.

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

  Lemma xform_rep_extended_unsync : forall xp l hm,
    crash_xform (rep xp (ExtendedUnsync l) hm) =p=> exists na, rep xp (Synced na l) hm.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply PermDiskLogPadded.xform_rep_synced.
  Qed.

  (*
  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       (exists na, rep xp (Synced na old) hm) \/
       (exists na, rep xp (Synced na (old ++ new)) hm) \/
       (rep xp (Rollback old) hm).
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite rep_extended_facts.
    xform; cancel.
    rewrite PermDiskLogPadded.xform_rep_extended.
    cancel.
    rewrite PaddedLog.rep_synced_app_pimpl.
    or_r; or_l; cancel.
  Qed.
   *)
  
  Lemma xform_rep_rollback : forall xp l hm,
    crash_xform (rep xp (Rollback l) hm) =p=>
      rep xp (Rollback l) hm.
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite xform_rep_rollback.
    cancel.
  Qed.

  Lemma xform_rep_recovering : forall xp l hm,
    crash_xform (rep xp (Recovering l) hm) =p=>
      rep xp (Rollback l) hm \/
        exists na, rep xp (Synced na l) hm.
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite xform_would_recover'.
    cancel.
  Qed.

  Lemma rep_synced_pimpl : forall xp nr l hm,
    rep xp (Synced nr l) hm =p=>
    rep xp (Recovering l) hm.
  Proof.
    unfold rep, would_recover'; intros.
    cancel.
    eassign padded; cancel.
    or_l; cancel.
  Qed.

  Lemma rep_rollback_pimpl : forall xp l hm,
    rep xp (Rollback l) hm =p=>
      rep xp (Recovering l) hm.
  Proof.
    unfold rep, would_recover'; intros.
    cancel.
    eassign padded; cancel.
    or_r; or_l; cancel.
  Qed.

  Lemma rep_hashmap_subset : forall xp hm hm',
    (exists l, hashmap_subset l hm hm')
    -> forall st, rep xp st hm
        =p=> rep xp st hm'.
  Proof.
    unfold rep; intros.
    destruct st; cancel;
    try erewrite rep_hashmap_subset; eauto.
    all: cancel; eauto.
    rewrite would_recover'_hashmap_subset; eauto.
  Qed.