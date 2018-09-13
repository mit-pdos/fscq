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
Require Export DiskLogPadded.

Set Implicit Arguments.

Import ListNotations.

Inductive state :=
(* The log is synced on disk *)
| Synced (navail : nat) (l: contents)
(* The log has been truncated; but the length (0) is unsynced *)
| Truncated  (old: contents)
(* The log has been extended; the new contents are synced but the length is unsynced *)
| Extended  (old: contents) (new: contents).

Definition rep_common l (padded: contents) : rawpred tagged_block :=
  ([[ l = log_nonzero padded /\
      length padded = roundup (length padded) DescSig.items_per_val ]])%pred.

Definition rep xp st hm :=
  (match st with
   | Synced navail l =>
     exists padded, rep_common l padded *
     [[ navail = (LogLen xp) - (length padded) ]] *
     DiskLogPadded.rep xp (DiskLogPadded.Synced padded) hm
   | Truncated l =>
     exists padded, rep_common l padded *
     DiskLogPadded.rep xp (DiskLogPadded.Truncated padded) hm
   | Extended l new =>
     exists padded, rep_common l padded *
     DiskLogPadded.rep xp (DiskLogPadded.Extended padded new) hm
   end)%pred.


(** API **)

  Definition read xp cs :=
    r <- DiskLogPadded.read xp cs;;
      Ret r.

  Definition init xp cs :=
    cs <- DiskLogPadded.init xp cs;;
    Ret cs.

  Definition trunc xp cs :=
    cs <- DiskLogPadded.trunc xp cs;;
    Ret cs.

  Definition avail xp cs :=
    r <- DiskLogPadded.avail xp cs;;
    Ret r.

  Definition extend xp new cs :=
    r <- DiskLogPadded.extend xp new cs;;
    Ret r.

  Definition recover xp cs :=
    cs <- DiskLogPadded.recover xp cs;;
    Ret cs.


(** Helpers **)
  Theorem sync_invariant_rep : forall xp st hm,
    sync_invariant (rep xp st hm).
  Proof.
    unfold rep, rep_common; destruct st; intros; eauto.
  Qed.

  Hint Resolve sync_invariant_rep.
  Local Hint Unfold rep rep_common : hoare_unfold.
  Hint Resolve DescDefs.items_per_val_gt_0 DescDefs.items_per_val_not_0.

  Lemma xform_rep_synced : forall xp na l hm,
    crash_xform (rep xp (Synced na l) hm) =p=> rep xp (Synced na l) empty_mem.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    apply xform_rep_synced.
  Qed.

  Lemma xform_rep_truncated : forall xp l hm,
    crash_xform (rep xp (Truncated l) hm) =p=> exists na,
      rep xp (Synced na l) empty_mem \/ rep xp (Synced (LogLen xp) nil) empty_mem.
  Proof.
    unfold rep, rep_common; intros.
    xform; cancel.
    rewrite xform_rep_truncated.
    cancel.
    or_r; cancel.
    rewrite roundup_0; auto.
  Qed.


  Lemma rep_domainmem_subset : forall xp hm hm',
    hm c= hm'
    -> forall st, rep xp st hm
        =p=> rep xp st hm'.
  Proof.
    unfold rep; intros.
    destruct st; cancel;
    try erewrite rep_domainmem_subset; eauto.
    all: cancel; eauto.
  Qed.
  
  Lemma xform_rep_extended : forall xp old new hm,
    crash_xform (rep xp (Extended old new) hm) =p=>
       (exists na, rep xp (Synced na old) empty_mem) \/
       (exists na, rep xp (Synced na (old ++ new)) empty_mem).
  Proof.
    unfold rep, rep_common; intros.
    xform.
    rewrite rep_extended_facts.
    xform; cancel.
    rewrite DiskLogPadded.xform_rep_extended.
    cancel.
    rewrite DiskLogPadded.rep_synced_app_pimpl.
    or_r; cancel.
    rewrite log_nonzero_app.
    repeat rewrite log_nonzero_padded_log; eauto.
    rewrite entry_valid_vals_nonzero with (l:=new); auto.
    unfold padded_log; rewrite <- padded_log_app.
    repeat rewrite padded_log_length.
    unfold roundup.
    rewrite divup_divup; eauto.
  Qed.



  (** Specs **)
  Definition recover_ok :
    forall xp cs pr,
    {!< F nr l d,
    PERM:pr   
    PRE:bm, hm,
          CacheDef.rep cs d bm * (
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]) *
          [[ bm = empty_mem ]] *
          [[ hm = empty_mem ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET:cs'
          CacheDef.rep cs' d bm' *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]] *
          [[ hm' dummy_handle = Some Public ]]             
    XCRASH:bm'', hm'', exists cs',
          CacheDef.rep cs' d bm'' * (
          [[ (F * rep xp (Synced nr l) hm'')%pred d ]])
    >!} recover xp cs.
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
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (recover _ _) _) => apply recover_ok : prog.
  
  Section UnifyProof.
  Hint Extern 0 (okToUnify (DiskLogPadded.rep _ _ _) (DiskLogPadded.rep _ _ _)) => constructor : okToUnify.

  Definition read_ok :
    forall xp cs pr,
    {< F l d nr,
     PERM:pr  
     PRE:bm, hm,
         CacheDef.rep cs d bm * 
         [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:bm', hm',   RET: ^(cs, r)
         CacheDef.rep cs d bm' *
         [[ extract_blocks_list bm' r = l /\
            (F * rep xp (Synced nr l) hm')%pred d ]] *
         [[ handles_valid_list bm' r ]] *
         [[ Forall entry_valid r ]]
    CRASH:bm'', hm'', exists cs',
         CacheDef.rep cs' d bm''*
         [[ (F * rep xp (Synced nr l) hm'')%pred d ]]
    >} read xp cs.
  Proof.
    unfold read.
    hoare.
    rewrite <- H1; cancel; eauto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

Hint Resolve rep_domainmem_subset.
  
  Definition trunc_ok :
    forall xp cs pr,
    {< F l d nr,
    PERM:pr   
    PRE:bm, hm,
     CacheDef.rep cs d bm *
     [[ (F * rep xp (Synced nr l) hm)%pred d ]] * 
     [[  sync_invariant F ]]
    POST:bm', hm', RET: cs exists d',
              CacheDef.rep cs d' bm' *
              [[ (F * rep xp (Synced (LogLen xp) nil) hm')%pred d' ]]
    XCRASH:bm'', hm'', exists cs d',
        CacheDef.rep cs d' bm'' * (
          [[ (F * rep xp (Synced nr l) hm'')%pred d' ]] \/
          [[ (F * rep xp (Truncated l) hm'')%pred d' ]])
    >} trunc xp cs.
  Proof.
    unfold trunc.
    safestep.
    step.
    safestep.
    simpl; unfold roundup; rewrite divup_0; omega.
    eauto.

    (* crashes *)
    rewrite <- H1; cancel.
    xcrash;
    eassign x; eassign x0; cancel.
    or_l; cancel.
    or_r; cancel.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.


  Definition avail_ok :
    forall xp cs pr,
    {< F l d nr,
    PERM:pr   
    PRE:bm, hm,
          CacheDef.rep cs d bm *
          [[ (F * rep xp (Synced nr l) hm)%pred d ]]
    POST:bm', hm', RET: ^(cs, r)
          CacheDef.rep cs d bm' *
          [[ (F * rep xp (Synced nr l) hm')%pred d ]] *
          [[ r = nr ]]
    CRASH:bm'', hm'', exists cs',
          CacheDef.rep cs' d bm'' *
          [[ (F * rep xp (Synced nr l) hm'')%pred d ]]
    >} avail xp cs.
  Proof.
    unfold avail.
    step.
    step.
    step.
    rewrite <- H1; cancel.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
  Qed.

  End UnifyProof.

  Definition init_ok :
    forall xp cs pr,
    {< F l d,
    PERM:pr   
    PRE:bm, hm,
          CacheDef.rep cs d bm *
          [[ (F * arrayS (LogHeader xp) l)%pred d ]] *
          [[ length l = (1 + LogDescLen xp + LogLen xp) /\
             LogDescriptor xp = LogHeader xp + 1 /\
             LogData xp = LogDescriptor xp + LogDescLen xp /\
             LogLen xp = (LogDescLen xp * DescSig.items_per_val)%nat /\
             goodSize addrlen ((LogHeader xp) + length l) ]] *
          [[ sync_invariant F ]]
    POST:bm', hm', RET: cs  exists d' nr,
          CacheDef.rep cs d' bm' *
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
    eauto.    
    rewrite roundup_0; auto.
    Unshelve.
    unfold EqDec; apply handle_eq_dec.
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
    -> (F * DiskLogPadded.rep xp (DiskLogPadded.Synced padded) hm)%pred d
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
              CacheDef.rep cs d bm *
              [[ (F * rep xp (Synced nr old) hm)%pred d ]] *
              [[ handles_valid bm (map ent_handle new) ]] *
              [[ blocks = extract_blocks bm (map ent_handle new) ]] *
              [[ entries_valid new /\ sync_invariant F ]]
    POST:bm', hm', RET: ^(cs, r) exists d',
              CacheDef.rep cs d' bm' * (
              [[ r = true /\
                (F * rep xp (Synced (nr - (rounded (length new))) (old ++ (combine (map fst new) blocks))) hm')%pred d' ]] \/
              [[ r = false /\ length new > nr /\
                (F * rep xp (Synced nr old) hm')%pred d' ]])
    XCRASH:bm'', hm'', exists cs' d',
              CacheDef.rep cs' d' bm'' * (
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
    eapply DiskLogPadded.rep_domainmem_subset; eauto.
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
      match goal with
      | [H: length _ = ?x |- context [?x] ] =>
        setoid_rewrite <- H
      end.
    rewrite Nat.sub_add_distr; auto.
    apply length_map_fst_extract_blocks_eq; auto.
    solve_hashmap_subset.

    step.
    solve_hashmap_subset.

    rewrite <- H1; cancel.
    eauto.
    xcrash; eassign x; eassign x0; cancel.
    or_l; cancel.
    or_r; cancel.
    Unshelve.
    all: unfold EqDec; apply handle_eq_dec.
  Qed.

  Hint Extern 1 ({{_|_}} Bind (avail _ _) _) => apply avail_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (trunc _ _) _) => apply trunc_ok : prog.
  Hint Extern 1 ({{_|_}} Bind (extend _ _ _) _) => apply extend_ok : prog.
