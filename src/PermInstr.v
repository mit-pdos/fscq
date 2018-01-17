Require Import Pred Mem Word Arith.
Require Import FunctionalExtensionality.
Require Export PermSepAuto.

Lemma bind_secure:
  forall T T' (p1: prog T) (p2: T -> prog T') pr d bm hm,
    permission_secure d bm hm pr p1 ->
    (forall d' bm' hm' tr tr' r,
       exec pr tr d bm hm p1 (Finished d' bm' hm' r) tr' ->
       permission_secure d' bm' hm' pr (p2 r)) ->
    permission_secure d bm hm pr (Bind p1 p2).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; cleanup.
  {
    specialize (trace_app H1); intros; cleanup.
    specialize (H _ _ _ H1); cleanup.
    specialize (trace_app H2); intros; cleanup.
    specialize (H0 _ _ _ _ _ _ H1); cleanup.
    rewrite <- app_assoc in H2;
    specialize (H0 _ _ _ H2); cleanup.
    apply trace_secure_app; auto.
  }
  {
    destruct H1.
    specialize (H _ _ _ H1); cleanup; auto.
    cleanup.
    specialize (trace_app H1); intros; cleanup.
    specialize (H _ _ _ H1); cleanup.
    specialize (trace_app H2); intros; cleanup.
    specialize (H0 _ _ _ _ _ _ H1); cleanup.
    rewrite <- app_assoc in H2;
    specialize (H0 _ _ _ H2); cleanup.
    apply trace_secure_app; auto.
  }
Qed.

Lemma permission_drop_secure:
  forall d bm pr1 pr2 T (p: prog T) hm,
    permission_secure d bm hm pr1 p ->
    permitted pr2 pr1 ->
    (forall tr tr2 r, exec pr2 tr d bm hm p r (tr2++tr) ->
                      exists tr1, exec pr1 tr d bm hm p r (tr1++tr) /\ trace_match tr1 tr2) ->
    permission_secure d bm hm pr2 p.
Proof.
  unfold permission_secure; intros.
  specialize (H1 _ _ _ H2); cleanup.
  specialize (H _ _ _ H1); intuition.
  eapply trace_secure_match; eauto.
Qed.

Hint Resolve HS_nil.

Definition false_pred {AT AEQ V}:= lift_empty(False)(AT:=AT)(AEQ:=AEQ)(V:=V).
Hint Unfold false_pred.

Lemma false_pred_all:
  forall AT AEQ V (P: @pred AT AEQ V),
    false_pred =p=> P.
Proof.
  unfold false_pred; intros; cancel.
Qed.

Hint Resolve false_pred_all.


Lemma read_secure:
  forall pr a,
    {< tbs,
       PERM: pr
       PRE: bm, hm,
          a|+> tbs
       POST: bm', hm',
          RET: i
          (a|+> tbs * [[ bm i = None ]] *
           [[ bm' = upd (AEQ:= PeanoNat.Nat.eq_dec) bm i (fst tbs) ]])%pred
       CRASH: bm',  hm',
          a|+>tbs
     >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
  }
  split_ors; cleanup.
  {
    split.
    right; do 3 eexists; intuition.
    inv_exec_perm.
    apply H3.
    pred_apply; cancel; eauto.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
  }
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
    split_ors; cleanup; try congruence.
    do 2 eexists; intuition eauto.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
  }
Qed.

Lemma write_secure:
  forall pr a i,
    {< tb tbs,
       PERM: pr
       PRE: bm, hm,
          (a|+>tbs * [[ bm i = Some tb ]])%pred
       POST: bm', hm',
          RET: tt
          (a|+>(tb, vsmerge tbs) * [[ bm' = bm ]])%pred
       CRASH: bm', hm',
          (a|+>tbs)%pred
     >} Write a i.
Proof.
  unfold corr2; intros.
   destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= tb)(vs':= vsmerge (fst dummy1, x0)) in H.
    pred_apply; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
    
    split; eauto.
    
    clear H0; eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    inv_exec_perm; cleanup; auto.
  }
  split_ors; cleanup.
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    do 2 eexists; intuition eauto.
    apply H3.
    pred_apply; cancel; eauto.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= tb)(vs':= vsmerge (fst dummy1, x)) in H.
    pred_apply; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
  }
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= tb)(vs':= vsmerge (fst dummy1, x0)) in H as Hy.
    pred_apply; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
    split_ors; cleanup; try congruence.
    do 2 eexists; intuition eauto.
    
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= tb)(vs':= vsmerge (fst dummy1, x4)) in H.
    pred_apply; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
  }
Qed.


Lemma seal_secure:
  forall pr t b,
    {!< F,
       PERM: pr
       PRE: bm, hm,
         (F * [[ can_access pr t ]])%pred
       POST: bm', hm',
          RET : i
          F * [[ bm i = None ]] *
          [[ bm' = upd (AEQ:= PeanoNat.Nat.eq_dec) bm i (t, b)]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     >!} Seal t b.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
Qed.

Lemma unseal_secure:
  forall pr i,
     {!< F tb,
       PERM: pr
       PRE: bm, hm, 
         F * [[ can_access pr (fst tb) ]] *
         [[ bm i = Some tb ]]
       POST: bm', hm', RET : b
         F * [[ b = snd tb ]] *
         [[ bm' = bm ]]
       CRASH: bm'', hm'',
         false_pred (* Can't crash *)
     >!} Unseal i.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto; cleanup.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
Qed.

Theorem hash_ok:
  forall sz (buf : word sz) pr,
  {!< F,
  PERM: pr
  PRE:bm, hm,
    F
  POST:bm', hm',
    RET:h     F * [[ bm' = bm ]] *
              [[ hash_safe hm h buf ]] *
              [[ h = hash_fwd buf ]] *
              [[ hm' = upd_hashmap' hm h buf ]]
  CRASH:bm'', hm'',
    false_pred (* Can't crash *)                            
  >!} Hash buf.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto; cleanup.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
Qed.


Theorem hash2_ok:
  forall sz1 sz2 (buf1 : word sz1) (buf2 : word sz2) pr,
  {!< F,
  PERM: pr
  PRE:bm, hm,
    F
  POST:bm', hm',
    RET:h     F * [[ bm' = bm ]] *
              [[ hash_safe hm h (Word.combine buf1 buf2) ]] *
              [[ h = hash_fwd (Word.combine buf1 buf2) ]] *
              [[ hm' = upd_hashmap' hm h (Word.combine buf1 buf2) ]]
  CRASH:bm'', hm'',
    false_pred (* Can't crash *)           
  >!} Hash2 buf1 buf2.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto; cleanup.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
Qed.

Theorem hashhandle_ok:
  forall i pr,
  {!< F tb,
  PERM: pr
  PRE:bm, hm,
    F * [[ bm i = Some tb ]]
  POST:bm', hm',
    RET:h     F * [[ bm' = bm ]] *
              [[ hash_safe hm h (encode tb) ]] *
              [[ h = hash_fwd (encode tb) ]] *
              [[ hm' = upd_hashmap' hm h (encode tb) ]]
  CRASH:bm'', hm'',
    false_pred (* Can't crash *)           
  >!} HashHandle i.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto; cleanup.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
Qed.

Theorem hashhandle2_ok:
  forall sz (buf2 : word sz) i pr,
  {!< F tb,
  PERM: pr
  PRE:bm, hm,
    F * [[ bm i = Some tb ]]
  POST:bm', hm',
    RET:h     F * [[ bm' = bm ]] *
              [[ hash_safe hm h (Word.combine (encode tb) buf2) ]] *
              [[ h = hash_fwd (Word.combine (encode tb) buf2) ]] *
              [[ hm' = upd_hashmap' hm h (Word.combine (encode tb) buf2) ]]
  CRASH:bm'', hm'',
    false_pred (* Can't crash *)           
  >!} HashHandle2 i buf2.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto; cleanup.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    solve_hashmap_subset.
  }
Qed.

Lemma ret_secure:
  forall T pr (v: T),
     {!< F,
       PERM: pr
       PRE: bm, hm,
          F
       POST: bm', hm', RET : r
         F * [[ r = v ]] *
         [[ bm' = bm ]]
       CRASH:bm'', hm'',
         false_pred (* Can't crash *)
     >!} Ret v.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
Qed.

Lemma ret_secure':
  forall T pr (v: T),
     {!< F,
       PERM: pr
       PRE: bm, hm,
          F bm hm
       POST: bm', hm', RET : r
         F bm' hm' * [[ r = v ]] *
         [[ bm' = bm ]]
       CRASH:bm'', hm'',
         false_pred (* Can't crash *)
     >!} Ret v.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    split.
    right; do 3 eexists; intuition.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
Qed.

Lemma sync_secure:
  forall pr,
     {!< F,
       PERM: pr
       PRE: bm, hm,
         F * [[ sync_invariant F ]]
       POST: bm', hm',  RET : tt
         sync_xform F *
         [[ bm' = bm ]]
       CRASH: bm'', hm'',
         F
     >!} Sync.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
    
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1; inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
   repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  split_ors; cleanup.
  {
    split.
    right; do 3 eexists; intuition.
    inv_exec_perm.
    apply H3; pred_apply; cancel; eauto.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  {
    split.
    right; do 3 eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
Qed.


Lemma sync_secure':
  forall pr,
     {!< F,
       PERM: pr
       PRE: bm, hm,
         F bm hm * [[ sync_invariant (F bm hm) ]]
       POST: bm', hm',  RET : tt
         sync_xform (F bm' hm') *
         [[ bm' = bm ]]
       CRASH: bm'', hm'',
         (F bm'' hm'')
     >!} Sync.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
    
    split; auto.
    clear H0; eapply bind_secure; intuition.  
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    clear H1; inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
   repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  split_ors; cleanup.
  {
    split.
    right; do 3 eexists; intuition.
    inv_exec_perm.
    apply H3; pred_apply; cancel; eauto.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  {
    split.
    right; do 3 eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
    split_ors; cleanup; try congruence.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (Read _) _)) => apply read_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Write _ _) _)) => apply write_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Seal _ _) _)) => apply seal_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Unseal _) _)) => apply unseal_secure : prog.
Hint Extern 1 ({{_|_}} Bind (Hash _) _) => apply hash_ok : prog.
Hint Extern 1 ({{_|_}} Bind (Hash2 _ _) _) => apply hash2_ok : prog.
Hint Extern 1 ({{_|_}} Bind (HashHandle _) _) => apply hashhandle_ok : prog.
Hint Extern 1 ({{_|_}} Bind (HashHandle2 _ _) _) => apply hashhandle2_ok : prog.
Hint Extern 1 (corr2 _ _ (Bind Sync _)) => apply sync_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Ret _) _)) => apply ret_secure : prog.














