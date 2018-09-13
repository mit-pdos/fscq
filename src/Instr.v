Require Import Pred Mem Word Arith List.
Require Import FunctionalExtensionality.
Require Export SepAuto.

Hint Resolve HS_nil.

Definition false_pred {AT AEQ V}:= lift_empty(False)(AT:=AT)(AEQ:=AEQ)(V:=V).
Hint Unfold false_pred.

Lemma false_pred_all:
  forall AT AEQ V (P: @pred AT AEQ V),
    false_pred =p=> P.
Proof.
  unfold false_pred; intros; cancel.
Qed.

Hint Unfold false_pred: hoare_unfold.

Lemma insdom_secure:
  forall pr i t,
    {!< F,
       PERM: pr
       PRE: bm, hm,
         F * [[ hm i = None ]]
       POST: bm', hm',
          RET : tt
          F * [[ hm' = upd hm i t]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     >!} InsDom i t.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm; try congruence.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (InsDom _ _) _)) => apply insdom_secure : prog.


Lemma chdom_secure:
  forall pr i t,
    {~!< F t',
       PERM: pr
       PRE: bm, hm,
         F * [[ hm i = Some t' ]]
       POST: bm', hm',
          RET : tt
          F * [[ hm' = upd hm i t]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     >!~} ChDom i t.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm; try congruence.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
Qed.

Lemma adddom_secure:
  forall pr t,
    {!< F,
       PERM: pr
       PRE: bm, hm,
         F
       POST: bm', hm',
          RET : i
          F * [[ hm i = None ]] *
          [[ hm' = upd hm i t]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     >!} AddDom t.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
Qed.


Lemma auth_secure:
  forall pr t,
    {!< F,
       PERM: pr
       PRE: bm, hm,
         F
       POST: bm', hm',
          RET : i
        F * (([[ i = true ]] * [[ can_access pr t ]]) \/
            ([[ i = false ]] * [[ ~can_access pr t ]]))    
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     >!} Auth t.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
  }
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    or_r; cancel.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
  }
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    or_r; cancel.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
  }
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    or_r; cancel.
  }
Qed.

Lemma read_secure:
  forall pr a,
    {!< F tbs,
       PERM: pr
       PRE: bm, hm,
          F * a|+> tbs
       POST: bm', hm',
          RET: i
          F * (a|+> tbs * [[ bm i = None ]] *
           [[ bm' = upd bm i (fst tbs) ]])%pred
       CRASH: bm',  hm',
          F * a|+>tbs
     >!} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
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
    inv_exec_perm; cleanup; simpl; auto.
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
    inv_exec_perm; cleanup; auto.
    try rewrite app_nil_r.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm.
    apply ptsto_subset_valid' in H; cleanup; congruence.
  }
  {
    repeat inv_exec_perm; simpl in *; cleanup.
    try rewrite app_nil_r.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_subset_valid' in H; cleanup; eauto.
  }
Qed.

Lemma write_secure:
  forall pr a i,
    {!< F tb tbs,
       PERM: pr
       PRE: bm, hm,
          F * (a|+>tbs * [[ bm i = Some tb ]])%pred
       POST: bm', hm',
          RET: tt
          F * (a|+>(tb, vsmerge tbs) * [[ bm' = bm ]])%pred
       CRASH: bm', hm',
          F * (a|+>tbs)%pred
     >!} Write a i.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= b)(vs':= vsmerge (dummy1_1, x)) in H.
    pred_apply' H; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
  }
  split_ors; cleanup.
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    do 2 eexists; intuition eauto.
    apply H3.
    pred_apply; cancel; eauto.
    inv_exec_perm; cleanup; simpl; auto.
  }
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= b)(vs':= vsmerge (dummy1_1, x)) in H as Hy.
    pred_apply' Hy; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
    split_ors; cleanup; try congruence.
    do 2 eexists; intuition eauto.
    inv_exec_perm; cleanup; simpl; auto.
    try rewrite app_nil_r.
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= b)(vs':= vsmerge (dummy1_1, x)) in H.
    pred_apply' H; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm; cleanup.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    intuition congruence.
  }
  {
    inv_exec_perm; cleanup;
    try rewrite app_nil_r.
    edestruct H4; eauto.
    apply ptsto_subset_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_subset_upd  with (v:= b)(vs':= vsmerge (dummy1_1, x)) in H.
    pred_apply' H; cancel; eauto.
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; auto.
  }
Qed.


Lemma seal_secure:
  forall pr t b,
    {!< F,
       PERM: pr
       PRE: bm, hm,
         F
       POST: bm', hm',
          RET : i
          F * [[ bm i = None ]] *
          [[ bm' = upd bm i (t, b)]]
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
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply only_public_operations_app_merge; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
  }
Qed.


Lemma seal_secure_weak:
  forall pr t b,
    {!<W F,
       PERM: pr
       PRE: bm, hm,
         F
       POST: bm', hm',
          RET : i
          F * [[ bm i = None ]] *
          [[ bm' = upd bm i (t, b)]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     W>!} Seal t b.
Proof.
  unfold corr2_weak; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply trace_secure_app; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply trace_secure_app; simpl; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.  
    split; auto.
    apply trace_secure_app; simpl; auto.
  }
Qed.

Lemma unseal_secure:
  forall pr i,
     {!< F tb,
       PERM: pr
       PRE: bm, hm, 
         F * [[ hm dummy_handle = Some Public ]] *
         [[ fst tb = dummy_handle ]] *
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
    apply only_public_operations_app_merge; simpl; eauto.
    simpl in *; cleanup; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    cleanup.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply only_public_operations_app_merge; simpl; auto.
    simpl in *; cleanup; eauto.
  }
  repeat split_ors; cleanup; inv_exec_perm; try congruence.
  split_ors; cleanup; simpl in *; try congruence.
  {
    cleanup.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
    simpl in *; cleanup; eauto.
  }
Qed.


Lemma unseal_secure_weak:
  forall pr i,
     {!<W F tb t,
       PERM: pr
       PRE: bm, hm, 
         F * [[ hm (fst tb) = Some t ]] * [[ can_access pr t ]] *
         [[ bm i = Some tb ]]
       POST: bm', hm', RET : b
         F * [[ b = snd tb ]] *
         [[ bm' = bm ]]
       CRASH: bm'', hm'',
         false_pred (* Can't crash *)
     W>!} Unseal i.
Proof.
  unfold corr2_weak; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split; auto.
    apply trace_secure_app; simpl; auto.
    simpl in *; cleanup; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H4; eauto.
    cleanup.
    pred_apply; cancel; eauto.
    split_ors; cleanup; try congruence.
    split.
    right; do 3 eexists; intuition.
    apply trace_secure_app; simpl; auto.
    simpl in *; cleanup; eauto.
  }
  split_ors; cleanup; inv_exec_perm; try congruence.
  split_ors; cleanup; simpl in *; try congruence.
  {
    cleanup.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    split; auto.
    apply trace_secure_app; simpl; auto.
    simpl in *; cleanup; eauto.
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
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
Qed.

Lemma ret_secure_weak:
  forall T pr (v: T),
     {!<W F,
       PERM: pr
       PRE: bm, hm,
          F
       POST: bm', hm', RET : r
         F * [[ r = v ]] *
         [[ bm' = bm ]]
       CRASH:bm'', hm'',
         false_pred (* Can't crash *)
     W>!} Ret v.
Proof.
  unfold corr2_weak; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
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
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
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
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
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
    inv_exec_perm; cleanup; simpl; auto.
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
    inv_exec_perm; cleanup; auto.
    try rewrite app_nil_r.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
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
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
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
    inv_exec_perm; cleanup; simpl; auto.
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
    inv_exec_perm; cleanup; auto.
    try rewrite app_nil_r.
    edestruct H4; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
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
Hint Extern 1 (corr2 _ _ (Bind (ChDom _ _) _)) => apply chdom_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (AddDom _) _)) => apply adddom_secure : prog.
Hint Extern 1 (corr2_weak _ _ (Bind (Seal _ _) _)) => apply seal_secure_weak : prog.
Hint Extern 1 (corr2_weak _ _ (Bind (Unseal _) _)) => apply unseal_secure_weak : prog.
Hint Extern 1 ({{_|_}} Bind (Auth _) _) => apply auth_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind Sync _)) => apply sync_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Ret _) _)) => apply ret_secure : prog.
Hint Extern 1 (corr2_weak _ _ (Bind (Ret _) _)) => apply ret_secure_weak : prog.














