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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H6; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
  }
  {
    edestruct H6; eauto.
    pred_apply; cancel; eauto.
    or_r; cancel.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H6; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
  }
  {
    edestruct H6; eauto.
    pred_apply; cancel; eauto.
    or_r; cancel.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H6; eauto.
    pred_apply; cancel; eauto.
    or_l; cancel.
  }
  {
    edestruct H6; eauto.
    pred_apply; cancel; eauto.
    or_r; cancel.
  }
Qed.

Lemma mem_merges_to_none :
  forall V1 V2 (bm: block_mem V1) (bt: block_mem V2) btb h,
    (mem_merges_to (AEQ:= handle_eq_dec)) bt bm btb ->
    (bt h = None \/ bm h = None) ->
    btb h = None.
Proof.
  unfold mem_merges_to, memmatch; intros.
  cleanup; specialize (H1 h).
  destruct (btb h); intuition;
    edestruct p, H1;
    edestruct H3; eauto; congruence.
Qed.

Lemma mem_merges_to_upd:
  forall V1 V2 (bm: block_mem V1) (bt: block_mem V2) btb h x1 x2,
    (mem_merges_to (AEQ:= handle_eq_dec)) bt bm btb ->
    (mem_merges_to (AEQ:= handle_eq_dec)) (upd bt h x1) (upd bm h x2) ((upd (AEQ:=handle_eq_dec)) btb h (x1,x2)).
Proof.
  unfold mem_merges_to, memmatch; intros.
  cleanup.
  split; intros.
  {
    split; intros.
   all: destruct (handle_eq_dec h h0); subst;
     [rewrite upd_eq in H1; eauto; congruence |
      rewrite upd_ne in H1; eauto;
      rewrite upd_ne; eauto;
      apply H; eauto].
  }
  {
    split; intros; cleanup.
    destruct (handle_eq_dec h h0); subst;
    [rewrite upd_eq in H1; eauto;
     rewrite upd_eq in H2; eauto; cleanup;
     apply upd_eq; eauto |
     rewrite upd_ne in H1; eauto;
     rewrite upd_ne in H2; eauto;
     rewrite upd_ne; eauto;
     apply H0; eauto].

    destruct (handle_eq_dec h h0); subst;
    [rewrite upd_eq in H1; eauto; cleanup;
     repeat rewrite upd_eq; eauto |
     rewrite upd_ne in H1; eauto;
     repeat rewrite upd_ne; eauto;
     apply H0; eauto].
  }
Qed.

Lemma combine_length_eq_refl_l:
  forall T1 T2 (l1: list T1) (l2: list T2) l3 l4,
    combine l1 l2 = combine l3 l4 ->
    length l1 = length l2 ->
    length l3 = length l4 ->
    l1 = l3.
Proof.
  induction l1; intros; simpl in *.
  destruct l3; eauto.
  destruct l4; simpl in *; congruence.
  destruct l2; simpl in *; try congruence.
  destruct l3; simpl in *; try congruence.
  destruct l4; simpl in *; try congruence.
  inversion H; subst.
  erewrite IHl1; eauto. 
Qed.

Lemma combine_length_eq_refl_r:
  forall T1 T2 (l2: list T2) (l1: list T1)  l3 l4,
    combine l1 l2 = combine l3 l4 ->
    length l1 = length l2 ->
    length l3 = length l4 ->
    l2 = l4.
Proof.
  induction l2; intros; simpl in *.
  destruct l4; eauto.
  rewrite ListUtils.combine_l_nil in H.
  destruct l3; simpl in *; try congruence.
  destruct l1; simpl in *; try congruence.
  destruct l4; simpl in *; try congruence.
  rewrite ListUtils.combine_l_nil in H; congruence.
  destruct l3; simpl in *; try congruence.
  inversion H; subst.
  erewrite IHl2; eauto. 
Qed.

Lemma combine_length_eq_refl:
  forall T1 T2 (l2: list T2) (l1: list T1)  l3 l4,
    combine l1 l2 = combine l3 l4 ->
    length l1 = length l2 ->
    length l3 = length l4 ->
    l1 = l3 /\ l2 = l4.
Proof.
  intros; split.
  eapply combine_length_eq_refl_l; eauto.
  eapply combine_length_eq_refl_r; eauto.
Qed.

Lemma disk_merges_to_upd:
  forall V1 V2 (dt: @mem addr addr_eq_dec (V1 * list V1)) (d: @mem addr addr_eq_dec (V2 * list V2)) dtb a x1 x2 l1 l2,
    (disk_merges_to (AEQ:= addr_eq_dec)) dt d dtb ->
    length l1 = length l2 ->
    (disk_merges_to (AEQ:= addr_eq_dec)) (upd dt a (x1, l1)) (upd d a (x2, l2)) ((upd (AEQ:=addr_eq_dec)) dtb a ((x1,x2), combine l1 l2)).
Proof.
  unfold disk_merges_to, diskmatch; intros.
  cleanup.
  split; intros.
  {
     destruct (addr_eq_dec a a0); subst.
     repeat rewrite upd_eq; eauto.
     right; do 2 eexists; eauto.
     repeat rewrite upd_ne; eauto.
  }
  {
    split; intros; cleanup.
    destruct (addr_eq_dec a a0); subst;
    [rewrite upd_eq in H2; eauto;
     rewrite upd_eq in H3; eauto; cleanup;
     rewrite upd_eq; eauto |
     rewrite upd_ne in H2; eauto;
     rewrite upd_ne in H3; eauto;
     rewrite upd_ne; eauto;
     apply H1; eauto].

    destruct (addr_eq_dec a a0); subst;
    [rewrite upd_eq in H2; eauto; cleanup;
     repeat rewrite upd_eq; eauto |
     rewrite upd_ne in H2; eauto;
     repeat rewrite upd_ne; eauto;
     apply H1; eauto].
    destruct ts, bs; simpl in *.
    apply combine_length_eq_refl in H7; eauto; cleanup; eauto.
    
  }
Qed.


Lemma disk_merges_to_some_eq:
  forall V1 V2 (dt: @mem addr addr_eq_dec (V1 * list V1)) (d: @mem addr addr_eq_dec (V2 * list V2))
    dtb a x1 x2 x3,
    (disk_merges_to (AEQ:= addr_eq_dec)) dt d dtb ->
    dt a = Some x1 ->
    d a = Some x2 ->
    dtb a = Some x3 ->
    x3 = (fst x1, fst x2, combine (snd x1) (snd x2)).
Proof.
  unfold disk_merges_to, diskmatch; intros.
  cleanup; specialize (H3 a x1 x2); destruct H3.  
  destruct H3; eauto. rewrite H3 in H2; cleanup; eauto.
Qed.


Lemma mem_merges_to_some_eq:
  forall V1 V2 (bm: block_mem V1) (bt: block_mem V2) btb h x1 x2 x3,
    (mem_merges_to (AEQ:= handle_eq_dec)) bt bm btb ->
    bt h = Some x1 ->
    bm h = Some x2 ->
    btb h = Some x3 ->
    x3 = (x1, x2).
Proof.
  unfold mem_merges_to, memmatch; intros.
  cleanup; specialize (H3 h); edestruct H3.
  destruct (btb h); try congruence; cleanup.
  destruct x3; simpl in *.
  assert (A: bt h = Some x1 /\ bm h = Some x2).
  eauto.
  specialize (H4 A); cleanup; auto.
Qed.


Lemma combine_split_length :
  forall T1 T2 (l1: list T1) (l2: list T2),
    split (combine l1 l2) = (l1, l2) ->
    length l1 = length l2.
Proof.
  induction l1; intros; simpl in *.
  inversion H; simpl in *; subst; eauto.
  destruct l2; simpl in *; try congruence.
  erewrite IHl1; eauto.
  destruct (split (combine l1 l2)); inversion H; eauto.
Qed.

Lemma disk_merges_to_none:
  forall V1 V2 (dt: @mem addr addr_eq_dec (V1 * list V1)) (d: @mem addr addr_eq_dec (V2 * list V2))
    dtb a,
    (disk_merges_to (AEQ:= addr_eq_dec)) dt d dtb ->
    dt a = None \/ d a = None ->
    dtb a = None.
Proof.
  unfold disk_merges_to, diskmatch; intros.
  cleanup; specialize (H1 a); specialize (H a).
  destruct H; cleanup.
  clear H0. destruct (dtb a); eauto.
  edestruct p, p0, H1.
  edestruct H3; eauto; cleanup.
  eassign (v, fst (split l));
    eassign (v0, snd (split l)); simpl.
  pose proof (split_combine l).
  destruct (split l) eqn:D; simpl in *; cleanup; eauto.
  apply combine_split_length in D; eauto.
  congruence.
  split_ors; congruence.
Qed.

Lemma disk_merges_to_some_length:
  forall V1 V2 (dt: @mem addr addr_eq_dec (V1 * list V1)) (d: @mem addr addr_eq_dec (V2 * list V2))
    dtb a x1 x2,
    (disk_merges_to (AEQ:= addr_eq_dec)) dt d dtb ->
    dt a = Some x1 ->
    d a = Some x2 ->
    length (vsmerge x1) = length (vsmerge x2).
Proof.
  unfold disk_merges_to, diskmatch; intros.
  cleanup; specialize (H a).
  destruct H; cleanup; try congruence.
  destruct x1, x2; simpl in *; eauto.
Qed.

Lemma combine_nil_either:
  forall T1 T2 (l1: list T1) (l2: list T2),
    combine l1 l2 = nil ->
    l1 = nil \/ l2 = nil.
Proof.
  intros; destruct l1; eauto; destruct l2; eauto; simpl in *; congruence.
Qed.

Lemma disk_merges_to_sync_mem:
  forall V1 V2 (dt: @mem addr addr_eq_dec (V1 * list V1)) (d: @mem addr addr_eq_dec (V2 * list V2)) (dtb: @mem addr addr_eq_dec ((V1 * V2) * list (V1 * V2))),
    (disk_merges_to (AEQ:= addr_eq_dec)) dt d dtb ->
    (disk_merges_to (AEQ:= addr_eq_dec)) (sync_mem dt) (sync_mem d) (sync_mem dtb).
Proof.
  unfold disk_merges_to, diskmatch, sync_mem; intros.
  cleanup.
  split; intros.
  {
    specialize (H a); split_ors; cleanup; eauto.
    destruct x, x0; right; do 2 eexists; eauto.
  }
  {
    specialize (H0 a).
    split; intros; cleanup; try congruence;
    edestruct H0.
    edestruct H1; eauto.
    rewrite H3; eauto.
    edestruct H3; eauto.
    eassign (fst ts, fst (split l));
    eassign (fst bs, snd (split l)); simpl.
    pose proof (split_combine l).
    destruct (split l) eqn:D0; simpl in *; cleanup; eauto.
    split; eauto.
    apply combine_split_length in D0; eauto.
    destruct ts, bs; simpl in *; cleanup; eauto.
    symmetry in H5; apply combine_nil_either in H5; split_ors; cleanup; simpl in *.
    symmetry in H2; apply length_zero_iff_nil in H2; cleanup; eauto.
    apply length_zero_iff_nil in H2; cleanup; eauto.
  }
Qed.






Lemma read_secure:
  forall pr a,
    {< tbs,
       PERM: pr
       PRE: bm, hm,
          a|+> tbs
       POST: bm', hm',
          RET: i
          (a|+> tbs * [[ bm i = None ]] *
           [[ bm' = upd bm i (fst tbs) ]])%pred
       CRASH: bm',  hm',
          a|+>tbs
     >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply ptsto_subset_valid' in H1; cleanup; eauto; simpl in *.
    eapply disk_merges_to_some_eq in H; eauto; cleanup.
    inversion H; cleanup; eauto.
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
  }
  split_ors; cleanup.
  {
    split.
    right; do 6 eexists; intuition.
    inv_exec_perm; eauto.
    inv_exec_perm; eauto.
    eapply H5.
    pred_apply; cancel; eauto.
    inv_exec_perm; cleanup; simpl; auto.
  }
  {
    inv_exec_perm.
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply ptsto_subset_valid' in H1; cleanup; eauto; simpl in *.
    eapply disk_merges_to_some_eq in H; eauto; cleanup.
    inversion H; cleanup; eauto.
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    split.
    right.
    split_ors; cleanup; try congruence.
    do 6 eexists; intuition eauto.
    try rewrite app_nil_r; eauto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm.
    apply ptsto_subset_valid' in H1; cleanup.
    eapply disk_merges_to_none in H; eauto; cleanup; congruence.    
  }
  {
    repeat inv_exec_perm; simpl in *; cleanup.
    try rewrite app_nil_r.
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply ptsto_subset_valid' in H1; cleanup; eauto; simpl in *.
    eapply disk_merges_to_some_eq in H; eauto; cleanup.
    inversion H; cleanup; eauto.
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_upd; eauto.
    eapply disk_merges_to_some_length; eauto.
    apply ptsto_subset_valid' in H1 as Hx; cleanup; eauto.
    eapply disk_merges_to_some_eq in H as Hx; eauto; simpl in *.
    eapply mem_merges_to_some_eq in H0 as Hy; eauto; simpl in *.
    inversion Hx; cleanup; clear Hx.
    eapply ptsto_subset_upd  with (v:= (t2, b1))(vs':= (fst ts, fst bs) :: combine (snd ts) (snd bs)) in H1.
    pred_apply; cancel; eauto.    
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; eauto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm.
    split; simpl; eauto.
    right; do 6 eexists; intuition eauto.
    eapply H5.
    pred_apply; cancel; eauto.
  }
  {
    inv_exec_perm.
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_upd; eauto.
    eapply disk_merges_to_some_length; eauto.
    apply ptsto_subset_valid' in H1 as Hx; cleanup; eauto.
    eapply disk_merges_to_some_eq in H as Hx; eauto; simpl in *.
    eapply mem_merges_to_some_eq in H0 as Hy; eauto; simpl in *.
    inversion Hx; cleanup; clear Hx.
    eapply ptsto_subset_upd  with (v:= (t1, b1))(vs':= (fst ts, fst bs) :: combine (snd ts) (snd bs)) in H1.
    pred_apply; cancel; eauto.    
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; eauto.
    try rewrite app_nil_r.
    split_ors; cleanup; try congruence.
    split; eauto.
    right; do  6 eexists; cleanup; eauto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm; cleanup.
    apply ptsto_subset_valid' in H1 as Hx; cleanup; eauto.
    split_ors.
    eapply mem_merges_to_none in H0; eauto; congruence.
    eapply disk_merges_to_none in H; eauto; congruence.
  }
  {
    inv_exec_perm; cleanup;
      try rewrite app_nil_r.
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_upd; eauto.
    eapply disk_merges_to_some_length; eauto.
    apply ptsto_subset_valid' in H1 as Hx; cleanup; eauto.
    eapply disk_merges_to_some_eq in H as Hx; eauto; simpl in *.
    eapply mem_merges_to_some_eq in H0 as Hy; eauto; simpl in *.
    inversion Hx; cleanup; clear Hx.
    eapply ptsto_subset_upd  with (v:= (t, b0))(vs':= (fst ts, fst bs) :: combine (snd ts) (snd bs)) in H1.
    pred_apply; cancel; eauto.    
    unfold vsmerge; simpl;
    apply ListUtils.incl_cons2; eauto.
  }
Qed.


Lemma seal_secure:
  forall pr t b,
    {!< F,
       PERM: pr
       PRE: bm, hm,
         (F * [[ t = Public ]])%pred
       POST: bm', hm',
          RET : i
          F * [[ bm i = None ]] *
          [[ bm' = upd bm i (t, b)]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     >!} Seal t b.
Proof.
  unfold corr2; intros.
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    rewrite app_nil_r.
    split; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    rewrite app_nil_r.
    split; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    rewrite app_nil_r.
    split; auto.
  }
Qed.


Lemma seal_secure_weak:
  forall pr t b,
    {!<W F,
       PERM: pr
       PRE: bm, hm,
         (F * [[ can_access pr t ]])%pred
       POST: bm', hm',
          RET : i
          F * [[ bm i = None ]] *
          [[ bm' = upd bm i (t, b)]]
       CRASH: bm'', hm'',
          false_pred (* Can't crash *)
     W>!} Seal t b.
Proof.
  unfold corr2_weak; intros.
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    rewrite app_nil_r.
    split; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    rewrite app_nil_r.
    split; auto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    eapply mem_merges_to_upd; eauto.
    pred_apply; cancel; eauto.    
    eapply mem_merges_to_none; eauto.      
    apply block_mem_subset_upd_none; eauto.
    eapply mem_merges_to_none; eauto.
    rewrite app_nil_r.
    split; auto.
  }
Qed.

Lemma unseal_secure:
  forall pr i,
     {!< F tb,
       PERM: pr
       PRE: bm, hm, 
         F * [[ fst tb = Public ]] *
         [[ bm i = Some tb ]]
       POST: bm', hm', RET : b
         F * [[ b = snd tb ]] *
         [[ bm' = bm ]]
       CRASH: bm'', hm'',
         false_pred (* Can't crash *)
     >!} Unseal i.
Proof.
  unfold corr2; intros.
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
  }
  split_ors; cleanup; inv_exec_perm; try congruence.
  {
    eapply mem_merges_to_none in H0; eauto; congruence.
  }
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
    split; auto.
    apply only_public_operations_app_merge; simpl; auto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
  }
Qed.


Lemma unseal_secure_weak:
  forall pr i,
     {!<W F tb,
       PERM: pr
       PRE: bm, hm, 
         F * [[ can_access pr (fst tb) ]] *
         [[ bm i = Some tb ]]
       POST: bm', hm', RET : b
         F * [[ b = snd tb ]] *
         [[ bm' = bm ]]
       CRASH: bm'', hm'',
         false_pred (* Can't crash *)
     W>!} Unseal i.
Proof.
  unfold corr2_weak; intros.
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
    split; auto.
    apply trace_secure_app; simpl; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; cleanup; eauto.
  }
  split_ors; cleanup; inv_exec_perm.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
    split; auto.
    apply trace_secure_app; simpl; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; cleanup; eauto.
  }
  split_ors; cleanup; inv_exec_perm; try congruence.
  {
    eapply mem_merges_to_none in H0; eauto; congruence.
  }
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; eauto.
    split; auto.
    apply trace_secure_app; simpl; eauto.
    eapply mem_merges_to_some_eq in H0; eauto.
    inversion H0; cleanup; eauto.
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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
     edestruct H6.
     4: eauto.
     all: eauto.
     pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
    pred_apply; cancel; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
     edestruct H6.
    4: eauto.
    all: eauto.
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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_sync_mem; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm.
    split.
    right; do 6 eexists; intuition eauto.
    eapply H5; pred_apply; cancel; eauto.
    simpl; auto.
  }
  {
    inv_exec_perm.
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_sync_mem; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
    try rewrite app_nil_r; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_sync_mem; eauto.
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
  destruct_lift H1; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup;
  try rewrite app_nil_r.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_sync_mem; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
  }
  split_ors; cleanup.
  {
    inv_exec_perm.
    split.
    right; do 6 eexists; intuition eauto.
    eapply H5; pred_apply; cancel; eauto.
    simpl; auto.
  }
  {
    inv_exec_perm.
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_sync_mem; eauto.
    repeat rewrite <- sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    apply sync_xform_pred_apply; auto.
    try rewrite app_nil_r; eauto.
  }
  split_ors; cleanup; inv_exec_perm;
  try rewrite app_nil_r.
  {
    edestruct H6.
    4: eauto.
    all: eauto.
    apply disk_merges_to_sync_mem; eauto.
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
Hint Extern 1 (corr2_weak _ _ (Bind (Seal _ _) _)) => apply seal_secure_weak : prog.
Hint Extern 1 (corr2_weak _ _ (Bind (Unseal _) _)) => apply unseal_secure_weak : prog.
Hint Extern 1 ({{_|_}} Bind (Auth _) _) => apply auth_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind Sync _)) => apply sync_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Ret _) _)) => apply ret_secure : prog.
Hint Extern 1 (corr2_weak _ _ (Bind (Ret _) _)) => apply ret_secure_weak : prog.














