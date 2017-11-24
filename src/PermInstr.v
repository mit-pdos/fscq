Require Import Pred Mem.
Require Export PermSepAuto.

Lemma bind_secure:
  forall T T' (p1: prog T) (p2: T -> prog T') pr d bm,
    permission_secure d bm pr p1 ->
    (forall d' bm' tr tr' r,
       exec pr tr d bm p1 (Finished d' bm' r) tr' ->
       permission_secure d' bm' pr (p2 r)) ->
    permission_secure d bm pr (Bind p1 p2).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; destruct r; cleanup.
  {
    specialize (trace_app H1); intros; cleanup.
    specialize (H _ _ _ H1); cleanup.
    specialize (trace_app H2); intros; cleanup.
    specialize (H0 _ _ _ _ _ H1); cleanup.
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
    specialize (H0 _ _ _ _ _ H1); cleanup.
    rewrite <- app_assoc in H2;
    specialize (H0 _ _ _ H2); cleanup.
    apply trace_secure_app; auto.
  }
Qed.

Lemma permission_drop_secure:
  forall d bm pr1 pr2 T (p: prog T),
    permission_secure d bm pr1 p ->
    permitted pr2 pr1 ->
    (forall tr tr2 r, exec pr2 tr d bm  p r (tr2++tr) ->
                      exists tr1, exec pr1 tr d bm  p r (tr1++tr) /\ trace_match tr1 tr2) ->
    permission_secure d bm pr2 p.
Proof.
  unfold permission_secure; intros.
  specialize (H1 _ _ _ H2); cleanup.
  specialize (H _ _ _ H1); intuition.
  eapply trace_secure_match; eauto.
Qed.


Lemma read_secure:
  forall pr a,
    {< tb tbs F,
       PERM: pr
       PRE: bm
          (F * a|-> (tb, tbs))%pred
       POST: bm'
          RET: i
          (F * a|-> (tb, tbs) * [[ bm i = None ]] *
           [[ bm' = upd (AEQ:= PeanoNat.Nat.eq_dec) bm i tb ]])%pred
       CRASH:
         (F * a|->(tb, tbs))%pred
     >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  destruct out; cleanup.
  {
    inv_exec_perm.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_valid' in H; cleanup; eauto.  
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
    apply ptsto_valid' in H; cleanup; eauto.
  }
  split_ors; cleanup.
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    pred_apply; cancel.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_valid' in H; cleanup; eauto.
  }
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    apply ptsto_valid' in H; cleanup; eauto.
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
    apply ptsto_valid' in H; cleanup; eauto.
  }
Qed.

Lemma write_secure:
  forall pr a i,
    {< F tb tbs,
       PERM: pr
       PRE: bm
          (F * a|->tbs * [[ bm i = Some tb ]])%pred
       POST: bm'
          RET: tt
          (F * a|->(tb, vsmerge tbs) * [[ bm' = bm ]])%pred
       CRASH:
          (F * a|->tbs)%pred
     >} Write a i.
Proof.
  unfold corr2; intros.
   destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  destruct out; cleanup.
  {
    inv_exec_perm.
    edestruct H4; eauto.
    apply ptsto_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_upd' with (v:= (tb, vsmerge tbs)) in H;
    pred_apply; cancel.
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
    pred_apply; cancel.
    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    apply ptsto_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_upd' with (v:= (tb, vsmerge tbs)) in H;
    pred_apply; cancel.
  }
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    edestruct H4; eauto.
    apply ptsto_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_upd' with (v:= (tb, vsmerge tbs)) in H;
    pred_apply; cancel.
    apply ptsto_valid' in H; cleanup; eauto.
    split_ors; cleanup; try congruence.
    inversion H0; cleanup; eauto.

    eapply bind_secure; intuition.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    simpl; eauto.
    simpl; eauto.
    unfold permission_secure; intros.
    inv_exec_perm; cleanup; auto.
    edestruct H4; eauto.
    apply ptsto_valid' in H as Hx; cleanup; eauto.
    eapply ptsto_upd' with (v:= (tb0, vsmerge tbs0)) in H;
    pred_apply; cancel.
  }
Qed.


Lemma seal_secure:
  forall pr t b,
    {< X,
       PERM: pr
       PRE: bm
          [[ can_access pr t ]]
       POST: bm'
          RET : i
          [[ bm i = None ]] *
          [[ bm' = upd (AEQ:= PeanoNat.Nat.eq_dec) bm i (t, b)]]
       CRASH:
          emp
     >} Seal t b.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
 destruct out; cleanup.
  {
    inv_exec_perm.
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
  split_ors; cleanup.
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    pred_apply; cancel.
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
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
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
     {< tb,
       PERM: pr
       PRE: bm
         [[ can_access pr (fst tb) ]] *
         [[ bm i = Some tb ]]
       POST: bm' RET : b
         [[ b = snd tb ]] *
         [[ bm' = bm ]]
       CRASH:
        emp
     >} Unseal i.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  destruct out; cleanup.
  {
    inv_exec_perm.
    edestruct H4; eauto.
    pred_apply; cancel; eauto.
    destruct tb; cleanup; auto.
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
  split_ors; cleanup.
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    pred_apply; cancel.
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
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    destruct tb; cleanup; auto.
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

Lemma ret_secure:
  forall T pr (v: T),
     {< X,
       PERM: pr
       PRE: bm
         emp
       POST: bm' RET : r
         [[ r = v ]] *
         [[ bm' = bm ]]
       CRASH:
         emp
     >} Ret v.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
   destruct out; cleanup.
  {
    inv_exec_perm.
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
  split_ors; cleanup.
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
    pred_apply; cancel.
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
  {
    split.
    right; eexists; intuition.
    inv_exec_perm.
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

(*
Lemma exec_trace_irrelevance:
  forall T (p: prog T) pr tr tr' tr'' d bm r,
    exec pr tr d bm p r (tr'++tr) ->
    exec pr tr'' d bm p r (tr'++tr'').
Proof.
  induction p; intros;
  repeat inv_exec_perm; simpl in *; cleanup;
  try solve [ econstructor; eauto].
  specialize (trace_app H8); intros; cleanup.
  constructor; eauto.
  specialize (trace_app H0); intros; cleanup.
  specialize (trace_app H1); intros; cleanup.
  econstructor; eauto.
  eapply IHp; eauto.
  rewrite <- app_assoc in *; eapply H; eauto.
Qed.

Lemma exec_permission_drop:
  forall T (p: prog T) pr pr' d bm tr r tr',
    exec pr' tr d bm p r tr' ->
    permitted pr pr' ->
    exists tr'', exec pr tr d bm p r tr''.
Proof.
  induction p; intros;
  repeat inv_exec_perm; simpl in *; cleanup;
  try solve [ eexists; econstructor; eauto ].
  specialize (trace_app H0); intros; cleanup.
  specialize (trace_app H2); intros; cleanup.
  specialize (IHp _ _ _ _ _ _ _ H0 H1); cleanup.
  specialize (H _ _ _ _ _ _ _ _ H2 H1); cleanup.
  specialize (trace_app H3); intros; cleanup.
  specialize (trace_app H); intros; cleanup.
  eexists; econstructor; eauto.
  eapply exec_trace_irrelevance; eauto.
Qed.


Lemma exec_trace_match:
  forall T (p: prog T) pr1 pr2 tr tr1 tr2 d bm r,
    exec pr2 tr d bm  p r (tr2++tr) ->
    exec pr1 tr d bm  p r (tr1++tr) ->
    trace_match pr1 pr2 tr1 tr2.
Proof.
  induction p; intros; repeat inv_exec_perm; subst;
  try solve [ (rewrite H10 in H12
             || rewrite H7 in H11
             || rewrite H5 in H8); clear_trace; cleanup; apply trace_match_refl];
  try solve [ clear_trace; cleanup; apply trace_match_refl].
  specialize (trace_app H8); intros; cleanup.
  specialize (trace_app H9); intros; cleanup.
  simpl; intuition eauto.
  eapply IHp; eauto.
  rewrite <- app_assoc; eapply H; eauto.
Qed.
*)


Hint Extern 1 (corr2 _ _ (Bind (Read _) _)) => apply read_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Write _ _) _)) => apply write_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Seal _ _) _)) => apply seal_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Unseal _) _)) => apply unseal_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Ret _) _)) => apply ret_secure : prog.