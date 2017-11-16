Require Import Pred Mem.
Require Export PermSec PermHoare PermSepAuto.


Lemma bind_secure:
  forall T T' (p1: prog T) (p2: T -> prog T') pr d bm,
    permission_secure d bm pr p1 ->
    (forall d' bm' tr tr' r,
       exec pr tr d bm p1 (Finished d' bm' r) tr' ->
       permission_secure d' bm' pr (p2 r)) ->
    permission_secure d bm pr (Bind p1 p2).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm.
  specialize (trace_app H1); intros; cleanup.
  specialize (H _ _ _ H1); cleanup.
  specialize (trace_app H2); intros; cleanup.
  specialize (H0 _ _ _ _ _ H1); cleanup.
  rewrite <- app_assoc in H2;
  specialize (H0 _ _ _ H2); cleanup.
  apply trace_secure_app; auto.
Qed.

Lemma permission_drop_secure:
  forall d bm pr1 pr2 T (p: prog T),
    permission_secure d bm pr1 p ->
    permitted pr2 pr1 ->
    (forall tr tr2 r, exec pr2 tr d bm  p r (tr2++tr) ->
                      exists tr1, exec pr1 tr d bm  p r (tr1++tr) /\ trace_match pr1 pr2 tr1 tr2) ->
    permission_secure d bm pr2 p.
Proof.
  unfold permission_secure; intros.
  specialize (H1 _ _ _ H2); cleanup.
  specialize (H _ _ _ H1); intuition.
  eapply trace_secure_match; eauto.
Qed.


Lemma read_secure:
  forall pr a,
    {< tb F (bm': block_mem),
       PERM: pr
       PRE: fun bm =>
          (F * a|->tb * [[ bm = bm' ]])%pred
       POST: fun bm =>
          RET: i
          (F * a|->tb * [[ bm' i = None ]] *
          [[ bm = upd (AEQ:= PeanoNat.Nat.eq_dec) bm' i tb ]])%pred
     >} Read a.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  edestruct H3; eauto.
  pred_apply; cancel.
  apply ptsto_valid' in H; cleanup; eauto.
  
  intuition.
  eapply bind_secure; intuition.
  
  unfold permission_secure; intros.
  inv_exec_perm; cleanup; auto.
  simpl; eauto.
  
  unfold permission_secure; intros.
  clear H1.
  inv_exec_perm; cleanup; auto.
  edestruct H3; eauto.
  pred_apply; cancel; eauto.
  apply ptsto_valid' in H; cleanup; eauto.
Qed.

Lemma write_secure:
  forall pr a i,
    {< F tb tb' bm',
       PERM: pr
       PRE: fun bm =>
          (F * a|->tb' * [[ bm = bm' ]] * [[ bm i = Some tb ]])%pred
       POST: fun bm =>
          RET: tt
          (F * a|->tb * [[ bm = bm' ]])%pred
     >} Write a i.
Proof.
  unfold corr2; intros.
   destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  edestruct H3; eauto.
  admit.
  intuition eauto.
  eapply bind_secure; intuition.
  
  unfold permission_secure; intros.
  inv_exec_perm; cleanup; auto.
  simpl; eauto.

  unfold permission_secure; intros.
  clear H1.
  inv_exec_perm; cleanup; auto.
  edestruct H3; eauto.
  admit.
  Unshelve.
  auto.
Admitted.


Lemma seal_secure:
  forall pr t b,
    {< bm',
       PERM: pr
       PRE: fun bm =>
          ([[ can_access pr t ]] * [[ bm = bm' ]])%pred
       POST: fun bm =>
          RET : i
          [[ bm' i = None ]] *
          [[ bm = upd (AEQ:= PeanoNat.Nat.eq_dec) bm' i (t, b)]]
     >} Seal t b.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  edestruct H3; eauto.
  pred_apply; cancel.

  intuition eauto.
  eapply bind_secure; intuition.
  
  unfold permission_secure; intros.
  inv_exec_perm; cleanup; auto.
  simpl; eauto.

  unfold permission_secure; intros.
  clear H1.
  inv_exec_perm; cleanup; auto.
  edestruct H3; eauto.
  pred_apply; cancel.
Qed.

Lemma unseal_secure:
  forall pr i,
     {< tb bm',
       PERM: pr
       PRE: fun bm =>
         ([[ can_access pr (fst tb) ]] * [[ bm = bm' ]] * [[ bm i = Some tb ]])%pred
       POST: fun bm =>
          RET : b
          ([[ b = snd tb ]] * [[ bm = bm' ]])%pred
     >} Unseal i.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  edestruct H3; eauto.
  pred_apply; cancel.
  intuition eauto.
  eapply bind_secure; intuition.
  
  unfold permission_secure; intros.
  inv_exec_perm; cleanup; auto.
  simpl; eauto.

  unfold permission_secure; intros.
  clear H2.
  inv_exec_perm; cleanup; auto.
  edestruct H3; eauto.
  pred_apply; cancel.
Qed.

Lemma ret_secure:
  forall T pr (v: T),
     {< bm',
       PERM: pr
       PRE: fun bm =>
         [[ bm = bm' ]]
       POST: fun bm =>
          RET : r
          ([[ r = v ]] * [[ bm = bm' ]])
     >} Ret v.
Proof.
  unfold corr2; intros.
  destruct_lift H; cleanup.
  repeat inv_exec_perm; simpl in *; cleanup.
  edestruct H3; eauto.
  pred_apply; cancel.
  intuition eauto.
  eapply bind_secure; intuition.
  
  unfold permission_secure; intros.
  inv_exec_perm; cleanup; auto.
  simpl; eauto.

  unfold permission_secure; intros.
  clear H1.
  inv_exec_perm; cleanup; auto.
  edestruct H3; eauto.
  pred_apply; cancel.
Qed.

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

(*
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


(* not a right spec *)
Lemma run_secure:
  forall E T (p: prog T) pr pr' pre post,
     {< (e: E),
       PERM: pr'
       PRE: fun bm =>
         pre
       POST: fun bm =>
          post
     >} p ->
     {< (e:E),
       PERM: pr
       PRE: fun bm =>
         (pre * [[ permitted pr pr']])%pred
       POST: fun bm =>
          post
     >} Run pr' p.
Proof.
Abort.

Hint Extern 1 (corr2 _ _ (Bind (Read _) _)) => apply read_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Write _ _) _)) => apply write_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Seal _ _) _)) => apply seal_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Unseal _) _)) => apply unseal_secure : prog.
Hint Extern 1 (corr2 _ _ (Bind (Ret _) _)) => apply ret_secure : prog.