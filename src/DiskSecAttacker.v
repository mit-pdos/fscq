Require Import Mem Word.
Require Import Omega.
Require Import Bool.
Require Import Pred.
Require Import Log GenSepN.
Require Import ListPred.
Require Import List ListUtils.
Require Import Bytes.
Require Import Rec.
Require Import Arith.
Require Import FSLayout.
Require Import Errno.
Require Import Lia.
Require Import FunctionalExtensionality.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import DirTree.
Require Import AsyncFS.
Require Import Prog ProgLoop ProgList.
Require Import ProgAuto.
Require Import DestructPair.
Require Import DiskSecDef.

Import ListNotations.
Set Implicit Arguments.


Ltac rewriteall :=
  match goal with
  | [H: ?x = ?x |- _ ] => clear H; repeat rewriteall
  | [H: ?x = ?y, H0: ?y = ?x |- _ ] => clear H0; repeat rewriteall
  | [H: ?x = _, H0: ?x = _ |- _ ] => rewrite H in H0; repeat rewriteall
  | [H: ?x = _, H0: _ = ?x |- _ ] => rewrite H in H0; repeat rewriteall
  end.


Ltac cleanup:= try split_match; try logic_clean; subst; try rewriteall;
               try clear_dup; try rewrite_upd_eq;
               try clear_dup; try some_subst;
               try clear_trace; subst; try rewriteall.

Theorem exec_equivalent_finished:
  forall T (p: prog T) pr tr d1 d2 bm1 bm2 hm d1' bm1' hm' (r: T),
    exec pr d1 bm1 hm p (Finished d1' bm1' hm' r) tr ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    trace_secure pr tr ->
    exists d2' bm2', exec pr d2 bm2 hm p (Finished d2' bm2' hm' r) tr /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    destruct bs.
    specialize H1 with (1:= can_access_public pr) as Hx;
    specialize (Hx r); intuition; cleanup; try congruence.
    specialize H0 with (1:= can_access_public pr) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    destruct x0, t0.
    unfold vsmerge in *; simpl in *.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    intros.
    simpl in *; eauto.
    specialize H0 with (1:= H) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    unfold vsmerge in *; simpl in *.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Write **)
    destruct b, bs, t; simpl in *.
    destruct (hm' n0) eqn: D.    
    destruct (can_access_dec pr t).
    { (** can access **)
      specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= c) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 2 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** can't access **)
      specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public pr) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 2 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      destruct (tag_dec t tag); subst; intuition.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; cleanup; intuition.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** inconsistent **)
      specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public pr) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 2 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; congruence.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
  }
  { (** Seal **)
    specialize H1 with (1:= can_access_public pr) as Hx;
    specialize (Hx r); intuition; cleanup; try congruence.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Unseal **)
    intuition.
    destruct b; simpl in *.
    specialize H1 with (1:= H) as Hx;
    specialize (Hx h); intuition; cleanup; try congruence.
    simpl in *; intuition; subst.
    do 2 eexists; split.
    econstructor; eauto.
    split; eauto.
  }
  { (** Sync **)
    repeat eexists; [econstructor; eauto| |eauto].
    unfold equivalent_for in *; intros.
    specialize H0 with (1:= H) as Hx.
    unfold sync_mem.
    specialize (Hx a); intuition; cleanup; eauto.
    repeat match goal with
           | [H: ?x = _ |- context [?x] ] => rewrite H
           end; eauto.
    repeat match goal with
           | [H: ?x = _ |- context [?x] ] => rewrite H
           end; eauto.
    destruct x, x0.
    unfold vsmerge in *; simpl in *; eauto.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    right; repeat eexists; simpl; eauto.    
  }
  { (** ChDom **)
    cleanup.
    specialize H0 with (1:= H) as Hdt'.
    specialize H1 with (1:= H) as Hbt'.
    repeat eexists; [econstructor; eauto| |eauto].
    {
      unfold equivalent_for in *; intros.
      specialize (Hdt' a); intuition; cleanup; eauto.
      specialize H0 with (1:= H3) as Hx.
      specialize (Hx a); intuition; cleanup; eauto.
      repeat match goal with
             | [H: ?x = _ |- context [?x] ] => rewrite H
             end; eauto.
      destruct x1, x2.
      right; repeat eexists; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
      destruct (addr_eq_dec n (fst t0)); subst.
      - econstructor; eauto.
        eapply forall_forall2.
        rewrite Forall_forall; intros.
        destruct (addr_eq_dec (fst t0) (fst (fst x))); subst.
        + cleanup.
          rewrite Mem.upd_eq in H7; eauto.
          cleanup.
          eapply forall2_forall in H17; rewrite Forall_forall in H17; eauto.
          eapply H17; eauto.
          setoid_rewrite <- H11; eauto.
        + rewrite Mem.upd_ne in H7; eauto.
          cleanup.
          eapply forall2_forall in H15; rewrite Forall_forall in H15; eauto.
        + eapply forall2_length; eauto.
      - cleanup.
        econstructor; eauto.
        rewrite Mem.upd_ne; eauto.
        eapply forall_forall2.
        rewrite Forall_forall; intros.
        destruct (addr_eq_dec n (fst (fst x))); subst.
        + rewrite Mem.upd_eq in H7; eauto.
          cleanup.
          eapply forall2_forall in H17; rewrite Forall_forall in H17; eauto.
        + rewrite Mem.upd_ne in H7; eauto.
          cleanup.
          eapply forall2_forall in H15; rewrite Forall_forall in H15; eauto.
        + eapply forall2_length; eauto.
    }
    {
      unfold blockmem_equivalent_for in *; intros.
      specialize (Hbt' a); intuition; cleanup; eauto.
      specialize H1 with (1:= H3) as Hx.
      specialize (Hx a); intuition; cleanup; eauto.
      repeat match goal with
             | [H: ?x = _ |- context [?x] ] => rewrite H
             end; eauto.
      destruct x1, x2.
      right; repeat eexists; eauto.
      simpl in *; eauto.
      destruct (addr_eq_dec n n0); subst.
      rewrite Mem.upd_eq; eauto.
      rewrite Mem.upd_ne; eauto.
    }
  }
  { (** Bind **)
    apply trace_secure_app_split in H3; cleanup.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H5); cleanup.
    specialize H with (1:=H4)(2:=H7)(3:=H8)(4:=H3); cleanup.
    repeat eexists; [econstructor; eauto| |]; eauto.
  }

  Unshelve.
  all: try exact addr; eauto.
  all: try exact nil.
  all: try exact eq.
Qed.


Theorem exec_equivalent_crashed:
  forall T (p: prog T) pr tr d1 d2 bm1 bm2 hm d1' bm1' hm',
    exec pr d1 bm1 hm p (Crashed d1' bm1' hm') tr ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    trace_secure pr tr ->
    exists d2' bm2', exec pr d2 bm2 hm p (Crashed d2' bm2' hm') tr /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm').
Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Bind **)
    intuition.
    { (** p Crashed **)
      specialize IHp with (1:=H4)(2:=H1)(3:=H2)(4:=H3); cleanup.
      do 2 eexists; split.
      eapply CrashBind; eauto.
      eauto.
    }
    { (** p0 crashed **)
      cleanup.
      apply trace_secure_app_split in H3; cleanup.
      eapply exec_equivalent_finished in H0; eauto; cleanup.
      specialize H with (1:=H4)(2:=H6)(3:=H7)(4:=H3); cleanup.
      do 2 eexists; split.
      econstructor; eauto.
      eauto.
    }
  }
Qed.

Theorem exec_equivalent_failed:
  forall T (p: prog T) pr tr d1 d2 bm1 bm2 hm,
    exec pr d1 bm1 hm p Failed tr ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    trace_secure pr tr ->
    exec pr d2 bm2 hm p Failed tr.
Proof.
  induction p; intros;  
    inv_exec_perm; cleanup; simpl in *;
  try solve [econstructor; eauto].
  { (** Read **)
    specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
    econstructor; eauto.
  }
  { (** Write **)
    econstructor; eauto.
    split_ors.
    specialize H1 with (1:= can_access_public pr) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
    specialize H0 with (1:= can_access_public pr) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
  }
  { (** Unseal **)
    econstructor; eauto.
    split_ors.
    specialize H1 with (1:= can_access_public pr) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
    specialize H1 with (1:= can_access_public pr) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
    right; eexists; split; eauto.
    rewrite <- H6; eauto.
  }
  { (** Bind **)
    split_ors; eauto.
    econstructor; eauto.
    
    apply trace_secure_app_split in H3; cleanup.
    eapply exec_equivalent_finished in H0; eauto.
    cleanup; eauto.
    eapply ExecBind; eauto.
  }
Qed.

Theorem exec_equivalent:
  forall T (p: prog T) pr tr d1 d2 bm1 bm2 hm (out: @result T),
    exec pr d1 bm1 hm p out tr ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    trace_secure pr tr ->
    
    (exists d1' bm1' hm' (r: T), out = Finished d1' bm1' hm' r /\
     exists d2' bm2', exec pr d2 bm2 hm p (Finished d2' bm2' hm' r) tr /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm')) \/
    
    (exists d1' bm1' hm', out = Crashed d1' bm1' hm' /\
     exists d2' bm2', exec pr d2 bm2 hm p (Crashed d2' bm2' hm') tr /\
     (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
     (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm')) \/
    
    (exec pr d2 bm2 hm p Failed tr).
Proof.
  intros.
  destruct out.
  left; do 4 eexists; split; eauto.
  eapply exec_equivalent_finished; eauto.
  right; left; do 3 eexists; split; eauto.
  eapply exec_equivalent_crashed; eauto.  
  right; right; eauto.
  eapply exec_equivalent_failed; eauto.  
Qed.


Theorem exec_equivalent_rfinished:
  forall T T' (p1: prog T) (p2: prog T') pr tr d1 d2 bm1 bm2 hm d1' bm1' hm' (r: T),
    exec_recover pr d1 bm1 hm p1 p2 (RFinished T' d1' bm1' hm' r) tr ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    trace_secure pr tr ->
    exists d2' bm2',
      exec_recover pr d2 bm2 hm p1 p2 (RFinished T' d2' bm2' hm' r) tr /\
      (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
      (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm').
Proof.
  intros.
  inversion H; subst.
  eapply exec_equivalent_finished in H14; eauto; cleanup.
  exists x, x0; split; eauto.
  econstructor; eauto.
Qed.

Theorem exec_equivalent_rfailed:
  forall T T' (p1: prog T) (p2: prog T') pr tr d1 d2 bm1 bm2 hm,
    exec_recover pr d1 bm1 hm p1 p2 (RFailed T T') tr ->
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    trace_secure pr tr ->
    exec_recover pr d2 bm2 hm p1 p2 (RFailed T T') tr.
Proof.
  intros.
  inversion H; subst.
  econstructor; eauto.
  eapply exec_equivalent_failed; eauto.  
Qed.



Theorem exec_equivalent_recover:
  forall T T' (p1: prog T) (p2: prog T') pr tr d1 bm1 hm out,
    exec_recover pr d1 bm1 hm p1 p2 out tr ->
    trace_secure pr tr ->
    forall d2 bm2,
    (forall tag, can_access pr tag -> equivalent_for tag d1 d2 hm) ->
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1 bm2 hm) ->
    
    (exists d1' bm1' hm' r, out = RFinished T' d1' bm1' hm' r /\
     exists d2' bm2', exec_recover pr d2 bm2 hm p1 p2 (RFinished T' d2' bm2' hm' r) tr /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm')) \/

    (out = RFailed T T' /\ exec_recover pr d2 bm2 hm p1 p2 (RFailed T T') tr) \/
    
    (exists d1' bm1' hm' r, out = RRecovered T d1' bm1' hm' r /\
     exists d2' bm2', exec_recover pr d2 bm2 hm p1 p2 (RRecovered T d2' bm2' hm' r) tr /\
    (forall tag, can_access pr tag -> equivalent_for tag d1' d2' hm') /\
    (forall tag, can_access pr tag -> blockmem_equivalent_for tag bm1' bm2' hm')).
Proof.
  induction 1; intros.
  { (** p1 Finished **)
    left; do 4 eexists; split; eauto.
    eapply exec_equivalent_rfinished; eauto.
    econstructor; eauto.
  }
  { (** p1 Failed **)
    right; left; split; eauto.
    eapply exec_equivalent_rfailed; eauto.
    econstructor; eauto.
  }
  { (** p1 Crashed then p2 Finished **)
    clear IHexec_recover.
    apply trace_secure_app_split in H2; cleanup.
    eapply exec_equivalent_crashed in H; eauto; cleanup.
    eapply possible_crash_equivalent in H6 as Hx; eauto; cleanup.
    eapply exec_equivalent_rfinished in H1; eauto; cleanup.
    (* eapply exec_equivalent_finished in H16 as Hp2; eauto; cleanup. *)
    right; right; do 4 eexists; split; eauto.
    do 2 eexists; split; eauto.
    econstructor; eauto.
    - intros; unfold blockmem_equivalent_for in *; intros.
      unfold empty_mem; simpl; eauto.
  }
  { (** p1 Crashed then p2 Crashed **)
    right; right; do 4 eexists; split; eauto.
    apply trace_secure_app_split in H2; cleanup.
    eapply exec_equivalent_crashed in H; eauto; cleanup.
    eapply possible_crash_equivalent in H6 as Hx; eauto; cleanup.
    specialize IHexec_recover with (1:=H2).
    edestruct IHexec_recover.
    {
      intros; unfold equivalent_for in *; intros.
      specialize (H9 _ H10).
      specialize (H9 a); split_ors; eauto.
      right; do 2 eexists; intuition eauto.
    }
    {
      eassign (@empty_mem handle handle_eq_dec tagged_block).
      intros; unfold blockmem_equivalent_for in *; intros.
      unfold empty_mem; simpl; eauto.
    }
   
    all: cleanup; try congruence.
    intuition; cleanup; try congruence.
    inversion H10; subst; clear H10.
    do 2 eexists; split; eauto.
    eapply XRCrashedRecovered; eauto.
  }
Qed.


  Lemma exec_equivalent_for_viewer_finished:
  forall T (p: prog T) caller viewer d d' bm bm' hm d1 bm1 hm1 r1 tr,
    exec caller d bm hm p (Finished d1 bm1 hm1 r1) tr ->
    (forall tag, can_access viewer tag -> equivalent_for tag d d' hm) ->
    (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm bm' hm) ->
    only_public_operations tr ->
    exists d2 bm2 tr2,
      exec caller d' bm' hm p (Finished d2 bm2 hm1 r1) tr2 /\
      (forall tag, can_access viewer tag -> equivalent_for tag d1 d2 hm1) /\
      (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm1 bm2 hm1).
  Proof.
     induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    destruct bs.
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx r1); intuition; cleanup; try congruence.
    specialize H0 with (1:= can_access_public viewer) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    destruct x0, t0.
    unfold vsmerge in *; simpl in *.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    do 3 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r1); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    split; eauto.
    split; eauto.
    split; eauto.
    intros.
    simpl in *; eauto.
    specialize H0 with (1:= H) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    unfold vsmerge in *; simpl in *.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Write **)
    destruct b, bs, t; simpl in *.
    destruct (hm1 n0) eqn: D.    
    destruct (can_access_dec viewer t).
    { (** can access **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= c) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** can't access **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public viewer) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      destruct (tag_dec t tag); subst; intuition.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; cleanup; intuition.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
    { (** inconsistent **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      specialize H1 with (1:= can_access_public viewer) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      destruct x0, x1; simpl in *; cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      split; eauto.
      unfold equivalent_for; intros.
      specialize H0 with (1:= H) as Hx;
      specialize (Hx n); destruct Hx; cleanup; try congruence.
      destruct (addr_eq_dec a n); subst.
      right.
      repeat rewrite Mem.upd_eq; eauto.
      do 2 eexists; eauto.
      split; eauto.
      split; eauto.
      split.
      unfold vsmerge in *; simpl in *; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      econstructor.
      simpl; intros; congruence.
      eauto.
      repeat rewrite Mem.upd_ne; eauto.
      eapply H0; eauto.
    }
  }
  { (** Seal **)
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx r1); intuition; cleanup; try congruence.
    do 3 eexists; split.
    econstructor; eauto.
    split; eauto.
    unfold blockmem_equivalent_for; intros.
    destruct (handle_eq_dec a r1); subst.
    right.
    repeat rewrite Mem.upd_eq; eauto.
    do 2 eexists; eauto.
    repeat rewrite Mem.upd_ne; eauto.
    eapply H1; eauto.
  }
  { (** Unseal **)
    intuition.
    destruct b; simpl in *.
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx h); intuition; cleanup; try congruence.
    simpl in *; intuition; subst.
    do 3 eexists; split.
    econstructor; eauto.
    split; eauto.
  }
  { (** Sync **)
    repeat eexists; [econstructor; eauto| |eauto].
    unfold equivalent_for in *; intros.
    specialize H0 with (1:= H) as Hx.
    unfold sync_mem.
    specialize (Hx a); intuition; cleanup; eauto.
    repeat match goal with
           | [H: ?x = _ |- context [?x] ] => rewrite H
           end; eauto.
    repeat match goal with
           | [H: ?x = _ |- context [?x] ] => rewrite H
           end; eauto.
    destruct x, x0.
    unfold vsmerge in *; simpl in *; eauto.
    repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
    right; repeat eexists; simpl; eauto.    
  }
  { (** ChDom **)
    cleanup.
    specialize H0 with (1:= can_access_public viewer) as Hdt'.
    specialize H1 with (1:= can_access_public viewer) as Hbt'.
    repeat eexists; [econstructor; eauto| |eauto].
    {
      unfold equivalent_for in *; intros.
      specialize (Hdt' a); intuition; cleanup; eauto.
      specialize H0 with (1:= H) as Hx.
      specialize (Hx a); intuition; cleanup; eauto.
      repeat match goal with
             | [H: ?x = _ |- context [?x] ] => rewrite H
             end; eauto.
      destruct x1, x2.
      right; repeat eexists; eauto.
      unfold vsmerge in *; simpl in *; eauto.
      repeat (denote (Forall2 _ (_::_)(_::_)) as Hf; inversion Hf; clear Hf; subst).
      destruct (addr_eq_dec n (fst t0)); subst.
      - econstructor; eauto.
        eapply forall_forall2.
        rewrite Forall_forall; intros.
        destruct (addr_eq_dec (fst t0) (fst (fst x))); subst.
        + cleanup.
          rewrite Mem.upd_eq in H6; eauto.
          cleanup.
          eapply forall2_forall in H16; rewrite Forall_forall in H16; eauto.
          eapply H16; eauto.
          setoid_rewrite <- H10; eauto.
        + rewrite Mem.upd_ne in H6; eauto.
          cleanup.
          eapply forall2_forall in H13; rewrite Forall_forall in H13; eauto.
        + eapply forall2_length; eauto.
      - cleanup.
        econstructor; eauto.
        rewrite Mem.upd_ne; eauto.
        eapply forall_forall2.
        rewrite Forall_forall; intros.
        destruct (addr_eq_dec n (fst (fst x))); subst.
        + rewrite Mem.upd_eq in H6; eauto.
          cleanup.
          eapply forall2_forall in H16; rewrite Forall_forall in H16; eauto.
        + rewrite Mem.upd_ne in H6; eauto.
          cleanup.
          eapply forall2_forall in H13; rewrite Forall_forall in H13; eauto.
        + eapply forall2_length; eauto.
    }
    {
      unfold blockmem_equivalent_for in *; intros.
      specialize (Hbt' a); intuition; cleanup; eauto.
      specialize H1 with (1:= H) as Hx.
      specialize (Hx a); intuition; cleanup; eauto.
      repeat match goal with
             | [H: ?x = _ |- context [?x] ] => rewrite H
             end; eauto.
      destruct x1, x2.
      right; repeat eexists; eauto.
      simpl in *; eauto.
      destruct (addr_eq_dec n n0); subst.
      rewrite Mem.upd_eq; eauto.
      rewrite Mem.upd_ne; eauto.
    }
  }
  { (** Bind **)
    apply only_public_operations_app in H3; cleanup.
    specialize IHp with (1:=H0)(2:=H1)(3:=H2)(4:=H5); cleanup.
    specialize H with (1:=H4)(2:=H7)(3:=H8)(4:=H3); cleanup.
    repeat eexists; [econstructor; eauto| |]; eauto.
  }

  Unshelve.
  all: try exact addr; eauto.
  all: try exact nil.
  all: try exact eq.
Qed.


  Lemma exec_equivalent_for_viewer_failed:
  forall T (p: prog T) caller viewer d d' bm bm' hm tr,
    exec caller d bm hm p Failed tr ->
    (forall tag, can_access viewer tag -> equivalent_for tag d d' hm) ->
    (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm bm' hm) ->
    only_public_operations tr ->
    exists tr2, exec caller d' bm' hm p Failed tr2.
  Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Read **)
    specialize H0 with (1:= can_access_public viewer) as Hx;
    specialize (Hx n); intuition; cleanup; try congruence.
    eexists; econstructor; eauto.
  }
  { (** Write **)
    intuition.
    { (** bm1 h = None **)
      specialize H1 with (1:= can_access_public viewer) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
      eexists; econstructor; eauto.
    }
    { (** d1 n = None **)
      specialize H0 with (1:= can_access_public viewer) as Hx;
      specialize (Hx n); intuition; cleanup; try congruence.
      eexists; econstructor; eauto.
    }
  }
  { (** Unseal **)
    eexists; econstructor; eauto.
    split_ors.
    specialize H1 with (1:= can_access_public viewer) as Hx;
    specialize (Hx h); intuition; cleanup; try congruence.
    
    specialize H1 with (1:= can_access_public viewer) as Hx;
      specialize (Hx h); intuition; cleanup; try congruence.
    right; eexists; econstructor; eauto.
    rewrite <- H6; eauto.
  }
  { (** ChDom **)
    eexists; econstructor; eauto.
  }
  { (** Bind **)
    intuition.
    { (** p Failed **)
      specialize IHp with (1:=H4)(2:=H1)(3:=H2)(4:=H3); cleanup.
      eexists.
      eapply FailBind; eauto.
    }
    { (** p0 Failed **)
      cleanup.
      apply only_public_operations_app in H3; cleanup.
      eapply exec_equivalent_for_viewer_finished in H0; eauto; cleanup.
      specialize H with (1:=H4)(2:=H6)(3:=H7)(4:=H3); cleanup.
      eexists; econstructor; eauto.
    }
  }
  Qed.

  Lemma exec_equivalent_for_viewer_crashed:
  forall T (p: prog T) caller viewer d d' bm bm' hm d1 bm1 hm1 tr,
    exec caller d bm hm p (Crashed d1 bm1 hm1) tr ->
    (forall tag, can_access viewer tag -> equivalent_for tag d d' hm) ->
    (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm bm' hm) ->
    only_public_operations tr ->
    exists d2 bm2 tr2,
      exec caller d' bm' hm p (Crashed d2 bm2 hm1) tr2 /\
      (forall tag, can_access viewer tag -> equivalent_for tag d1 d2 hm1) /\
      (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm1 bm2 hm1).
  Proof.
  induction p; intros;  
  inv_exec_perm; cleanup; simpl in *;
  try solve [repeat eexists; [econstructor; eauto|eauto|eauto] ].
  { (** Bind **)
    intuition.
    { (** p Crashed **)
      specialize IHp with (1:=H4)(2:=H1)(3:=H2)(4:=H3); cleanup.
      do 3 eexists; split.
      eapply CrashBind; eauto.
      eauto.
    }
    { (** p0 crashed **)
      cleanup.
      apply only_public_operations_app in H3; cleanup.
      eapply exec_equivalent_for_viewer_finished in H0; eauto; cleanup.
      specialize H with (1:=H4)(2:=H6)(3:=H7)(4:=H3); cleanup.
      do 3 eexists; split.
      econstructor; eauto.
      eauto.
    }
  }
Qed.


Lemma exec_equivalent_for_viewer:
  forall T (p: prog T) caller viewer d d' bm bm' hm res tr,
    exec caller d bm hm p res tr ->
    (forall tag, can_access viewer tag -> equivalent_for tag d d' hm) ->
    (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm bm' hm) ->
    only_public_operations tr ->
     (exists d1 bm1 hm1 r1, res = Finished d1 bm1 hm1 r1 /\ 
      exists d2 bm2 tr2, exec caller d' bm' hm p (Finished d2 bm2 hm1 r1) tr2 /\
      (forall tag, can_access viewer tag -> equivalent_for tag d1 d2 hm1) /\
      (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm1 bm2 hm1)) \/
      
      (exists d1 bm1 hm1, res = Crashed d1 bm1 hm1 /\
       exists d2 bm2 tr2, exec caller d' bm' hm p (Crashed d2 bm2 hm1) tr2 /\
      (forall tag, can_access viewer tag -> equivalent_for tag d1 d2 hm1) /\
      (forall tag, can_access viewer tag -> blockmem_equivalent_for tag bm1 bm2 hm1)) \/
      
      (res = Failed /\
       exists tr2, exec caller d' bm' hm p Failed tr2).
Proof.
  intros.
  destruct res.
  left; do 4 eexists; split; eauto.
  eapply exec_equivalent_for_viewer_finished; eauto.
  right; left; do 3 eexists; split; eauto.
  eapply exec_equivalent_for_viewer_crashed; eauto.
  right; right; split; eauto.
  eapply exec_equivalent_for_viewer_failed; eauto.
Qed.