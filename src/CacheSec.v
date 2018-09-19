Require Import Mem List.
Require Import FMapAVL.
Require Import FMapFacts.
Require Import Word.
Require Import Pred.
Require Import WordAuto.
Require Import Omega.
Require Import ListUtils.
Require Import OrderedTypeEx.
Require Import Arith.
Require Import MapUtils.
Require Import ListPred. 
Require Import FunctionalExtensionality.
Require Import DestructPair DestructVarname.
Require Export CacheLemmas.


Import AddrMap.
Import Map MapFacts.
Import ListNotations.

Set Implicit Arguments.


Hint Resolve dummy_handle.

  Theorem writeback_ok' :
    forall a cs pr,
    {< vs0,
    PERM: pr                       
    PRE:bm, hm,
        a |+> vs0 * [[ forall hb, Map.find a (CSMap cs) = Some hb -> exists v, bm (fst hb) = Some v ]]
    POST:bm', hm',  RET:cs'
      [[ bm' = bm ]] *
      exists h v,
      ([[ Map.find a (CSMap cs) = Some (h, true) /\ bm' h = Some v /\
          cs' = mk_cs (Map.add a (h, false) (CSMap cs))
                      (CSMaxCount cs) (CSCount cs) (CSEvict cs) ]] *
         a |+> (v, vsmerge vs0)) \/
      ([[ (Map.find a (CSMap cs) = None \/
           Map.find a (CSMap cs) = Some (h, false)) /\ cs' = cs ]] * a |+> vs0) 
    CRASH:bm'', hm'',
       a |+> vs0
    >} writeback a cs.
  Proof.
    unfold writeback; intros.
    prestep.
    norml.
    edestruct H6; eauto; cleanup; simpl in *.
    cancel; eauto; try cancel.
    hoare.

    cancel.
    hoare.
    cancel.
    cancel.
    hoare.
    cancel.

    Unshelve.
    all:eauto.
  Qed.

  
Theorem writeback_ok :
  forall a cs pr,
    {< d,
     PERM: pr
     PRE: bm, hm,
       rep cs d bm
     POST: bm', hm',
       RET:cs'
          rep cs' d bm' * [[ bm' = bm ]] *
          [[ forall a, find a (CSMap cs) = None ->
              find a (CSMap cs') = None ]] * 
          [[ addr_clean (CSMap cs') a ]] * 
          [[ In a (CSMap cs) -> In a (CSMap cs')]]
     CRASH:bm'', hm'',
       exists cs', rep cs' d bm''
    >} writeback a cs.
Proof.
  unfold writeback; intros; cleanup.
  destruct (find a (CSMap cs)) eqn:D.
  {
    destruct p.
    destruct b.
    {
      prestep. (* step not smart enough *)
      unfold rep, addr_valid; norml.
      assert (A: In a (CSMap cs)). {        
        apply MapFacts.in_find_iff.
        intuition; congruence.
      }
      specialize (H7 _ A) as Hx.
      destruct (d a) eqn: D0; try congruence; clear Hx.
      unfold stars; simpl. rewrite mem_pred_extract'; eauto.
      unfold mem_pred_one, cachepred at 2; simpl; cleanup.
      destruct v; simpl in *.

      norm.
      unfold stars; simpl; cancel.
      eassign tb0; eassign l; cancel.
      intuition; eauto.

      hoare.
      erewrite <- mem_pred_absorb_nop with (hm:= d)(a:= a); eauto.
      unfold cachepred at 3; simpl; eauto.
      rewrite MapFacts.add_eq_o; eauto; simpl.
      erewrite ptsto_subset_pimpl.
      eassign l.
      simpl; cancel; eauto.
      unfold ptsto_subset; cancel.
      apply mem_pred_pimpl_except; intros.
      unfold cachepred.
      rewrite MapFacts.add_neq_o; eauto.
      unfold vsmerge; simpl.
      eapply incl_cons; eauto.

      unfold size_valid in *; simpl; auto.
      repeat rewrite map_add_dup_cardinal; auto.
      admit.

      destruct (Nat.eq_dec a a0); subst; try congruence.
      rewrite add_neq_o; auto.
      
      unfold addr_clean.
      right; eexists; apply add_eq_o; eauto.
      apply add_in_iff; intuition.

      rewrite <- H1.
      cancel; eauto.
      erewrite <- mem_pred_absorb_nop with (hm:= d)(a:= a); eauto.
      unfold cachepred at 3; simpl; eauto; cleanup.
      cancel; eauto; cancel; eauto.
    }

    unfold addr_clean; hoare.
  }
  unfold addr_clean; hoare.
Admitted.

Hint Extern 1 (corr2 _ _ (Bind (writeback _ _) _)) => apply writeback_ok : prog.

Hint Extern 0 (okToUnify (rep _ _ _) (rep _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (synrep _ _ _ _ _) (synrep _ _ _ _ _)) => constructor : okToUnify.
Hint Extern 0 (okToUnify (mem_pred ?p _) (mem_pred ?p _)) => constructor : okToUnify.


Theorem evict_ok :
  forall a cs pr,
    {< d ,
     PERM: pr
     PRE: bm, hm,
      rep cs d bm
    POST: bm', hm',
      RET:cs'
        rep cs' d bm' * [[ bm' = bm ]] *
        [[ forall a, find a (CSMap cs) = None ->
              find a (CSMap cs') = None ]] *     
        [[ ~ In a (CSMap cs') ]] *
        [[ In a (CSMap cs) -> cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH: bm'', hm'',
       exists cs', rep cs' d bm''
    >} evict a cs.
  Proof.
    unfold evict; step.
    unfold rep in *; destruct (find a (CSMap r_)) eqn:D.
    {
      hoare.
      eapply addr_valid_ptsto_subset in D as Hx;
      eauto; cleanup.      
      eapply addr_clean_cachepred_remove; eauto.
      
      apply size_valid_remove; auto.
      eapply in_find_iff; intuition; congruence.
      apply addr_valid_remove; auto.

      rewrite remove_o.
      destruct (eq_dec a a0); subst; eauto.

      eapply remove_1; eauto.
      eapply size_valid_remove_cardinal_ok; eauto.
    }
    
    {
      hoare.    
      eapply addr_clean_cachepred_remove_none; eauto.
      apply size_valid_remove_notin; auto.
      unfold not; intros.
      eapply in_find_iff in D; congruence.
      apply addr_valid_remove; auto.
      
      
      rewrite remove_o.
      destruct (eq_dec a a0); subst; eauto.
      
      eapply remove_1; eauto.
      eapply size_valid_remove_cardinal_ok; eauto.
    }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (evict _ _) _)) => apply evict_ok : prog.



Theorem maybe_evict_ok :
  forall cs pr,
  {< d,
    PERM: pr                          
    PRE: bm, hm,
      rep cs d bm
    POST: bm', hm', RET:cs'
      rep cs' d bm'* [[ bm' = bm ]] *
      [[ forall a, find a (CSMap cs) = None ->
              find a (CSMap cs') = None ]] *                 
      [[ cardinal (CSMap cs') < CSMaxCount cs' ]]
    CRASH:bm'', hm'',
        exists cs', rep cs' d bm''
    >} maybe_evict cs.
Proof.
  unfold maybe_evict; step. step_r.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  step.
  apply H10; apply in_find_iff; intuition; congruence.
  step_r.
  unfold rep, size_valid in *; destruct_lift H; cleanup; auto.
  rewrite cardinal_1 in *; cleanup; rewrite Heql in *; simpl in *; omega.
  step.
  apply find_elements_hd in Heql;
  apply H10; apply in_find_iff; intuition; congruence.
Qed.

Hint Extern 1 (corr2 _ _ (Bind (maybe_evict _) _)) => apply maybe_evict_ok : prog.


Theorem read_ok :
  forall cs a pr,
  {< d F tbs,
    PERM: pr                 
    PRE: bm, hm,
      rep cs d bm *
      [[ (sep_star (AEQ:= addr_eq_dec) F (a |+> tbs))%pred d ]]
    POST: bm', hm',
      RET:^(cs', r)
        rep cs' d bm' *
        [[ match find a (CSMap cs) with
           | None => bm' = upd bm r (fst tbs) /\ bm r = None
           | Some _ => bm' = bm
           end ]] *
        [[ bm' r = Some (fst tbs) ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm''
  >} read a cs.
Proof.
  unfold read; intros.
  repeat destruct_branch.
  {
    safestep; eauto.
    eapply ptsto_subset_valid' in H6 as Hx; cleanup; simpl in *.
    step_r.
    unfold rep in *; erewrite mem_pred_extract with (a := a) in H1; eauto; 
    unfold cachepred at 2 in H1; rewrite Heqo in H1.
    destruct p_2; destruct_lift H1; eauto.
    cancel; eauto.
  }
  {
    safestep.
    eapply ptsto_subset_valid' in H5 as Hx; cleanup; simpl in *.
    unfold rep; safestep_r.
    specialize (H15 _ Heqo).
    unfold rep in *; erewrite mem_pred_extract with (a := a); eauto; 
    unfold cachepred at 2; rewrite H15.
    eassign tbs_1; eassign x.
    eassign (F_ * [[ size_valid r_ ]] *
             [[ addr_valid d (CSMap r_) ]] *
             mem_pred (HighAEQ:=addr_eq_dec)
                      (cachepred (CSMap r_) bm) (mem_except d a))%pred.
    cancel.
    unfold rep in *; hoare.
    
    rewrite sep_star_comm.
    eapply mem_pred_cachepred_add_absorb_clean; eauto.
    apply size_valid_add; auto.
    eapply addr_valid_add; eauto.       
    apply upd_eq; auto.
    
    rewrite <- H1; unfold rep; cancel; eauto.
    (eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto]);
    unfold cachepred at 3; rewrite H15; eauto;
    cancel; eauto.
  }
Qed.

Hint Extern 1 (corr2 _ _ (Bind (read _ _) _)) => apply read_ok : prog.

Theorem write_ok':
  forall cs a h pr,
    {< d F tb0 tb,
     PERM: pr
     PRE: bm, hm,
            rep cs d bm *
            [[ bm h = Some tb ]] *
            [[ (F * a |+> tb0)%pred d ]]
    POST: bm', hm', RET:cs'
      exists d',
        rep cs' d' bm' * [[ bm' = bm ]] *
        [[ (sep_star (AEQ:= addr_eq_dec) F  (a |+> (tb, vsmerge tb0)))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm'' 
     >} write a h cs.
Proof.
    unfold write; intros.
    safestep; eauto.
    
    eapply ptsto_subset_valid' in H as Hx; cleanup; simpl in *.
    hoare.
    {
      unfold rep; simpl;
      erewrite mem_pred_extract with (a := a) at 1; eauto.
      unfold cachepred at 2; rewrite Heqo; eauto; cancel.
      (rewrite mem_pred_pimpl_except;
       [ | intros; apply cachepred_add_invariant with (v':=(h, true)); eassumption]).
      rewrite <- mem_pred_absorb with (hm := d) (a := a);
      unfold cachepred at 3;
      rewrite MapFacts.add_eq_o by reflexivity.
      destruct p_2.
      cancel.
      eassign tb0.
      eassign (tb, vsmerge (tb0_1, tb0_2)); simpl.
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      simpl; auto.
      simpl; auto.

      cancel.
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      
      eapply size_valid_add_in; eauto.
      eapply addr_valid_upd_add; eauto.        
    }
    eapply ptsto_subset_upd; eauto; apply incl_refl.

    {
      unfold rep; simpl;
      erewrite mem_pred_extract with (a := a) at 1; eauto.
      unfold cachepred at 2; rewrite Heqo; eauto; cancel.
      (rewrite mem_pred_pimpl_except;
       [ | intros; apply cachepred_add_invariant with (v':=(h, true)); eassumption]).
      rewrite <- mem_pred_absorb with (hm := d) (a := a);
      unfold cachepred at 3;
      rewrite MapFacts.add_eq_o by reflexivity.
      cancel.
      eassign (tb, vsmerge(tb0_cur, tb0_old)).
      erewrite ptsto_subset_pimpl; eauto.
      simpl; apply incl_tl; auto.
      simpl; auto.
      simpl; auto.

      eapply size_valid_add; eauto.
      eapply addr_valid_upd_add; eauto.
    }
    eapply ptsto_subset_upd; eauto; apply incl_refl.
    eexists; eapply hashmap_subset_trans; eauto.  
Qed.    

Hint Extern 1 (corr2 _ _ (Bind (write _ _ _) _)) => apply write_ok' : prog.

Theorem begin_sync_ok :
  forall cs pr,
    {< d F,
     PERM: pr   
     PRE:bm, hm,
       rep cs d bm * [[ F d /\ @sync_invariant _ addr_eq_dec _ F ]]
     POST:bm', hm', RET:cs
       exists d',
         synrep cs d d' bm * [[ bm' = bm ]] * [[ F d' ]]
     CRASH:bm'', hm'',
       exists cs', rep cs' d bm''
    >} begin_sync cs.
  Proof.
    unfold begin_sync, synrep.
    step.
    prestep.
    norml; unfold stars; simpl.
    rewrite rep_synrep by eauto.
    cancel; eauto.
  Qed.
  
Theorem end_sync_ok :
  forall cs pr,
   {< d0 d,
    PERM: pr
    PRE:bm, hm,
      synrep cs d0 d bm
    POST:bm', hm', RET:cs
      rep cs d bm' * [[ bm' = bm ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} end_sync cs.
  Proof.
    unfold end_sync; intros.
    hoare.
    unfold rep, synrep, synrep', mem_pred, mem_pred_one; simpl.
    rewrite sync_xform_sep_star_dist, sync_xform_and_dist. rewrite pimpl_r_and.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    norml; unfold stars; simpl.
    repeat (rewrite sync_xform_sep_star_dist || rewrite sync_xform_lift_empty || rewrite sync_xform_exists_comm).
    cancel; auto.
    rewrite sync_xform_listpred_synpred_cachepred; auto.
    rewrite sync_xform_sync_invariant by auto.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto.
    rewrite <- H1; cancel; eauto.
    unfold synrep.
    rewrite pimpl_l_and.
    eassign cs; eauto.
  Qed.

  
  Theorem sync_ok' :
    forall cs a pr,
   {< d0 d (F F' : rawpred tagged_block) v0 v',
    PERM: pr   
    PRE:bm, hm,
      synrep cs d0 d bm * [[ sync_invariant F ]] *
      [[ (F * a |+> v0)%pred d ]] *
      [[ (F' * a |+> v')%pred d0 ]]
    POST:bm', hm', RET:cs
      exists d,
        synrep cs d0 d bm' * [[ bm' = bm ]] *
        [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} sync a cs.
  Proof.
    unfold sync; intros.
    eapply pimpl_ok2; monad_simpl. apply writeback_ok'.
    intros.
    norml; unfold stars; simpl.
    denote (_ d) as Hx; apply ptsto_subset_valid' in Hx as Hy; repeat deex.
    denote (_ d0) as Hz; apply ptsto_subset_valid' in Hz as Hy; repeat deex.
    unfold synrep, rep, synrep'.
    rewrite sep_star_lift_empty.
    rewrite sep_star_lift_empty.
    rewrite lift_empty_and_distr_l; norml; unfold stars; simpl.
    rewrite mem_pred_extract with (a := a) (hm := d) by eauto.
    rewrite mem_pred_extract with (a := a) (hm := d0) by eauto.
    unfold cachepred at 2; unfold synpred at 2; simpl in *.
    destruct (Map.find a (CSMap cs)) eqn:?; try destruct p, b.
    - unfold ptsto_subset at 1 2.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      safecancel; simpl in *; cleanup.
      eassign (x1_cur, l0).
      unfold ptsto_subset;
      cancel; simpl; eauto.
      auto.

      
      hoare.
      repeat cleanup.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply cachepred_add_invariant; eassumption.
        cancel.        
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite MapFacts.add_eq_o by reflexivity.
        unfold ptsto_subset; cancel; eauto.
        rewrite mem_pred_pimpl_except.
        2: intros; apply synpred_add_invariant; eassumption.
        eassign (v, old); simpl.
        cancel.
        simpl; auto.
        simpl; auto.
        eapply size_valid_add_in; eauto.
        eapply addr_valid_add; eauto.
        rewrite upd_eq; auto.
        apply addr_valid_upd; auto.
      + eexists; eapply hashmap_subset_trans; eauto.
      + (* crash *)
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

    - unfold ptsto_subset at 1 2.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      safecancel; simpl in *; cleanup.
      eassign (x0_cur, l0).
      unfold ptsto_subset;
      cancel; simpl; eauto.
      auto.

      hoare.
      cancel.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_comm, sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.
      
      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eassign (x0_cur, old); cancel.
        simpl; auto.
        simpl; auto.
        apply addr_valid_upd; auto.
      + eexists; eapply hashmap_subset_trans; eauto.
      + rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.

    - unfold ptsto_subset at 1 2.
      repeat (rewrite pimpl_exists_l_star_r ||
              rewrite pimpl_exists_r_star_r ||
              rewrite pimpl_and_l_exists ||
              rewrite pimpl_and_r_exists ||
              apply pimpl_exists_l; intros ).
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite sep_star_assoc at 2.
      repeat rewrite sep_star_lift_empty.
      setoid_rewrite <- sep_star_assoc at 1 2.
      rewrite lift_empty_and_distr_r.
      norml; unfold stars; simpl; subst.
      rewrite sep_star_ptsto_and_eq.
      safecancel; simpl in *; cleanup.
      eassign (x0_cur, l0).
      unfold ptsto_subset;
      cancel; simpl; eauto.
      auto.

      hoare.
      2: eapply ptsto_subset_upd with (vs' := nil); eauto; apply incl_refl.
      rewrite sep_star_and_distr; unfold synrep.
      apply pimpl_and_split.
      + rewrite pimpl_l_and; unfold rep; cancel.
        erewrite <- upd_nop with (m := d0) at 2 by eauto.
        rewrite <- mem_pred_absorb with (hm := d0) (a := a).
        unfold cachepred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel.

      + rewrite pimpl_r_and; unfold synrep'; cancel.
        rewrite <- mem_pred_absorb with (hm := d) (a := a).
        unfold synpred at 3.
        rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
        eassign (x0_cur, old); cancel.
        simpl; auto.
        apply addr_valid_upd; auto.
      + eexists; eapply hashmap_subset_trans; eauto.
      +
        rewrite <- H1; safecancel; eauto.
        repeat cleanup.
        rewrite sep_star_and_distr, pimpl_l_and.
        unfold rep; cancel; eauto.
        eapply pimpl_trans; [ | apply mem_pred_absorb_nop; eauto ].
        unfold cachepred at 3; rewrite Heqo.
        unfold ptsto_subset; cancel; eauto.
    Unshelve. all: eauto.
  Qed.



  Theorem sync_ok :
    forall cs pr a,
   {< d0 d (F : rawpred tagged_block) v0,
    PERM: pr                 
    PRE:bm, hm,
      synrep cs d0 d bm *
      [[ (F * a |+> v0)%pred d ]] *
      [[ sync_invariant F ]]
    POST:bm', hm', RET:cs exists d,
      synrep cs d0 d bm' * [[ bm' = bm ]] *
      [[ (F * a |+> (fst v0, nil))%pred d ]]
    CRASH: bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} sync a cs.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply sync_ok'.
    intros; norml; unfold stars; simpl.
    rewrite sync_synrep_helper_2 by eauto.
    safecancel.
    eassign F_; cancel.
    apply H5.
    eauto.
    eauto.
    eauto.
    step.
    rewrite <- H1.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto.
  Qed.



Definition init_load := init.
Definition init_recover := init.
  

Theorem init_load_ok :
  forall cachesize pr,
    {!< disk,
    PERM: pr   
    PRE: bm, hm,
      arrayS 0 disk *
      [[ cachesize <> 0 ]]
    POST:bm',hm', RET:^(cs)
      exists d,
      rep cs d bm' * [[ bm' = bm ]] *
      [[ arrayS 0 disk d ]]
    CRASH:bm'', hm'',
      arrayS 0 disk 
    >!} init_load cachesize.
  Proof.
    unfold init_load, init; step.
    step.
    
    eapply pimpl_ok2; monad_simpl; eauto.
    simpl; intros.

    unfold pimpl; intros.
    destruct_lift H0; subst.

    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm; apply emp_star_r.
    exists m.
    inversion H13; subst.
    repeat (apply sep_star_lift_apply'; eauto).
    apply sep_star_comm.
    apply sep_star_assoc.
    repeat (apply sep_star_lift_apply'; eauto).
    inversion H13; subst.
    apply sync_xform_arrayS in H0.
    eapply mem_pred_cachepred_refl_arrayS; eauto.
    apply size_valid_cache0; eauto.
    apply addr_valid_empty.
    apply sync_xform_arrayS in H0; eauto.
    cleanup.
    eexists; eapply hashmap_subset_trans; eauto.
  Qed.


 

  Theorem init_recover_ok :
    forall cachesize pr,
    {< d F,
    PERM: pr                           
    PRE:bm, hm,
      exists cs, rep cs d bm *
      [[ F d ]] * [[ cachesize <> 0 ]]
    POST:bm', hm', RET:^(cs')
      exists d', rep cs' d' bm' * [[ bm' = bm ]] *
             [[ (@crash_xform _ addr_eq_dec _ F) d' ]]
    CRASH:bm'', hm'',
      exists cs, rep cs d bm''
    >} init_recover cachesize.
  Proof.
    unfold init_recover, init, rep.
    step.
    
    prestep; norml; unfold stars; simpl.
    rewrite sync_xform_sep_star_dist.
    rewrite sync_xform_mem_pred_cachepred; norm.
    cancel.
    intuition eauto.
    step.
    rewrite sync_xform_sync_invariant; auto.
    unfold size_valid in *; intuition.
    unfold addr_valid in *; intuition.
    eapply MapFacts.empty_in_iff; eauto.
    unfold crash_xform; eexists; eauto.
    eexists; eapply hashmap_subset_trans; eauto.
    cancel; eauto.
    rewrite <- H1; cancel; eauto.
  Qed.


  Theorem write_ok :
    forall cs a h pr,
    {< d (F : rawpred tagged_block) v v0,
    PERM: pr   
    PRE:bm, hm,
        rep cs d bm * [[ bm h = Some v ]] *
        [[ (F * a |+> v0)%pred d ]]
    POST:bm', hm', RET:cs
      exists d',
        rep cs d' bm' * [[ bm' = bm ]] *
        [[ (F * a |+> (v, vsmerge v0))%pred d' ]]
    XCRASH:bm'', hm'',
      exists cs' d', rep cs' d' bm'' *
      [[  (F * a |+> (v, vsmerge v0))%pred d' ]]
    >} write a h cs.
  Proof.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel; auto.
    cancel.
    rewrite <- H1.
    eassign ((exists cs' : cachestate, rep cs' d bm'')%pred).
    cancel; eauto.
    rewrite crash_xform_exists_comm.
    cancel.
    
    rewrite crash_xform_rep.
    unfold rep at 1; xform_norm.
    edestruct ptsto_subset_valid' with (a := a); eauto; intuition.
    edestruct possible_crash_sel_exis; eauto; intuition.
    rewrite mem_pred_extract with (a := a) by eauto.

    cancel; xform_normr; cleanup.
    rewrite <- crash_xform_rep_r.
    unfold rep; cancel.
    eapply pimpl_trans2.
    eapply mem_pred_absorb_nop with (a := a).
    2: apply pimpl_refl.
    eauto.
    eauto.
    eauto.
    eapply ptsto_subset_upd; eauto.
    eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    apply incl_tl.
    apply incl_cons2; auto.

    rewrite <- crash_xform_rep_r.
    cancel.
    eapply pimpl_trans2.
    unfold rep; cancel; eauto.
    eapply mem_pred_absorb_nop with (a := a).
    eauto.
    eapply ptsto_subset_upd; eauto.
    eapply possible_crash_ptsto_upd_incl' with (m := d); eauto.
    apply incl_tl.
    apply incl_cons2; auto.
  Qed.

  Hint Extern 1 ({{_ | _}} Bind (init_recover _) _) => apply init_recover_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (init_load _) _) => apply init_load_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (read _ _) _) => apply read_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (sync _ _) _) => apply sync_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (begin_sync _) _) => apply begin_sync_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (end_sync _) _) => apply end_sync_ok : prog.

  
  Theorem read_array_ok :
    forall a i cs pr,
    {< d F vs,
    PERM: pr
    PRE:bm, hm,
        rep cs d bm *
        [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
        [[ i < length vs ]]
    POST:bm', hm',
      RET:^(cs', h)
        rep cs' d bm' *
        [[ match find (a + i) (CSMap cs) with
           | None => bm' = upd bm h (fst (selN vs i valuset0)) /\ bm h = None
           | Some _ => bm' = bm
           end ]] *
        [[ bm' h = Some (fst (selN vs i valuset0)) ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d bm''
    >} read_array a i cs.
  Proof.
    unfold read_array.
    hoare.
    rewrite isolateN_fwd with (i:=i) by auto.
    eassign (F * arrayS a (firstn i vs) *  arrayS (a + i + 1) (skipn (S i) vs))%pred.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto. 
  Qed.



  Theorem write_array_ok :
    forall a i h cs pr,
    {< d F v vs,
    PERM: pr
    PRE: bm, hm,
         rep cs d bm * [[ bm h = Some v ]] *
         [[ (F * arrayN ptsto_subset a vs)%pred d ]] *
         [[ i < length vs ]]
    POST:bm', hm', RET:cs
      exists d', rep cs d' bm' * [[ bm' = bm ]] *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]
    XCRASH:bm'', hm'', exists cs' d',
      rep cs' d' bm'' *
      [[ (F * arrayN ptsto_subset a (vsupd vs i v))%pred d' ]]
    >} write_array a i h cs.
  Proof.
    unfold write_array, vsupd.
    intros.
    eapply pimpl_ok2; monad_simpl.
    apply write_ok'.
    cancel.
    eauto.

    rewrite isolateN_fwd with (i:=i) by auto.
    eassign (arrayS a (firstn i vs) * arrayS (a + i + 1) (skipn (S i) vs) * F)%pred; cancel.
    
    hoare.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
    eexists; eapply hashmap_subset_trans; eauto.

    xcrash.
    rewrite <- H1.
    2:apply write_array_xcrash_ok; eauto.
    cancel; eauto.
  Qed.


  Theorem sync_array_ok :
    forall a i cs pr,
    {< d0 d (F : rawpred tagged_block) vs,
    PERM: pr
    PRE:bm, hm,
      synrep cs d0 d bm *
      [[ (F * arrayN ptsto_subset a vs)%pred d ]] * 
      [[ i < length vs /\ sync_invariant F ]]
    POST:bm', hm', RET:cs exists d',
      synrep cs d0 d' bm' * [[ bm' = bm ]] *
      [[ (F * arrayN ptsto_subset a (vssync vs i))%pred d' ]]
    CRASH:bm'', hm'',
      exists cs', rep cs' d0 bm''
    >} sync_array a i cs.
  Proof.
    unfold sync_array, vssync.
    safestep.
    4: eauto.
    cancel.
    pred_apply;
    rewrite isolateN_fwd with (i:=i) by auto.
    eassign (arrayS a (firstn i vs) * arrayS (a + i + 1) (skipn (S i) vs) * F)%pred; cancel.
    repeat apply sync_invariant_sep_star; eauto; apply sync_invariant_arrayS.
  
    hoare.
    rewrite <- isolateN_bwd_upd by auto.
    cancel.
     eexists; eapply hashmap_subset_trans; eauto.

    xcrash.
    rewrite <- H1.
    cancel; eauto.
  Qed.

  Hint Extern 1 ({{_ | _}} Bind (write _ _ _) _) => apply write_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (read_array _ _ _) _) => apply read_array_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (write_array _ _ _ _) _) => apply write_array_ok : prog.
  Hint Extern 1 ({{_ | _}} Bind (sync_array _ _ _) _) => apply sync_array_ok : prog.
